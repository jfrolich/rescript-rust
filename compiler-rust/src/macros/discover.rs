//! The type checker's side of macro expansion.
//!
//! The type checker knows where macros are used: it is the one that resolves
//! `Json.encode` to a value marked `@generic`, and it has the types a macro
//! asks about. It does not expand anything in place. In a discovery pass it
//! runs the macro and records the result as an [`Edit`] of the source text;
//! [`super::expand`] applies the edits and type checks the new text, until a
//! pass records none.
//!
//! Outside a discovery pass ([`MacroMode::Off`], every ordinary compilation)
//! the first macro use stops type checking with
//! [`TypeCheckContext::macro_expansion_required`] set, which tells the driver
//! to expand the file first.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use serde_json::{Value, json};

use crate::parse_arena::{ExprIdx, LocIdx, ParseArena};
use crate::parser::ast::{
    ArgLabel, Constant, ExpressionDesc, Extension, ModuleBinding, PatternDesc, Payload, RecFlag,
    StructureItem as ParsedStructureItem, StructureItemDesc as ParsedStructureItemDesc,
};
use crate::parser::longident::Longident;
use crate::parser::module::{HOLE_EXTENSION, HOLE_MODULE_NAME, SPLICE_HOLE_EXTENSION};
use crate::types::context::TypeContext;
use crate::types::decl::ValueDescription;
use crate::types::env::Env;
use crate::types::path::{Path, PathView};
use crate::types::predef;
use crate::types::type_expr::{TypeArg, TypeDesc, TypeExprRef};
use crate::types::typecore::{
    BuiltinExtensionError, TypeCheckContext, TypeCoreError, TypeCoreResult,
};
use crate::types::typedtree::{Expression, ExpressionDesc as TypedExpressionDesc};

use super::edit::{Code, Edit, Segment, SourceText, Span, SpanSource};
use super::reflect::{self, TypeTable};
use super::{EVAL_MACRO, MacroHost, is_macro_name, quote};

/// Whether the type checker expands macros.
pub enum MacroMode {
    /// An ordinary compilation: a macro use asks for expansion.
    Off,
    /// A discovery pass of [`super::expand`].
    Discover(Box<Discovery>),
    /// The compilation of a file after its expansion. A macro use is left
    /// only where the code has an error of its own (an unknown name in the
    /// argument of a `@generic`, say): the use is typed as far as its
    /// declared type goes, so that type checking gets to that error and
    /// reports it. `left` is the first such use.
    Expanded { left: Option<LocIdx> },
}

/// Reported if a macro use is left in a file that otherwise type checks.
pub const UNEXPANDED: &str =
    "This macro use was not expanded. This is a bug in the compiler: please report it.";

/// A problem a macro reported, or one with how a macro is used.
#[derive(Debug, Clone)]
pub struct MacroDiagnostic {
    /// Characters of the text being expanded.
    pub start: u32,
    pub end: u32,
    pub message: String,
}

/// A `%Macro.eval(expr)` found by a pass: evaluated between passes, when no
/// type checker is running.
#[derive(Debug, Clone)]
pub struct EvalSite {
    pub start: u32,
    pub end: u32,
    /// The expression's source text.
    pub expression: String,
    /// How to write a value of the expression's type as a literal.
    pub shape: Value,
}

/// A generated function: `Json.encode` at the type `user`.
struct Instance {
    name: String,
    /// Original offset of the first top-level item that calls the instance:
    /// the instance is defined in the group before that item.
    ordinal: u32,
}

/// The instances of a file, kept from pass to pass.
#[derive(Default)]
pub struct InstanceTable {
    by_key: HashMap<String, Instance>,
    names: HashSet<String>,
}

impl InstanceTable {
    fn add(&mut self, key: String, base: &str, ordinal: u32) -> String {
        let mut name = base.to_string();
        let mut counter = 1;
        while self.names.contains(&name) {
            counter += 1;
            name = format!("{base}${counter}");
        }
        self.names.insert(name.clone());
        self.by_key.insert(
            key,
            Instance {
                name: name.clone(),
                ordinal,
            },
        );
        name
    }
}

/// A group of instances that is in the text: a `let rec` an earlier pass
/// added before the top-level item that needed them.
struct Group {
    /// The range of the whole item.
    item: (u32, u32),
    /// Name and range of each function, `name = (...) => body`.
    functions: Vec<(String, u32, u32)>,
}

const GROUP_SEPARATOR: &str = "\nand ";

/// A function of an instance group, `name = (...) => body`.
struct Function {
    /// The call the function was generated for, in the text being edited,
    /// and what the function is. `None` for a function that is in the text
    /// already.
    generated_for: Option<((u32, u32), Arc<str>)>,
    segments: Vec<Segment>,
}

impl Function {
    /// The function at `start..end` of the text.
    fn in_text(start: u32, end: u32) -> Self {
        Function {
            generated_for: None,
            segments: vec![Segment::Copy(start, end)],
        }
    }

    /// The function after `before`: the start of a group, or the separator.
    fn render(self, before: &str, out: &mut Vec<Segment>) {
        if let Some(((start, end), description)) = self.generated_for {
            out.push(Segment::For(start, end, Some(description)));
        }
        out.push(Segment::Text(before.to_string()));
        out.extend(self.segments);
    }
}

fn render_group(functions: Vec<Function>) -> Vec<Segment> {
    let mut segments = Vec::new();
    for (index, function) in functions.into_iter().enumerate() {
        if index == 0 {
            function.render(
                &format!("@{INSTANCES_ATTRIBUTE} @warning(\"-39\") let rec "),
                &mut segments,
            );
        } else {
            function.render(GROUP_SEPARATOR, &mut segments);
        }
    }
    segments
}

/// Why a macro did not return code.
struct Failure {
    message: String,
    by: FailedBy,
}

enum FailedBy {
    /// The macro reported a problem, with `Macro.error`.
    Report,
    /// The macro raised an exception.
    Exception,
    /// The engine could not run the macro.
    Engine,
}

impl Failure {
    fn engine(message: impl Into<String>) -> Self {
        Failure {
            message: message.into(),
            by: FailedBy::Engine,
        }
    }

    /// The message of the diagnostic at the use of the macro `name`.
    fn report(&self, name: &str) -> String {
        match self.by {
            FailedBy::Report => format!(
                "{}\n\nThis is reported by the macro `{name}`.",
                self.message
            ),
            FailedBy::Exception => {
                format!("The macro `{name}` raised an exception:\n{}", self.message)
            }
            FailedBy::Engine => self.message.clone(),
        }
    }
}

/// The code a macro returned: its text, and the parts of it the engine says
/// are an argument or a quote. The engine counts in UTF-16 code units.
fn returned_code(text: &str, spans: Option<&Value>, origins: &[(u32, u32)]) -> Code {
    let mut code = Code::plain(text);
    let Some(spans) = spans.and_then(Value::as_array) else {
        return code;
    };
    // The text is one `char` per byte of its UTF-8 encoding.
    let units: Option<Vec<u32>> = (!text.is_ascii()).then(|| {
        let decoded = crate::source_text::decode_internal_utf8(text);
        let mut offsets = Vec::with_capacity(decoded.len() + 1);
        let mut bytes = 0u32;
        for ch in decoded.chars() {
            for _ in 0..ch.len_utf16() {
                offsets.push(bytes);
            }
            bytes += ch.len_utf8() as u32;
        }
        offsets.push(bytes);
        offsets
    });
    let length = text.chars().count() as u32;
    let offset = |unit: u64| -> Option<u32> {
        match &units {
            Some(units) => units.get(unit as usize).copied(),
            None => (unit <= length as u64).then_some(unit as u32),
        }
    };
    for span in spans {
        let Some(parts) = span.as_array() else {
            continue;
        };
        let (Some(start), Some(len)) = (
            parts.first().and_then(Value::as_u64),
            parts.get(1).and_then(Value::as_u64),
        ) else {
            continue;
        };
        let (Some(from), Some(to)) = (offset(start), offset(start + len)) else {
            continue;
        };
        let source = match &parts[2..] {
            [origin] => match origin.as_u64().and_then(|id| origins.get(id as usize)) {
                Some((at, _)) => SpanSource::Text(*at),
                None => continue,
            },
            [file, line, column] => {
                let (Some(file), Some(line), Some(column)) =
                    (file.as_str(), line.as_u64(), column.as_u64())
                else {
                    continue;
                };
                SpanSource::Quote {
                    file: file.into(),
                    line: line as u32,
                    column: column as u32,
                }
            }
            _ => continue,
        };
        code.spans.push(Span {
            start: from,
            len: to - from,
            from: source,
        });
    }
    code.spans.sort_by_key(|span| span.start);
    code
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ParamKind {
    /// `code<'a>`: the argument's syntax.
    Code,
    /// `typ`: a type.
    Typ,
    /// `Type.decl`: the type declaration the macro is attached to.
    Decl,
    /// `Decl.value`: the `let` the macro is attached to.
    Binding,
    /// A plain type: the argument's value, known at compile time.
    Value,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ResultKind {
    Code,
    Decls,
    Typ,
    Pat,
    Other,
}

struct Signature {
    params: Vec<ParamKind>,
    result: ResultKind,
    /// Per parameter, and for the result: whether the declared type has a
    /// type variable, so that its type differs from use to use.
    open_params: Vec<bool>,
    open_result: bool,
}

/// Whether a type of a macro's declared signature has a type variable.
fn is_open(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    reflect::print_type(ctx, ty).contains('\'')
}

fn macro_type_name(ctx: &TypeContext, ty: TypeExprRef) -> Option<(String, Vec<TypeExprRef>)> {
    match &*ctx.get_desc(ctx.repr(ty)) {
        TypeDesc::Tconstr { path, args, .. } => {
            Some((path.name(), ctx.type_list(*args).iter().collect()))
        }
        _ => None,
    }
}

fn param_kind(ctx: &TypeContext, ty: TypeExprRef) -> ParamKind {
    match macro_type_name(ctx, ty)
        .as_ref()
        .map(|(name, _)| name.as_str())
    {
        Some("Macro.code") | Some("Macro.decls") => ParamKind::Code,
        Some("Macro.typ") => ParamKind::Typ,
        Some("Macro.Type.decl") => ParamKind::Decl,
        Some("Macro.Decl.value") => ParamKind::Binding,
        _ => ParamKind::Value,
    }
}

fn result_kind(ctx: &TypeContext, ty: TypeExprRef) -> ResultKind {
    match macro_type_name(ctx, ty)
        .as_ref()
        .map(|(name, _)| name.as_str())
    {
        Some("Macro.code") => ResultKind::Code,
        Some("Macro.decls") => ResultKind::Decls,
        Some("Macro.typ") => ResultKind::Typ,
        Some("Macro.pat") => ResultKind::Pat,
        _ => ResultKind::Other,
    }
}

fn is_unit(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    matches!(&*ctx.get_desc(ctx.repr(ty)), TypeDesc::Tconstr { path, .. } if path.same(&predef::path_unit()))
}

/// Parameters and result of a macro, read from its type.
fn signature(ctx: &TypeContext, ty: TypeExprRef) -> (Signature, Vec<TypeExprRef>, TypeExprRef) {
    match &*ctx.get_desc(ctx.repr(ty)) {
        TypeDesc::Tarrow { args, ret } => {
            let types: Vec<TypeExprRef> = ctx.type_args(*args).iter().map(|arg| arg.typ).collect();
            // `() => ...` takes no argument.
            let types: Vec<TypeExprRef> = if types.len() == 1 && is_unit(ctx, types[0]) {
                Vec::new()
            } else {
                types
            };
            (
                Signature {
                    params: types.iter().map(|ty| param_kind(ctx, *ty)).collect(),
                    result: result_kind(ctx, *ret),
                    open_params: types.iter().map(|ty| is_open(ctx, *ty)).collect(),
                    open_result: is_open(ctx, *ret),
                },
                types,
                *ret,
            )
        }
        _ => (
            Signature {
                params: Vec::new(),
                result: result_kind(ctx, ty),
                open_params: Vec::new(),
                open_result: is_open(ctx, ty),
            },
            Vec::new(),
            ty,
        ),
    }
}

/// The type a `@generic` has where it is used: `code<'a> => code<JSON.t>`
/// is called as `'a => JSON.t`. `None` when the value is not a function
/// that returns code.
fn erased_type(ctx: &TypeContext, ty: TypeExprRef) -> Option<TypeExprRef> {
    let TypeDesc::Tarrow { args, ret } = &*ctx.get_desc(ctx.repr(ty)) else {
        return None;
    };
    let (name, result_args) = macro_type_name(ctx, *ret)?;
    if name != "Macro.code" {
        return None;
    }
    let erased_args: Vec<TypeArg> = ctx
        .type_args(*args)
        .iter()
        .map(|arg| {
            let erased = match macro_type_name(ctx, arg.typ) {
                Some((name, inner)) if name == "Macro.code" && inner.len() == 1 => inner[0],
                _ => arg.typ,
            };
            TypeArg::with_label(arg.label(), erased)
        })
        .collect();
    Some(ctx.new_type(TypeDesc::Tarrow {
        args: ctx.new_type_args(&erased_args),
        ret: *result_args.first()?,
    }))
}

/// How a value is marked.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MacroKind {
    /// `@macro`: used as `%M.f(...)` or `@M.f`.
    Macro,
    /// `@generic`: called like a function.
    Generic,
}

pub fn macro_kind(desc: &ValueDescription) -> Option<MacroKind> {
    desc.val_attributes
        .iter()
        .find_map(|attr| match attr.attr_name.txt.as_str() {
            "macro" => Some(MacroKind::Macro),
            "generic" => Some(MacroKind::Generic),
            _ => None,
        })
}

/// A generic use found while typing an item, resolved when the item's types
/// are final.
struct PendingGeneric {
    /// The identifier.
    callee: (u32, u32),
    /// The call, when the identifier is applied directly.
    call: Option<PendingCall>,
    module: String,
    name: String,
    signature: Signature,
    /// The erased type at this use.
    ty: TypeExprRef,
    env: Env,
}

struct PendingCall {
    range: (u32, u32),
    /// Per argument: its source range and, for a literal, its value.
    args: Vec<((u32, u32), Option<Value>)>,
}

/// State of one discovery pass.
pub struct Discovery {
    host: Arc<dyn MacroHost>,
    text: Arc<SourceText>,
    /// Directory `readFile` paths are resolved from.
    base_dir: std::path::PathBuf,
    pub edits: Vec<Edit>,
    pub errors: Vec<MacroDiagnostic>,
    /// Per top-level item that failed to type check: where the failure
    /// counts as being, for the order of what is reported.
    pub failed_items: Vec<u32>,
    pub instances: InstanceTable,
    pub evals: Vec<EvalSite>,
    pending: Vec<PendingGeneric>,
    /// Nesting of `type_structure`: 1 while typing a top-level item.
    depth: u32,
    /// The top-level item being typed.
    item_start: u32,
    /// The item stopped because one of its macros was expanded.
    item_pending: bool,
    /// How many problems were reported before the item.
    item_errors: usize,
    /// The application whose function is being typed.
    apply: Option<(LocIdx, PendingCall)>,
    /// The instance groups in the text, by ordinal.
    groups: BTreeMap<u32, Group>,
    /// Instances this pass generated: the ordinal of the item that needs
    /// the instance, the offset of that item, and the function.
    added: Vec<(u32, u32, Function)>,
    /// Instances an earlier item turned out to need as well: name, ordinal
    /// and offset of that item. They move to its group.
    moved: Vec<(String, u32, u32)>,
}

/// What a discovery pass found.
pub struct PassResult {
    pub edits: Vec<Edit>,
    pub errors: Vec<MacroDiagnostic>,
    pub failed_items: Vec<u32>,
    pub instances: InstanceTable,
    pub evals: Vec<EvalSite>,
}

impl Discovery {
    pub fn new(
        host: Arc<dyn MacroHost>,
        text: Arc<SourceText>,
        base_dir: std::path::PathBuf,
        instances: InstanceTable,
    ) -> Self {
        Discovery {
            host,
            text,
            base_dir,
            edits: Vec::new(),
            errors: Vec::new(),
            failed_items: Vec::new(),
            instances,
            evals: Vec::new(),
            pending: Vec::new(),
            depth: 0,
            item_start: 0,
            item_pending: false,
            item_errors: 0,
            apply: None,
            groups: BTreeMap::new(),
            added: Vec::new(),
            moved: Vec::new(),
        }
    }

    pub fn finish(mut self) -> PassResult {
        // Where each instance that moves goes: the earliest item that needs
        // it. What a moved function calls moves with it.
        let mut targets: BTreeMap<String, (u32, u32)> = BTreeMap::new();
        let mut queue: VecDeque<(String, u32, u32)> = std::mem::take(&mut self.moved).into();
        while let Some((name, ordinal, at)) = queue.pop_front() {
            let Some((home, (start, end))) = self.function_in_text(&name) else {
                continue;
            };
            if home <= ordinal
                || targets
                    .get(&name)
                    .is_some_and(|(target, _)| *target <= ordinal)
            {
                continue;
            }
            targets.insert(name, (ordinal, at));
            let function = self.text.slice(start, end);
            for word in
                function.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
            {
                if word.contains('$') && self.instances.names.contains(word) {
                    queue.push_back((word.to_string(), ordinal, at));
                }
            }
        }
        for instance in self.instances.by_key.values_mut() {
            if let Some((ordinal, _)) = targets.get(&instance.name) {
                instance.ordinal = instance.ordinal.min(*ordinal);
            }
        }

        // What each group gains, by ordinal: the offset to start a new group
        // at, and the functions.
        let mut gains: BTreeMap<u32, (u32, Vec<Function>)> = BTreeMap::new();
        for (name, (ordinal, at)) in &targets {
            if let Some((_, (start, end))) = self.function_in_text(name) {
                gains
                    .entry(*ordinal)
                    .or_insert((*at, Vec::new()))
                    .1
                    .push(Function::in_text(start, end));
            }
        }
        let removed: HashSet<&String> = targets.keys().collect();
        for (ordinal, at, function) in std::mem::take(&mut self.added) {
            gains
                .entry(ordinal)
                .or_insert((at, Vec::new()))
                .1
                .push(function);
        }
        for (ordinal, group) in &self.groups {
            let gained = gains
                .remove(ordinal)
                .map(|(_, functions)| functions)
                .unwrap_or_default();
            let loses = group
                .functions
                .iter()
                .any(|(name, _, _)| removed.contains(name));
            if !loses {
                if !gained.is_empty() {
                    let mut segments = Vec::new();
                    for function in gained {
                        function.render(GROUP_SEPARATOR, &mut segments);
                    }
                    self.edits
                        .push(Edit::with(group.item.1, group.item.1, segments));
                }
                continue;
            }
            let mut functions: Vec<Function> = group
                .functions
                .iter()
                .filter(|(name, _, _)| !removed.contains(name))
                .map(|(_, start, end)| Function::in_text(*start, *end))
                .collect();
            functions.extend(gained);
            self.edits.push(Edit::with(
                group.item.0,
                group.item.1,
                render_group(functions),
            ));
        }
        for (_, (at, functions)) in gains {
            let mut segments = render_group(functions);
            segments.push(Segment::Text("\n".into()));
            self.edits.push(Edit::with(at, at, segments));
        }
        PassResult {
            edits: self.edits,
            errors: self.errors,
            failed_items: self.failed_items,
            instances: self.instances,
            evals: self.evals,
        }
    }

    fn error(&mut self, at: (u32, u32), message: impl Into<String>) {
        self.errors.push(MacroDiagnostic {
            start: at.0,
            end: at.1,
            message: message.into(),
        });
    }

    /// The group an instance is defined in, and where its function is.
    fn function_in_text(&self, name: &str) -> Option<(u32, (u32, u32))> {
        self.groups.iter().find_map(|(home, group)| {
            group
                .functions
                .iter()
                .find(|(function, _, _)| function == name)
                .map(|(_, start, end)| (*home, (*start, *end)))
        })
    }

    /// The name of the instance for `key`, if there is one. When it is
    /// defined for an item after the one being typed, it moves here.
    fn instance(&mut self, key: &str) -> Option<String> {
        let ordinal = self.text.origin(self.item_start);
        let instance = self.instances.by_key.get_mut(key)?;
        if instance.ordinal > ordinal {
            instance.ordinal = ordinal;
            self.moved
                .push((instance.name.clone(), ordinal, self.item_start));
        }
        Some(instance.name.clone())
    }

    fn add_instance(&mut self, function: Function) {
        let ordinal = self.text.origin(self.item_start);
        self.added.push((ordinal, self.item_start, function));
    }

    /// Run a macro: ask the engine, answer its questions, ask again.
    fn run(
        &self,
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        table: &mut TypeTable,
        mut request: Value,
    ) -> Result<Code, Failure> {
        let mut answers = serde_json::Map::new();
        for _ in 0..4096 {
            request["answers"] = Value::Object(answers.clone());
            let response =
                super::call_host(&*self.host, &request.to_string()).map_err(|message| {
                    Failure::engine(format!("The macro engine failed: {message}"))
                })?;
            let response: Value = serde_json::from_str(&response).map_err(|error| {
                Failure::engine(format!("The macro engine returned invalid JSON: {error}"))
            })?;
            if let Some(code) = response.get("ok").and_then(Value::as_str) {
                let mut code = returned_code(code, response.get("spans"), table.origins());
                // A quote names its file without directories: find the file.
                let mut paths: HashMap<Arc<str>, Arc<str>> = HashMap::new();
                for span in &mut code.spans {
                    if let SpanSource::Quote { file, .. } = &mut span.from {
                        let path = paths.entry(file.clone()).or_insert_with(|| {
                            let module = crate::driver::module_name_from_source_filename(file);
                            tctx.persistent_env
                                .as_ref()
                                .and_then(|env| env.resolve_module_source_path(&module))
                                .map(|path| Arc::from(path.to_string_lossy().as_ref()))
                                .unwrap_or_else(|| file.clone())
                        });
                        *file = path.clone();
                    }
                }
                return Ok(code);
            }
            if let Some(message) = response.get("error").and_then(Value::as_str) {
                let is = |key: &str| response.get(key).and_then(Value::as_bool) == Some(true);
                return Err(Failure {
                    message: message.to_string(),
                    by: if is("exception") {
                        FailedBy::Exception
                    } else if is("engine") {
                        FailedBy::Engine
                    } else {
                        FailedBy::Report
                    },
                });
            }
            let Some(question) = response.get("need").and_then(Value::as_str) else {
                return Err(Failure::engine(
                    "The macro engine returned an unknown response.",
                ));
            };
            let answer = self.answer(tctx, env, table, question);
            answers.insert(question.to_string(), answer);
        }
        Err(Failure::engine("The macro asked more than 4096 questions."))
    }

    fn answer(
        &self,
        tctx: &mut TypeCheckContext<'_>,
        env: &Env,
        table: &mut TypeTable,
        question: &str,
    ) -> Value {
        let ctx = tctx.type_ctx;
        let failure = |message: String| json!({ "__error": message });
        let (kind, rest) = question.split_once(':').unwrap_or((question, ""));
        match kind {
            "info" => match rest.parse::<usize>().ok().and_then(|id| table.get(id)) {
                Some(ty) => reflect::type_info(ctx, env, table, ty),
                None => failure("Type.info: unknown type.".into()),
            },
            "companion" => {
                let (id, name) = rest.split_once(':').unwrap_or((rest, ""));
                let Some(ty) = id.parse::<usize>().ok().and_then(|id| table.get(id)) else {
                    return failure("Type.companion: unknown type.".into());
                };
                let TypeDesc::Tconstr { path, .. } = &*ctx.get_desc(ctx.repr(ty)) else {
                    return Value::Null;
                };
                let PathView::Pdot(module, _, _) = path.view() else {
                    return Value::Null;
                };
                let value = format!("{}.{}", module.name(), name);
                match lookup_value(tctx, env, &value) {
                    Some(_) => json!({ "c": value }),
                    None => Value::Null,
                }
            }
            _ => answer_input(&self.base_dir, question)
                .unwrap_or_else(|| failure(format!("Unknown question `{question}`."))),
        }
    }
}

/// The answers that need no type checker: files and environment variables.
pub(crate) fn answer_input(base_dir: &std::path::Path, question: &str) -> Option<Value> {
    let (kind, rest) = question.split_once(':')?;
    match kind {
        "readFile" => Some(match read_file(base_dir, rest) {
            Some(text) => Value::String(text),
            None => json!({ "__error": format!("readFile: cannot read `{rest}`.") }),
        }),
        "env" => Some(match std::env::var(rest) {
            Ok(value) => Value::String(crate::source_text::latin1_bytes_to_string(
                value.into_bytes(),
            )),
            Err(_) => Value::Null,
        }),
        _ => None,
    }
}

/// Read `path` relative to `base` or one of its ancestors, as the compiler
/// reads a source file: one `char` per byte.
fn read_file(base: &std::path::Path, path: &str) -> Option<String> {
    #[cfg(feature = "wasm")]
    {
        let _ = base;
        let absolute = if path.starts_with('/') {
            path.to_string()
        } else {
            format!("/{path}")
        };
        return crate::wasm_vfs::read_file(&absolute).or_else(|| crate::wasm_vfs::read_file(path));
    }
    #[cfg(not(feature = "wasm"))]
    {
        let read = |path: &std::path::Path| {
            std::fs::read(path)
                .ok()
                .map(crate::source_text::latin1_bytes_to_string)
        };
        let relative = std::path::Path::new(path);
        if relative.is_absolute() {
            return read(relative);
        }
        let mut dir = Some(base);
        while let Some(current) = dir {
            if let Some(text) = read(&current.join(relative)) {
                return Some(text);
            }
            dir = current.parent();
        }
        read(relative)
    }
}

fn range(arena: &ParseArena, loc: LocIdx) -> (u32, u32) {
    let location = arena.to_location(loc);
    (
        location.loc_start.cnum.max(0) as u32,
        location.loc_end.cnum.max(0) as u32,
    )
}

fn error_at(loc: LocIdx, message: impl Into<String>) -> TypeCoreError {
    TypeCoreError::ExtensionError(BuiltinExtensionError {
        loc,
        message: message.into(),
        sub: Vec::new(),
    })
}

/// Stop an ordinary compilation at a macro use.
fn required(tctx: &mut TypeCheckContext<'_>, loc: LocIdx) -> TypeCoreError {
    if leave(tctx, loc) {
        return error_at(loc, UNEXPANDED);
    }
    tctx.macro_expansion_required = true;
    error_at(loc, "This file uses macros and has to be expanded first.")
}

/// In the compilation of an expanded file: note the macro use at `loc` as
/// left over. Returns whether this is such a compilation.
fn leave(tctx: &mut TypeCheckContext<'_>, loc: LocIdx) -> bool {
    match &mut tctx.macro_mode {
        MacroMode::Expanded { left } => {
            left.get_or_insert(loc);
            true
        }
        _ => false,
    }
}

/// Stop typing the current item of a discovery pass: its edit, or the
/// macro's error, is recorded.
fn pending(tctx: &mut TypeCheckContext<'_>, loc: LocIdx) -> TypeCoreError {
    if let MacroMode::Discover(discovery) = &mut tctx.macro_mode {
        discovery.item_pending = true;
    }
    error_at(loc, "(macro expansion pending)")
}

/// Report a misuse of a macro that only a discovery pass sees: an ordinary
/// compilation stops at the macro before it gets this far.
fn fail(tctx: &mut TypeCheckContext<'_>, loc: LocIdx, message: impl Into<String>) -> TypeCoreError {
    let message = message.into();
    let at = range(tctx.arena, loc);
    match &mut tctx.macro_mode {
        MacroMode::Discover(discovery) => {
            discovery.error(at, message);
            pending(tctx, loc)
        }
        MacroMode::Off | MacroMode::Expanded { .. } => error_at(loc, message),
    }
}

const HOLE_OUTSIDE_QUOTE: &str =
    "A hole `${...}` can only be used inside a quote: %code(...), %type(...) or %pat(...).";

/// `${...}` or `${...items}`: both belong in a quote.
fn is_hole_name(name: &str) -> bool {
    name == HOLE_EXTENSION || name == SPLICE_HOLE_EXTENSION
}

fn discovering(tctx: &TypeCheckContext<'_>) -> bool {
    matches!(tctx.macro_mode, MacroMode::Discover(_))
}

/// Run `f` with the pass state taken out of the context, so `f` can use
/// both.
fn with_discovery<R>(
    tctx: &mut TypeCheckContext<'_>,
    f: impl FnOnce(&mut TypeCheckContext<'_>, &mut Discovery) -> R,
) -> Option<R> {
    let MacroMode::Discover(mut discovery) =
        std::mem::replace(&mut tctx.macro_mode, MacroMode::Off)
    else {
        return None;
    };
    let result = f(tctx, &mut discovery);
    tctx.macro_mode = MacroMode::Discover(discovery);
    Some(result)
}

fn longident_of(arena: &ParseArena, name: &str) -> Option<Longident> {
    let mut longident: Option<Longident> = None;
    for segment in name.split('.') {
        if segment.is_empty() {
            return None;
        }
        let idx = arena
            .find_string_idx(segment)
            .unwrap_or_else(|| arena.push_typecheck_string(segment.to_string()));
        longident = Some(match longident {
            None => Longident::Lident(idx),
            Some(prefix) => Longident::Ldot(Box::new(prefix), idx),
        });
    }
    longident
}

fn lookup_value(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    name: &str,
) -> Option<(Path, Arc<ValueDescription>)> {
    let longident = longident_of(tctx.arena, name)?;
    env.lookup_value_by_lid(
        &longident,
        tctx.arena,
        &mut tctx.persistent_env,
        tctx.type_ctx,
    )
}

/// `Json.encode` → (`Json`, `encode`): the file whose JavaScript the engine
/// loads, and the path of the macro in its exports (`Inner.encode` for a
/// macro in a submodule).
fn split_macro_name(name: &str) -> (String, String) {
    match name.split_once('.') {
        Some((module, path)) => (module.to_string(), path.to_string()),
        None => (String::new(), name.to_string()),
    }
}

fn literal(arena: &ParseArena, expr: ExprIdx) -> Option<Value> {
    let expr = arena.get_expr(expr);
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match constant {
            Constant::String(text) => Some(Value::String(text.semantic(arena).to_string())),
            Constant::Integer(text, None) => arena
                .get_string(*text)
                .replace('_', "")
                .parse::<i64>()
                .ok()
                .map(Value::from),
            Constant::Float(text, None) => arena
                .get_string(*text)
                .replace('_', "")
                .parse::<f64>()
                .ok()
                .map(Value::from),
            _ => None,
        },
        ExpressionDesc::Pexp_construct(lid, args) if arena.expr_list(args.txt).is_empty() => {
            match arena.get_longident(lid.txt) {
                Longident::Lident(name) => match arena.get_string(*name) {
                    "true" => Some(Value::Bool(true)),
                    "false" => Some(Value::Bool(false)),
                    "()" => Some(Value::Null),
                    _ => None,
                },
                _ => None,
            }
        }
        // An array and a tuple are both an array at run time.
        ExpressionDesc::Pexp_array(items) | ExpressionDesc::Pexp_tuple(items) => arena
            .expr_list(*items)
            .iter()
            .map(|item| literal(arena, *item))
            .collect::<Option<Vec<Value>>>()
            .map(Value::Array),
        ExpressionDesc::Pexp_record((fields, None)) => {
            let mut object = serde_json::Map::new();
            for field in arena.expr_field_list(*fields) {
                let Longident::Lident(name) = arena.get_longident(field.lid.txt) else {
                    return None;
                };
                if field.opt {
                    return None;
                }
                object.insert(
                    arena.get_string(*name).to_string(),
                    literal(arena, field.expr)?,
                );
            }
            Some(Value::Object(object))
        }
        _ => None,
    }
}

/// The argument expressions of `%M.f(a, b)`.
fn payload_expressions(
    arena: &ParseArena,
    payload: &Payload,
    arity: usize,
) -> Result<Vec<ExprIdx>, String> {
    let Payload::PStr(items) = payload else {
        return Err("The arguments of a macro are expressions here.".into());
    };
    match items.as_slice() {
        [] => Ok(Vec::new()),
        [item] => {
            let ParsedStructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
                return Err("The arguments of a macro are expressions here.".into());
            };
            match &arena.get_expr(eval.0).pexp_desc {
                ExpressionDesc::Pexp_tuple(elements) if arity != 1 => {
                    Ok(arena.expr_list(*elements).to_vec())
                }
                _ => Ok(vec![eval.0]),
            }
        }
        _ => Err("The arguments of a macro are expressions here.".into()),
    }
}

/// The JSON arguments of a `%M.f(...)` call.
fn call_arguments(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    discovery: &Discovery,
    table: &mut TypeTable,
    name: &str,
    signature: &Signature,
    payload: &Payload,
) -> Result<Vec<Value>, String> {
    let exprs = payload_expressions(tctx.arena, payload, signature.params.len())?;
    if exprs.len() != signature.params.len() {
        return Err(format!(
            "The macro `{name}` takes {} argument{}, and {} {} given.",
            signature.params.len(),
            if signature.params.len() == 1 { "" } else { "s" },
            exprs.len(),
            if exprs.len() == 1 { "is" } else { "are" },
        ));
    }
    let mut args = Vec::with_capacity(exprs.len());
    for (index, (expr_idx, kind)) in exprs.iter().zip(&signature.params).enumerate() {
        let expr = tctx.arena.get_expr(*expr_idx);
        let at = range(tctx.arena, expr.pexp_loc);
        match kind {
            ParamKind::Code => {
                let mut code =
                    json!({ "c": discovery.text.slice(at.0, at.1), "$o": table.origin(at) });
                // The type as far as it is known here. An argument that
                // does not type check on its own has none.
                let ctx = tctx.type_ctx;
                let expected = ctx.new_var(None);
                if let Ok(typed) =
                    crate::types::typecore::type_expect(tctx, env, expr, expected, None)
                {
                    code["t"] = reflect::type_ref(ctx, table, typed.exp_type);
                }
                args.push(code);
            }
            ParamKind::Value => match literal(tctx.arena, *expr_idx) {
                Some(value) => args.push(value),
                None => {
                    return Err(format!(
                        "Argument {} of the macro `{name}` is a compile-time value, so it has to be a literal: a number, a string, a boolean, or an array, tuple or record of them.",
                        index + 1
                    ));
                }
            },
            ParamKind::Typ => {
                return Err(format!(
                    "Argument {} of the macro `{name}` is a type. Use the macro where a type is written: `type t = %{name}(...)`.",
                    index + 1
                ));
            }
            ParamKind::Decl | ParamKind::Binding => {
                return Err(format!(
                    "The macro `{name}` works on a declaration. Attach it: `@{name}`."
                ));
            }
        }
    }
    Ok(args)
}

/// Look up the macro an extension or attribute names.
fn find_macro(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    name: &str,
) -> Result<Arc<ValueDescription>, TypeCoreError> {
    // Only `expression_extension` evaluates it.
    if name == EVAL_MACRO {
        return Err(error_at(
            loc,
            format!(
                "`%{EVAL_MACRO}(expr)` is the value of an expression: it is written where an expression is."
            ),
        ));
    }
    let Some((_, desc)) = lookup_value(tctx, env, name) else {
        let own_module = tctx
            .persistent_env
            .as_ref()
            .and_then(|persistent_env| persistent_env.compiling_module_name())
            .is_some_and(|module| name.split('.').next() == Some(module));
        return Err(error_at(
            loc,
            if own_module {
                format!(
                    "`{name}` is defined in this file. A macro cannot be used in the file that defines it: the compiler runs the compiled file."
                )
            } else {
                format!("The macro `{name}` cannot be found.")
            },
        ));
    };
    match macro_kind(&desc) {
        Some(_) => Ok(desc),
        None => Err(error_at(
            loc,
            format!("`{name}` is not a macro. A macro is a function marked with @macro."),
        )),
    }
}

/// Run a macro for a call site and return its code, or record the failure.
#[allow(clippy::too_many_arguments)]
fn run_call(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    discovery: &mut Discovery,
    table: &mut TypeTable,
    at: (u32, u32),
    name: &str,
    args: Result<Vec<Value>, String>,
    expected: Option<Value>,
) -> Option<Code> {
    let args = match args {
        Ok(args) => args,
        Err(message) => {
            discovery.error(at, message);
            return None;
        }
    };
    let (module, value) = split_macro_name(name);
    let request = json!({
        "kind": "call",
        "module": module,
        "name": value,
        "args": args,
        "expected": expected,
    });
    match discovery.run(tctx, env, table, request) {
        Ok(code) => Some(code),
        Err(failure) => {
            discovery.error(at, failure.report(name));
            None
        }
    }
}

/// `(code)`: generated code where an expression, a pattern or a type is
/// expected.
fn parenthesized(code: Code) -> Vec<Segment> {
    vec![
        Segment::Text("(".into()),
        Segment::Code(code),
        Segment::Text(")".into()),
    ]
}

/// `%name(...)` where an expression is expected. `None`: not a macro, the
/// type checker handles the extension as before.
pub(crate) fn expression_extension(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    extension: &Extension,
    expected_ty: TypeExprRef,
) -> Option<TypeCoreResult<Expression>> {
    let name = tctx.arena.get_string(extension.0.txt).to_string();
    let is_hole = is_hole_name(&name);
    if is_hole || quote::is_quote_name(&name) {
        // Quotes are lowered before a discovery pass; one that is left has
        // no payload.
        return Some(Err(if matches!(tctx.macro_mode, MacroMode::Off) {
            required(tctx, loc)
        } else if is_hole {
            fail(tctx, loc, HOLE_OUTSIDE_QUOTE)
        } else {
            fail(
                tctx,
                loc,
                format!("The quote `%{name}` needs a payload: `%{name}(...)`."),
            )
        }));
    }
    if name == EVAL_MACRO {
        return Some(eval(tctx, env, loc, extension, expected_ty));
    }
    if !is_macro_name(&name) {
        return None;
    }
    let desc = match find_macro(tctx, env, loc, &name) {
        Ok(desc) => desc,
        Err(error) => return Some(Err(error)),
    };
    // After expansion a use that is left is typed as its declared result.
    if !discovering(tctx) && !leave(tctx, loc) {
        return Some(Err(required(tctx, loc)));
    }
    let ctx = tctx.type_ctx;
    let macro_type = crate::types::instance(ctx, desc.val_type);
    let (signature, _, result_type) = signature(ctx, macro_type);
    let at = range(tctx.arena, loc);
    if signature.result != ResultKind::Code {
        return Some(Err(fail(
            tctx,
            loc,
            format!(
                "The macro `{name}` does not return an expression, so it cannot be used as one."
            ),
        )));
    }
    let mut table = TypeTable::default();
    with_discovery(tctx, |tctx, discovery| {
        let args = call_arguments(
            tctx,
            env,
            discovery,
            &mut table,
            &name,
            &signature,
            &extension.1,
        );
        if let Some(code) = run_call(tctx, env, discovery, &mut table, at, &name, args, None) {
            discovery
                .edits
                .push(Edit::with(at.0, at.1, parenthesized(code)));
        }
    });
    // Type the call as its declared result, `code<string>` as `string`, so
    // the rest of the item is checked as far as possible in this pass.
    if let Some((_, inner)) = macro_type_name(ctx, result_type)
        && let Some(inner) = inner.first()
    {
        let mut state = crate::types::ctype::UnifyState::default();
        let _ = crate::types::ctype::unify(ctx, &mut state, *inner, expected_ty);
    }
    Some(Ok(Expression::new(
        TypedExpressionDesc::Texp_break,
        loc,
        expected_ty,
        ctx.store_typed_env(env),
    )))
}

/// `%Macro.eval(expr)`: `expr` is typed as usual; its value replaces it
/// between passes.
fn eval(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    extension: &Extension,
    expected_ty: TypeExprRef,
) -> TypeCoreResult<Expression> {
    if !discovering(tctx) && !leave(tctx, loc) {
        return Err(required(tctx, loc));
    }
    let expr_idx = match payload_expressions(tctx.arena, &extension.1, 1) {
        Ok(exprs) if exprs.len() == 1 => exprs[0],
        _ => {
            return Err(fail(
                tctx,
                loc,
                format!("%{EVAL_MACRO} takes one expression: `%{EVAL_MACRO}(expr)`."),
            ));
        }
    };
    let expr = tctx.arena.get_expr(expr_idx);
    let typed = crate::types::typecore::type_expect(tctx, env, expr, expected_ty, None)?;
    let at = range(tctx.arena, loc);
    let inner = range(tctx.arena, expr.pexp_loc);
    let ctx = tctx.type_ctx;
    let shape = reflect::value_shape(ctx, env, typed.exp_type, 0);
    with_discovery(tctx, |_, discovery| {
        let expression = discovery.text.slice(inner.0, inner.1).to_string();
        discovery.evals.push(EvalSite {
            start: at.0,
            end: at.1,
            expression,
            shape,
        });
    });
    Ok(typed)
}

/// An application is about to be typed: remember its arguments for the case
/// that its function is a `@generic`.
pub(crate) fn note_application(
    tctx: &mut TypeCheckContext<'_>,
    loc: LocIdx,
    funct: &crate::parser::ast::Expression,
    args: &[(ArgLabel, ExprIdx)],
) {
    let arena = tctx.arena;
    let MacroMode::Discover(discovery) = &mut tctx.macro_mode else {
        return;
    };
    if !matches!(funct.pexp_desc, ExpressionDesc::Pexp_ident(_)) {
        return;
    }
    let call = PendingCall {
        range: range(arena, loc),
        args: args
            .iter()
            .map(|(label, arg)| {
                let value = match label {
                    ArgLabel::Nolabel => literal(arena, *arg),
                    _ => None,
                };
                (range(arena, arena.get_expr(*arg).pexp_loc), value)
            })
            .collect(),
    };
    discovery.apply = Some((funct.pexp_loc, call));
}

/// An identifier resolved to `desc`. For a `@generic` of another file this
/// returns the type the identifier has here; otherwise `None`.
pub(crate) fn generic_use(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    path: &Path,
    desc: &ValueDescription,
) -> TypeCoreResult<Option<TypeExprRef>> {
    let Some(kind) = macro_kind(desc) else {
        return Ok(None);
    };
    // In its own file a macro is an ordinary function.
    let PathView::Pdot(..) = path.view() else {
        return Ok(None);
    };
    let name = path.name();
    if kind == MacroKind::Macro {
        return Err(error_at(
            loc,
            format!("`{name}` is a macro. Use it as `%{name}(...)` or attach it as `@{name}`."),
        ));
    }
    if !discovering(tctx) && !leave(tctx, loc) {
        return Err(required(tctx, loc));
    }
    let ctx = tctx.type_ctx;
    let instance = crate::types::instance(ctx, desc.val_type);
    let Some(erased) = erased_type(ctx, instance) else {
        return Err(error_at(
            loc,
            format!(
                "`{name}` is marked @generic, so it has to be a function that returns `code<...>`."
            ),
        ));
    };
    let (signature, _, _) = signature(ctx, instance);
    let callee = range(tctx.arena, loc);
    let (module, value) = split_macro_name(&name);
    let env = env.clone();
    if let MacroMode::Discover(discovery) = &mut tctx.macro_mode {
        let call = match discovery.apply.take() {
            Some((apply_loc, call)) if apply_loc == loc => Some(call),
            _ => None,
        };
        discovery.pending.push(PendingGeneric {
            callee,
            call,
            module,
            name: value,
            signature,
            ty: erased,
            env,
        });
    }
    Ok(Some(erased))
}

fn instance_name(base: &str, parts: &[String]) -> String {
    let mut name = String::from(base);
    for part in parts {
        name.push('$');
        let mut last_underscore = true;
        for ch in part.chars() {
            if ch.is_ascii_alphanumeric() {
                name.push(ch);
                last_underscore = false;
            } else if !last_underscore {
                name.push('_');
                last_underscore = true;
            }
        }
        while name.ends_with('_') {
            name.pop();
        }
    }
    name
}

/// A top-level item is about to be typed.
pub(crate) fn begin_item(tctx: &mut TypeCheckContext<'_>, item: &ParsedStructureItem) {
    let arena = tctx.arena;
    let MacroMode::Discover(discovery) = &mut tctx.macro_mode else {
        return;
    };
    discovery.depth += 1;
    if discovery.depth != 1 {
        return;
    }
    let (start, end) = range(arena, item.pstr_loc);
    discovery.item_start = start;
    discovery.item_pending = false;
    discovery.item_errors = discovery.errors.len();
    // An instance group that an earlier pass added.
    if is_instance_group(arena, item)
        && let ParsedStructureItemDesc::Pstr_value((_, bindings)) = &item.pstr_desc
    {
        let bindings = arena.vb_list(*bindings);
        let starts: Vec<u32> = bindings
            .iter()
            .map(|binding| range(arena, arena.get_pat(binding.pvb_pat).ppat_loc).0)
            .collect();
        let functions = bindings
            .iter()
            .enumerate()
            .filter_map(|(index, binding)| {
                let PatternDesc::Ppat_var(name) = &arena.get_pat(binding.pvb_pat).ppat_desc else {
                    return None;
                };
                // A function ends where the separator before the next starts.
                let function_end = match starts.get(index + 1) {
                    Some(next) => next.saturating_sub(GROUP_SEPARATOR.len() as u32),
                    None => end,
                };
                Some((
                    arena.get_string(name.txt).to_string(),
                    starts[index],
                    function_end,
                ))
            })
            .collect();
        let ordinal = discovery.text.origin(start);
        discovery.groups.insert(
            ordinal,
            Group {
                item: (start, end),
                functions,
            },
        );
    }
}

/// The attribute on a group of generated instances.
pub const INSTANCES_ATTRIBUTE: &str = "res.macroInstances";

/// Whether a structure item is a group of generated instances. The group is
/// not part of the module's signature and is not exported.
pub(crate) fn is_instance_group(arena: &ParseArena, item: &ParsedStructureItem) -> bool {
    if let ParsedStructureItemDesc::Pstr_value((RecFlag::Recursive, bindings)) = &item.pstr_desc
        && let Some(first) = arena.vb_list(*bindings).first()
    {
        return first
            .pvb_attributes
            .iter()
            .any(|attr| arena.get_string(attr.0.txt) == INSTANCES_ATTRIBUTE);
    }
    false
}

/// A top-level item was typed (`ok`) or failed. Resolves the generic uses
/// found in it. Returns whether the failure is only a recorded expansion.
pub(crate) fn end_item(tctx: &mut TypeCheckContext<'_>, ok: bool) {
    let MacroMode::Discover(discovery) = &mut tctx.macro_mode else {
        return;
    };
    discovery.depth -= 1;
    if discovery.depth != 0 {
        return;
    }
    discovery.apply = None;
    let pending = std::mem::take(&mut discovery.pending);
    if !ok && !discovery.item_pending {
        // The item has a type error. It comes after the problems its macros
        // reported while it was typed, and before the rest of the file.
        let start = discovery.item_start;
        let at = discovery.errors[discovery.item_errors..]
            .iter()
            .map(|error| error.end)
            .max()
            .unwrap_or(start);
        discovery.failed_items.push(at);
        // Its types are not final: no generic is generated from them.
        return;
    }
    with_discovery(tctx, |tctx, discovery| {
        for generic in pending {
            resolve_generic(tctx, discovery, generic);
        }
    });
}

fn resolve_generic(
    tctx: &mut TypeCheckContext<'_>,
    discovery: &mut Discovery,
    generic: PendingGeneric,
) {
    let ctx = tctx.type_ctx;
    let full_name = format!("{}.{}", generic.module, generic.name);
    let TypeDesc::Tarrow { args, ret } = &*ctx.get_desc(ctx.repr(generic.ty)) else {
        return;
    };
    let ret = *ret;
    let arg_types: Vec<TypeExprRef> = ctx.type_args(*args).iter().map(|arg| arg.typ).collect();

    let mut table = TypeTable::default();
    let mut macro_args = Vec::new();
    let mut params = Vec::new();
    let mut call_args = Vec::new();
    let mut key_parts = Vec::new();
    let mut name_parts = Vec::new();
    for (index, kind) in generic.signature.params.iter().enumerate() {
        match kind {
            ParamKind::Code => {
                let Some(ty) = arg_types.get(index).copied() else {
                    return;
                };
                let printed = reflect::print_type(ctx, ty);
                if reflect::is_unknown(ctx, ty) || printed.contains("'_") {
                    discovery.error(
                        generic.callee,
                        format!(
                            "`{full_name}` is generated per type, and the type of this argument is not known here. Add a type annotation."
                        ),
                    );
                    return;
                }
                let param = format!("{}$", (b'a' + (params.len() % 26) as u8) as char);
                let mut code = json!({ "c": param });
                code["t"] = reflect::type_ref(ctx, &mut table, ty);
                macro_args.push(code);
                params.push((param, printed.clone()));
                key_parts.push(printed.clone());
                // The name says what differs from instance to instance.
                if generic.signature.open_params.get(index) == Some(&true) {
                    name_parts.push(printed);
                }
                if let Some(call) = &generic.call
                    && let Some((at, _)) = call.args.get(index)
                {
                    call_args.push(discovery.text.slice(at.0, at.1).to_string());
                }
            }
            ParamKind::Value => {
                let value = generic
                    .call
                    .as_ref()
                    .and_then(|call| call.args.get(index))
                    .and_then(|(_, value)| value.clone());
                let Some(value) = value else {
                    discovery.error(
                        generic.callee,
                        format!(
                            "Argument {} of `{full_name}` is a compile-time value: call `{full_name}` directly, with a literal.",
                            index + 1
                        ),
                    );
                    return;
                };
                key_parts.push(value.to_string());
                name_parts.push(match &value {
                    Value::String(text) => text.clone(),
                    other => other.to_string(),
                });
                macro_args.push(value);
            }
            _ => {
                discovery.error(
                    generic.callee,
                    format!(
                        "`{full_name}`: a @generic takes `code<...>` and compile-time values only."
                    ),
                );
                return;
            }
        }
    }
    let has_values = generic.signature.params.contains(&ParamKind::Value);
    let result = reflect::print_type(ctx, ret);
    // What an instance is of, for a diagnostic in its code.
    let described: Vec<String> = if name_parts.is_empty() {
        vec![result.clone()]
    } else {
        name_parts.clone()
    };
    let key = format!("{full_name}({})->{result}", key_parts.join(","));
    let ordinal = discovery.text.origin(discovery.item_start);

    let name = match discovery.instance(&key) {
        Some(name) => name,
        None => {
            let expected = reflect::type_ref(ctx, &mut table, ret);
            let request = json!({
                "kind": "call",
                "module": generic.module,
                "name": generic.name,
                "args": macro_args,
                "expected": expected,
            });
            let body = match discovery.run(tctx, &generic.env, &mut table, request) {
                Ok(body) => body,
                Err(failure) => {
                    discovery.error(generic.callee, failure.report(&full_name));
                    return;
                }
            };
            if generic.signature.open_result || name_parts.is_empty() {
                name_parts.push(result.clone());
            }
            let name =
                discovery
                    .instances
                    .add(key, &instance_name(&generic.name, &name_parts), ordinal);
            let annotation = if result.contains("'_") || reflect::is_unknown(ctx, ret) {
                String::new()
            } else {
                format!(": {result}")
            };
            let params = params
                .iter()
                .map(|(param, ty)| {
                    // A parameter the macro's code does not mention.
                    let used = body
                        .text
                        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$'))
                        .any(|word| word == param);
                    format!("{}: {ty}", if used { param } else { "_" })
                })
                .collect::<Vec<_>>()
                .join(", ");
            let description = format!("`{full_name}` for `{}`", described.join(", "));
            discovery.add_instance(Function {
                generated_for: Some((generic.callee, description.into())),
                segments: vec![
                    Segment::Text(format!("{name} = ({params}){annotation} => ")),
                    Segment::Code(body),
                ],
            });
            name
        }
    };

    if has_values {
        // The compile-time arguments are part of the instance: the call
        // keeps the others.
        match &generic.call {
            Some(call) => discovery.edits.push(Edit::replace(
                call.range.0,
                call.range.1,
                format!("{name}({})", call_args.join(", ")),
            )),
            None => discovery.error(
                generic.callee,
                format!(
                    "`{full_name}` takes compile-time values, so it has to be called directly."
                ),
            ),
        }
    } else {
        discovery
            .edits
            .push(Edit::replace(generic.callee.0, generic.callee.1, name));
    }
}

/// Whether a failed top-level item is skipped: in a discovery pass, at the
/// top level of the file.
pub(crate) fn skips_failed_item(tctx: &TypeCheckContext<'_>) -> bool {
    matches!(&tctx.macro_mode, MacroMode::Discover(discovery) if discovery.depth == 0)
}

/// An extension where a pattern is expected: `| %Http.status("ok") => ...`.
pub(crate) fn pattern_extension(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    extension: &Extension,
) -> Option<TypeCoreError> {
    let name = tctx.arena.get_string(extension.0.txt).to_string();
    if is_hole_name(&name) {
        return Some(if matches!(tctx.macro_mode, MacroMode::Off) {
            required(tctx, loc)
        } else {
            fail(tctx, loc, HOLE_OUTSIDE_QUOTE)
        });
    }
    if !is_macro_name(&name) {
        return None;
    }
    let desc = match find_macro(tctx, env, loc, &name) {
        Ok(desc) => desc,
        Err(error) => return Some(error),
    };
    if !discovering(tctx) {
        return Some(required(tctx, loc));
    }
    let ctx = tctx.type_ctx;
    let (signature, _, _) = signature(ctx, crate::types::instance(ctx, desc.val_type));
    if signature.result != ResultKind::Pat {
        return Some(fail(
            tctx,
            loc,
            format!(
                "The macro `{name}` does not return a pattern (`pat`), so it cannot be used as one."
            ),
        ));
    }
    let at = range(tctx.arena, loc);
    let mut table = TypeTable::default();
    with_discovery(tctx, |tctx, discovery| {
        let args = call_arguments(
            tctx,
            env,
            discovery,
            &mut table,
            &name,
            &signature,
            &extension.1,
        );
        if let Some(code) = run_call(tctx, env, discovery, &mut table, at, &name, args, None) {
            discovery
                .edits
                .push(Edit::with(at.0, at.1, parenthesized(code)));
        }
    });
    Some(pending(tctx, loc))
}

/// An extension where a type is expected: `type t = %Partial.t(user)`.
pub(crate) fn type_extension(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    extension: &Extension,
) -> Option<TypeCoreError> {
    let name = tctx.arena.get_string(extension.0.txt).to_string();
    if is_hole_name(&name) {
        return Some(if matches!(tctx.macro_mode, MacroMode::Off) {
            required(tctx, loc)
        } else {
            fail(tctx, loc, HOLE_OUTSIDE_QUOTE)
        });
    }
    if !is_macro_name(&name) {
        return None;
    }
    let desc = match find_macro(tctx, env, loc, &name) {
        Ok(desc) => desc,
        Err(error) => return Some(error),
    };
    if !discovering(tctx) {
        return Some(required(tctx, loc));
    }
    let ctx = tctx.type_ctx;
    let (signature, _, _) = signature(ctx, crate::types::instance(ctx, desc.val_type));
    if signature.result != ResultKind::Typ {
        return Some(fail(
            tctx,
            loc,
            format!("The macro `{name}` does not return a type, so it cannot be used as one."),
        ));
    }
    let arena = tctx.arena;
    let types: Vec<crate::parse_arena::CoreTypeIdx> = match &extension.1 {
        Payload::PTyp(idx) => match &arena.get_core_type(*idx).ptyp_desc {
            crate::parser::ast::CoreTypeDesc::Ptyp_tuple(elements)
                if signature.params.len() != 1 =>
            {
                arena.type_list(*elements).to_vec()
            }
            _ => vec![*idx],
        },
        _ => Vec::new(),
    };
    let at = range(arena, loc);
    let mut table = TypeTable::default();
    let mut args: Result<Vec<Value>, String> = if types.len() == signature.params.len() {
        Ok(Vec::new())
    } else {
        Err(format!(
            "The macro `{name}` takes {} argument(s), and {} are given.",
            signature.params.len(),
            types.len()
        ))
    };
    if let Ok(values) = &mut args {
        for (idx, kind) in types.iter().zip(&signature.params) {
            let styp = arena.get_core_type(*idx);
            let type_range = range(arena, styp.ptyp_loc);
            if *kind != ParamKind::Typ {
                args = Err(format!(
                    "The macro `{name}` takes arguments that are not types."
                ));
                break;
            }
            match crate::types::typecore::transl_type(tctx, env, styp) {
                Ok((_, ty)) => {
                    let mut value = reflect::type_ref(ctx, &mut table, ty);
                    value["$o"] = json!(table.origin(type_range));
                    with_discovery(tctx, |_, discovery| {
                        value["c"] = Value::String(
                            discovery.text.slice(type_range.0, type_range.1).to_string(),
                        );
                    });
                    values.push(value);
                }
                Err(error) => return Some(error),
            }
        }
    }
    with_discovery(tctx, |tctx, discovery| {
        if let Some(code) = run_call(tctx, env, discovery, &mut table, at, &name, args, None) {
            // A record or variant body is the right-hand side of a type
            // declaration, which takes no parentheses.
            let segments = if code.text.trim_start().starts_with(['{', '|']) {
                vec![Segment::Code(code)]
            } else {
                parenthesized(code)
            };
            discovery.edits.push(Edit::with(at.0, at.1, segments));
        }
    });
    Some(pending(tctx, loc))
}

/// A structure item or module expression that is a macro call:
/// `%M.f(...)` on its own, or `module X = %M.f(...)`.
pub(crate) fn declarations_extension(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    loc: LocIdx,
    extension: &Extension,
    as_module: bool,
) -> Option<TypeCoreError> {
    let name = tctx.arena.get_string(extension.0.txt).to_string();
    if !is_macro_name(&name) {
        return None;
    }
    let desc = match find_macro(tctx, env, loc, &name) {
        Ok(desc) => desc,
        Err(error) => return Some(error),
    };
    if !discovering(tctx) {
        return Some(required(tctx, loc));
    }
    let ctx = tctx.type_ctx;
    let (signature, _, _) = signature(ctx, crate::types::instance(ctx, desc.val_type));
    if signature.result != ResultKind::Decls {
        return Some(fail(
            tctx,
            loc,
            format!(
                "The macro `{name}` does not return declarations (`decls`), so it cannot be used here."
            ),
        ));
    }
    let at = range(tctx.arena, loc);
    let mut table = TypeTable::default();
    with_discovery(tctx, |tctx, discovery| {
        let args = call_arguments(
            tctx,
            env,
            discovery,
            &mut table,
            &name,
            &signature,
            &extension.1,
        );
        if let Some(code) = run_call(tctx, env, discovery, &mut table, at, &name, args, None) {
            let segments = if as_module {
                vec![
                    Segment::Text("{\n".into()),
                    Segment::Code(code),
                    Segment::Text("\n}".into()),
                ]
            } else {
                vec![Segment::Code(code)]
            };
            discovery.edits.push(Edit::with(at.0, at.1, segments));
        }
    });
    Some(pending(tctx, loc))
}

/// The macros attached to something: `@Json.codec`.
fn macro_attributes(
    arena: &ParseArena,
    attributes: &crate::parser::ast::Attributes,
) -> Vec<(String, LocIdx)> {
    attributes
        .iter()
        .filter_map(|attr| {
            let name = arena.get_string(attr.0.txt);
            is_macro_name(name).then(|| (name.to_string(), attr.0.loc))
        })
        .collect()
}

/// Whether a `let` or a type declaration carries a macro attribute.
pub(crate) fn has_macro_attribute(
    arena: &ParseArena,
    attributes: &crate::parser::ast::Attributes,
) -> bool {
    attributes
        .iter()
        .any(|attr| is_macro_name(arena.get_string(attr.0.txt)))
}

/// Mark an attribute as done: `@Json.codec` becomes `@expanded.Json.codec`,
/// which is inert.
fn retire_attribute(discovery: &mut Discovery, arena: &ParseArena, name: &str, loc: LocIdx) {
    let at = range(arena, loc);
    let text = discovery.text.slice(at.0, at.1).to_string();
    discovery.edits.push(Edit::replace(
        at.0,
        at.1,
        text.replacen(name, &format!("expanded.{name}"), 1),
    ));
}

/// `@M.f let x = ...`: the macro gets the binding as syntax and its result
/// replaces the item. `None`: no macro attribute.
pub(crate) fn value_item(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    item: &ParsedStructureItem,
) -> Option<TypeCoreError> {
    let arena = tctx.arena;
    let ParsedStructureItemDesc::Pstr_value((_, bindings)) = &item.pstr_desc else {
        return None;
    };
    let bindings = arena.vb_list(*bindings);
    let (binding, (name, attr_loc)) = bindings.iter().find_map(|binding| {
        macro_attributes(arena, &binding.pvb_attributes)
            .into_iter()
            .next()
            .map(|found| (binding, found))
    })?;
    let loc = item.pstr_loc;
    let desc = match find_macro(tctx, env, attr_loc, &name) {
        Ok(desc) => desc,
        Err(error) => return Some(error),
    };
    if !discovering(tctx) {
        return Some(required(tctx, loc));
    }
    if bindings.len() != 1 {
        return Some(fail(
            tctx,
            attr_loc,
            format!("`@{name}` works on a `let` with one binding."),
        ));
    }
    let ctx = tctx.type_ctx;
    let (signature, _, _) = signature(ctx, crate::types::instance(ctx, desc.val_type));
    if signature.params != [ParamKind::Binding] || signature.result != ResultKind::Decls {
        return Some(fail(
            tctx,
            attr_loc,
            format!(
                "A macro on a `let` has the type `Decl.value => decls`, and `{name}` does not."
            ),
        ));
    }
    let pat = arena.get_pat(binding.pvb_pat);
    let pat_range = range(arena, pat.ppat_loc);
    let expr_range = range(arena, arena.get_expr(binding.pvb_expr).pexp_loc);
    let bound = match &pat.ppat_desc {
        PatternDesc::Ppat_var(name) => arena.get_string(name.txt).to_string(),
        _ => String::new(),
    };
    let at = range(arena, loc);
    let mut table = TypeTable::default();
    with_discovery(tctx, |tctx, discovery| {
        let args = Ok(vec![json!({
            "name": bound,
            "pat": { "c": discovery.text.slice(pat_range.0, pat_range.1), "$o": table.origin(pat_range) },
            "expr": { "c": discovery.text.slice(expr_range.0, expr_range.1), "$o": table.origin(expr_range) },
        })]);
        if let Some(code) = run_call(tctx, env, discovery, &mut table, at, &name, args, None) {
            discovery
                .edits
                .push(Edit::with(at.0, at.1, vec![Segment::Code(code)]));
        }
    });
    Some(pending(tctx, loc))
}

/// What stops the typing of an item before it starts: a type item with a
/// macro in an ordinary compilation, and a module whose name is a hole.
pub(crate) fn item_stops_typing(
    tctx: &mut TypeCheckContext<'_>,
    item: &ParsedStructureItem,
) -> Option<TypeCoreError> {
    match &item.pstr_desc {
        ParsedStructureItemDesc::Pstr_type(_) => type_item_requires_expansion(tctx, item),
        ParsedStructureItemDesc::Pstr_module(binding) => module_name_hole(tctx, binding),
        _ => None,
    }
}

/// `module ${name} = ...` outside a quote: the hole is the module's name.
fn module_name_hole(
    tctx: &mut TypeCheckContext<'_>,
    binding: &ModuleBinding,
) -> Option<TypeCoreError> {
    if tctx.arena.get_string(binding.pmb_name.txt) != HOLE_MODULE_NAME {
        return None;
    }
    let loc = binding.pmb_name.loc;
    Some(if matches!(tctx.macro_mode, MacroMode::Off) {
        required(tctx, loc)
    } else {
        fail(tctx, loc, HOLE_OUTSIDE_QUOTE)
    })
}

/// Whether a type item carries a macro, for an ordinary compilation to
/// stop at.
fn type_item_requires_expansion(
    tctx: &mut TypeCheckContext<'_>,
    item: &ParsedStructureItem,
) -> Option<TypeCoreError> {
    if discovering(tctx) {
        return None;
    }
    let ParsedStructureItemDesc::Pstr_type(inner) = &item.pstr_desc else {
        return None;
    };
    let arena = tctx.arena;
    if !inner
        .1
        .iter()
        .any(|decl| has_macro_attribute(arena, &decl.ptype_attributes))
    {
        return None;
    }
    // After expansion: the type itself is checked as written.
    if leave(tctx, item.pstr_loc) {
        return None;
    }
    Some(required(tctx, item.pstr_loc))
}

/// `@M.f type t = ...`, after the declaration is type checked in `env`: the
/// macro gets the declaration and its result is added after the item.
pub(crate) fn type_item(tctx: &mut TypeCheckContext<'_>, env: &Env, item: &ParsedStructureItem) {
    if !discovering(tctx) {
        return;
    }
    let ParsedStructureItemDesc::Pstr_type(inner) = &item.pstr_desc else {
        return;
    };
    let arena = tctx.arena;
    let item_range = range(arena, item.pstr_loc);
    for decl in inner.1.iter() {
        for (name, attr_loc) in macro_attributes(arena, &decl.ptype_attributes) {
            let at = range(arena, attr_loc);
            let desc = match find_macro(tctx, env, attr_loc, &name) {
                Ok(desc) => desc,
                Err(error) => {
                    let message = match error {
                        TypeCoreError::ExtensionError(error) => error.message,
                        _ => format!("The macro `{name}` cannot be used here."),
                    };
                    with_discovery(tctx, |_, discovery| discovery.error(at, message));
                    continue;
                }
            };
            let ctx = tctx.type_ctx;
            let (signature, _, _) = signature(ctx, crate::types::instance(ctx, desc.val_type));
            if signature.params != [ParamKind::Decl] || signature.result != ResultKind::Decls {
                with_discovery(tctx, |_, discovery| {
                    discovery.error(
                        at,
                        format!("A macro on a type has the type `Type.decl => decls`, and `{name}` does not."),
                    )
                });
                continue;
            }
            let type_name = arena.get_string(decl.ptype_name.txt).to_string();
            let Some((path, type_decl)) = lookup_type(tctx, env, &type_name) else {
                continue;
            };
            let ty = ctx.new_constr(path, type_decl.type_params.clone());
            let mut table = TypeTable::default();
            let mut type_value = reflect::type_ref(ctx, &mut table, ty);
            if type_decl.type_params.is_empty() {
                type_value["c"] = Value::String(type_name.clone());
            }
            let attrs: Vec<Value> = decl
                .ptype_attributes
                .iter()
                .filter(|attr| !is_macro_name(arena.get_string(attr.0.txt)))
                .map(|attr| json!({ "name": arena.get_string(attr.0.txt) }))
                .collect();
            with_discovery(tctx, |tctx, discovery| {
                let args = Ok(vec![
                    json!({ "name": type_name, "typ": type_value, "attrs": attrs }),
                ]);
                if let Some(code) =
                    run_call(tctx, env, discovery, &mut table, at, &name, args, None)
                {
                    discovery.edits.push(Edit::with(
                        item_range.1,
                        item_range.1,
                        vec![
                            Segment::For(at.0, at.1, None),
                            Segment::Text("\n".into()),
                            Segment::Code(code),
                        ],
                    ));
                    retire_attribute(discovery, arena, &name, attr_loc);
                }
            });
        }
    }
}

fn lookup_type(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    name: &str,
) -> Option<(Path, crate::types::TypeDeclaration)> {
    let _ = tctx;
    let (path, decl) = env.find_type_with_path(name).ok()?;
    Some((path, decl.clone()))
}
