//! JavaScript IR - Intermediate representation for JavaScript output.
//!
//! This module provides the JavaScript IR, which is the final intermediate
//! representation before generating JavaScript source code. It's a subset
//! of JavaScript AST specialized for the ReScript compilation target.
//!
//! # Architecture
//!
//! The JS IR is organized into:
//!
//! - [`op`] - Operators, properties, and other JS-specific types
//! - Expressions - Values that produce results
//! - Statements - Instructions that have effects
//! - Programs - Complete compilation units

pub mod op;
pub mod printer;

use std::collections::HashMap;
use std::ffi::OsString;
use std::fs;
use std::path::{Component, Path as FsPath, PathBuf};

use crate::cmi::persistent_env::{CmjExportConstant, PersistentEnv};
use crate::ident::Ident;
use crate::lambda::SwitchCaseTag;
use crate::lambda::tag_info::TagInfo;
pub use op::{BinOp, IdentInfo, Kind, LengthObject, MutableFlag, Number, Property, PropertyName};
pub use printer::{JsPrinter, print_block, print_deps_program, print_expression, print_program};

/// Module identifier for imports/requires
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleId {
    /// The module identifier
    pub id: Ident,
    /// Module kind (Ml, Runtime, External)
    pub kind: Kind,
    /// Is this a dynamic import?
    pub dynamic_import: bool,
}

/// Output module format used to resolve import paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleFormat {
    /// ECMAScript modules (`.mjs`)
    EsModule,
    /// CommonJS (`.js`, `.bs.js`)
    CommonJs,
}

/// Resolves lowered module identifiers to emitted JavaScript import paths.
#[derive(Clone)]
pub struct ModulePathResolver {
    format: ModuleFormat,
    output_suffix: String,
    current_source_path: Option<PathBuf>,
    runtime_path: Option<PathBuf>,
    persistent_env: Option<PersistentEnv>,
    path_overrides: HashMap<String, String>,
}

impl ModulePathResolver {
    /// Build a resolver from the current compilation context.
    pub fn from_compile_options(
        source_filename: Option<&str>,
        output_path: Option<&FsPath>,
        runtime_path: Option<&FsPath>,
        persistent_env: Option<PersistentEnv>,
    ) -> Self {
        Self {
            format: module_format_from_output_path(output_path),
            output_suffix: output_suffix_from_path(output_path),
            current_source_path: source_filename
                .map(|path| normalize_absolute_path(FsPath::new(path))),
            runtime_path: runtime_path.map(normalize_absolute_path),
            persistent_env,
            path_overrides: HashMap::new(),
        }
    }

    /// Override a module's emitted JS import path.
    pub fn set_module_path_override(&mut self, module_name: &str, path: String) {
        self.path_overrides.insert(module_name.to_string(), path);
    }

    /// Resolve a same-directory source fallback path for an ML module.
    pub fn resolve_local_module_fallback_path(&self, module_name: &str) -> Option<String> {
        let target_source = self.fallback_local_module_source(module_name)?;
        self.relative_output_path(&target_source)
    }

    /// Resolve the emitted JavaScript import path for a lowered module id.
    pub fn resolve_module_path(&self, module: &ModuleId) -> Option<String> {
        if let Some(path) = self.path_overrides.get(module.id.name()) {
            return Some(path.clone());
        }

        match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            Kind::Runtime => Some(self.runtime_module_path(module.id.name())),
            Kind::Ml => {
                if self.is_runtime_module(module.id.name()) {
                    Some(self.runtime_module_path(module.id.name()))
                } else {
                    let target_source = self
                        .persistent_env
                        .as_ref()
                        .and_then(|env| env.resolve_module_source_path(module.id.name()))
                        .map(|path| normalize_absolute_path(&path))?;
                    self.relative_output_path(&target_source)
                }
            }
        }
    }

    /// Return the side-effect reason OCaml records for a required module, if it
    /// is not marked pure.
    pub fn module_side_effect_reason(&self, module: &ModuleId) -> Option<String> {
        if self.is_pure_module(module) {
            return None;
        }

        Some(match &module.kind {
            Kind::External { name, .. } => name.clone(),
            Kind::Runtime | Kind::Ml => module.id.name().to_string(),
        })
    }

    /// Read closed constant exports recorded in a module's companion `.cmj`.
    pub fn module_cmj_export_constants(
        &self,
        module_name: &str,
    ) -> Option<HashMap<String, CmjExportConstant>> {
        self.persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_export_constants(module_name))
            .map(|exports| exports.into_iter().collect())
    }

    fn runtime_module_path(&self, module_name: &str) -> String {
        let dir = match self.format {
            ModuleFormat::EsModule => "es6",
            ModuleFormat::CommonJs => "js",
        };
        format!("@rescript/runtime/lib/{dir}/{module_name}.js")
    }

    fn is_runtime_module(&self, module_name: &str) -> bool {
        let Some(runtime_path) = &self.runtime_path else {
            return false;
        };
        let ocaml_dir = runtime_path.join("lib").join("ocaml");
        ocaml_dir.join(format!("{module_name}.cmi")).exists()
            || ocaml_dir.join(format!("{module_name}.ast")).exists()
            || ocaml_dir.join(format!("{module_name}.iast")).exists()
    }

    fn is_pure_module(&self, module: &ModuleId) -> bool {
        match &module.kind {
            Kind::Runtime => true,
            Kind::External { .. } => false,
            Kind::Ml => {
                if self.is_runtime_module(module.id.name()) {
                    true
                } else {
                    self.persistent_env
                        .as_ref()
                        .and_then(|env| env.module_cmj_is_pure(module.id.name()))
                        .unwrap_or(false)
                }
            }
        }
    }

    fn relative_output_path(&self, target_source: &FsPath) -> Option<String> {
        let current_source = self.current_source_path.as_ref()?;
        let from_dir = current_source.parent()?;
        let target_dir = target_source.parent()?;
        let target_stem = target_source.file_stem()?.to_str()?;
        let target_output = target_dir.join(format!("{target_stem}{}", self.output_suffix));
        let relative = relative_path_between(from_dir, &target_output)?;
        let mut rendered = relative.to_string_lossy().replace('\\', "/");
        if !rendered.starts_with("./") && !rendered.starts_with("../") {
            rendered = format!("./{rendered}");
        }
        Some(rendered)
    }

    fn fallback_local_module_source(&self, module_name: &str) -> Option<PathBuf> {
        let current_source = self.current_source_path.as_ref()?;
        let current_dir = current_source.parent()?;
        let entries = fs::read_dir(current_dir)
            .ok()?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect::<Vec<_>>();
        let mut candidate_stems = vec![module_name.to_string()];
        if let Some(first) = module_name.chars().next() {
            if first.is_ascii_uppercase() {
                candidate_stems.push(format!(
                    "{}{}",
                    first.to_ascii_lowercase(),
                    &module_name[first.len_utf8()..]
                ));
            }
        }

        for stem in candidate_stems {
            for ext in ["res", "ml"] {
                let candidate_name = format!("{stem}.{ext}");
                if let Some(path) = entries.iter().find(|path| {
                    path.file_name()
                        .and_then(|name| name.to_str())
                        .is_some_and(|name| name.eq_ignore_ascii_case(&candidate_name))
                }) {
                    return Some(path.clone());
                }
            }
        }

        None
    }
}

fn module_format_from_output_path(output_path: Option<&FsPath>) -> ModuleFormat {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ModuleFormat::EsModule,
        _ => ModuleFormat::CommonJs,
    }
}

fn output_suffix_from_path(output_path: Option<&FsPath>) -> String {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ".mjs".to_string(),
        Some(name) if name.ends_with(".bs.js") => ".bs.js".to_string(),
        _ => ".js".to_string(),
    }
}

fn normalize_absolute_path(path: &FsPath) -> PathBuf {
    let base = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    };
    normalize_lexical_path(base)
}

fn normalize_lexical_path(path: PathBuf) -> PathBuf {
    let mut prefix: Option<OsString> = None;
    let mut has_root = false;
    let mut parts: Vec<OsString> = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_os_string()),
            Component::RootDir => has_root = true,
            Component::CurDir => {}
            Component::ParentDir => match parts.last() {
                Some(last) if last != ".." => {
                    parts.pop();
                }
                _ if !has_root && prefix.is_none() => parts.push(OsString::from("..")),
                _ => {}
            },
            Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if has_root {
        normalized.push(std::path::MAIN_SEPARATOR.to_string());
    }
    for part in parts {
        normalized.push(part);
    }

    if normalized.as_os_str().is_empty() && !has_root {
        PathBuf::from(".")
    } else {
        normalized
    }
}

fn relative_path_between(base_dir: &FsPath, target: &FsPath) -> Option<PathBuf> {
    let base = normalize_lexical_path(base_dir.to_path_buf());
    let target = normalize_lexical_path(target.to_path_buf());

    let base_components: Vec<_> = base.components().collect();
    let target_components: Vec<_> = target.components().collect();

    if matches!(
        (base_components.first(), target_components.first()),
        (Some(Component::Prefix(left)), Some(Component::Prefix(right)))
            if left.as_os_str() != right.as_os_str()
    ) {
        return None;
    }

    let shared_prefix = base_components
        .iter()
        .zip(target_components.iter())
        .take_while(|(left, right)| left == right)
        .count();

    let mut relative = PathBuf::new();
    for component in &base_components[shared_prefix..] {
        if matches!(component, Component::Normal(_)) {
            relative.push("..");
        }
    }
    for component in &target_components[shared_prefix..] {
        match component {
            Component::Normal(part) => relative.push(part),
            Component::CurDir => {}
            Component::ParentDir => relative.push(".."),
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }

    Some(relative)
}

/// Variable identifier (local or qualified)
#[derive(Debug, Clone, PartialEq)]
pub enum VIdent {
    /// Local identifier
    Id(Ident),
    /// Qualified identifier (module.member)
    Qualified(ModuleId, Option<String>),
}

/// String delimiter type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delim {
    /// No special delimiter
    None,
    /// StarJ format
    StarJ,
    /// No quotes (raw)
    NoQuotes,
    /// Backtick template literal
    BackQuotes,
}

/// For loop direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForDirection {
    /// i++
    Upto,
    /// i--
    Downto,
    /// for...of style
    Up,
}

/// Call information for function calls
#[derive(Debug, Clone, Default)]
pub struct CallInfo {
    /// Is this a method call?
    pub is_method: bool,
    /// Additional metadata
    pub comment: Option<String>,
}

/// Function environment (for closures)
#[derive(Debug, Clone, Default)]
pub struct FunEnv {
    /// Captured variables
    pub captured: Vec<Ident>,
}

/// Raw JavaScript code info
#[derive(Debug, Clone, PartialEq)]
pub struct JsRawInfo {
    /// The JavaScript code
    pub code: String,
    /// Is this a statement?
    pub is_stmt: bool,
}

/// JavaScript expression description
#[derive(Debug, Clone)]
pub enum ExpressionDesc {
    /// Length property access (arr.length, str.length)
    Length(Box<Expression>, LengthObject),

    /// Null/undefined check (== null)
    IsNullOrUndefined(Box<Expression>),

    /// String concatenation
    StringAppend(Box<Expression>, Box<Expression>),

    /// Boolean literal
    Bool(bool),

    /// typeof operator
    Typeof(Box<Expression>),

    /// in operator (prop in obj)
    In(Box<Expression>, Box<Expression>),

    /// Logical not (!)
    JsNot(Box<Expression>),

    /// Bitwise not (~)
    JsBnot(Box<Expression>),

    /// Sequence expression (a, b)
    Seq(Box<Expression>, Box<Expression>),

    /// Conditional expression (a ? b : c)
    Cond(Box<Expression>, Box<Expression>, Box<Expression>),

    /// Binary operation
    Bin(BinOp, Box<Expression>, Box<Expression>),

    /// Function.prototype.apply call
    FlatCall(Box<Expression>, Box<Expression>),

    /// Function call
    Call(Box<Expression>, Vec<Expression>, CallInfo),

    /// String index access (str[i])
    StringIndex(Box<Expression>, Box<Expression>),

    /// Array index access (arr[i])
    ArrayIndex(Box<Expression>, Box<Expression>),

    /// Tagged template literal
    TaggedTemplate(Box<Expression>, Vec<Expression>, Vec<Expression>),

    /// Static property access (obj.prop or obj["prop"])
    StaticIndex(Box<Expression>, String, Option<i32>),

    /// new expression
    New(Box<Expression>, Option<Vec<Expression>>),

    /// Variable reference
    Var(VIdent),

    /// Function expression
    Fun {
        is_method: bool,
        params: Vec<Ident>,
        body: Block,
        env: FunEnv,
        return_unit: bool,
        async_: bool,
        directive: Option<String>,
    },

    /// String literal
    Str { delim: Delim, txt: String },

    /// Raw JavaScript code
    RawJsCode(JsRawInfo),

    /// Array literal
    Array(Vec<Expression>, MutableFlag),

    /// Optional block (Some value)
    OptionalBlock(Box<Expression>, bool),

    /// Caml block (variant, record, tuple)
    CamlBlock(Vec<Expression>, MutableFlag, Box<Expression>, TagInfo),

    /// Block tag access
    CamlBlockTag(Box<Expression>, String),

    /// Number literal
    Number(Number),

    /// Object literal
    Object(Option<Box<Expression>>, PropertyMap),

    /// undefined literal
    Undefined { is_unit: bool },

    /// null literal
    Null,

    /// await expression
    Await(Box<Expression>),

    /// spread operator
    Spread(Box<Expression>),
}

/// Property map for object literals
pub type PropertyMap = Vec<(PropertyName, Expression)>;

/// JavaScript expression
#[derive(Debug, Clone)]
pub struct Expression {
    /// Expression description
    pub desc: ExpressionDesc,
    /// Optional comment
    pub comment: Option<String>,
}

impl Expression {
    /// Create a new expression
    pub fn new(desc: ExpressionDesc) -> Self {
        Self {
            desc,
            comment: None,
        }
    }

    /// Create a new expression with a comment
    pub fn with_comment(desc: ExpressionDesc, comment: impl Into<String>) -> Self {
        Self {
            desc,
            comment: Some(comment.into()),
        }
    }

    /// Create a boolean expression
    pub fn bool(value: bool) -> Self {
        Self::new(ExpressionDesc::Bool(value))
    }

    /// Create a variable expression
    pub fn var(id: Ident) -> Self {
        Self::new(ExpressionDesc::Var(VIdent::Id(id)))
    }

    /// Create a qualified variable expression
    pub fn qualified(module: ModuleId, member: Option<String>) -> Self {
        Self::new(ExpressionDesc::Var(VIdent::Qualified(module, member)))
    }

    /// Create a string expression
    pub fn string(txt: impl Into<String>) -> Self {
        Self::new(ExpressionDesc::Str {
            delim: Delim::None,
            txt: txt.into(),
        })
    }

    /// Create an undefined expression
    pub fn undefined(is_unit: bool) -> Self {
        Self::new(ExpressionDesc::Undefined { is_unit })
    }

    /// Create a null expression
    pub fn null() -> Self {
        Self::new(ExpressionDesc::Null)
    }

    /// Create a number expression
    pub fn number(n: Number) -> Self {
        Self::new(ExpressionDesc::Number(n))
    }

    /// Create an array expression
    pub fn array(elements: Vec<Expression>, mutable_flag: MutableFlag) -> Self {
        Self::new(ExpressionDesc::Array(elements, mutable_flag))
    }

    /// Create a binary operation
    pub fn bin(op: BinOp, left: Expression, right: Expression) -> Self {
        if let Some(expr) = rewrite_plus_negative_int_rhs(op, &left, &right) {
            return expr;
        }
        if let Some(value) = fold_strict_comparison(op, &left, &right) {
            return Expression::bool(value);
        }
        match op {
            BinOp::And => js_and_expression(left, right),
            BinOp::Or => js_or_expression(left, right),
            _ => raw_bin_expression(op, left, right),
        }
    }

    /// Create a function call
    pub fn call(func: Expression, args: Vec<Expression>, info: CallInfo) -> Self {
        Self::new(ExpressionDesc::Call(Box::new(func), args, info))
    }

    /// Create a conditional expression
    pub fn cond(test: Expression, consequent: Expression, alternate: Expression) -> Self {
        if let (
            ExpressionDesc::Seq(consequent_effect, consequent_suffix),
            ExpressionDesc::Seq(alternate_effect, alternate_suffix),
        ) = (&consequent.desc, &alternate.desc)
        {
            if matches!(
                consequent_suffix.as_ref().desc,
                ExpressionDesc::Undefined { .. }
            ) && matches!(
                alternate_suffix.as_ref().desc,
                ExpressionDesc::Undefined { .. }
            ) {
                return Self::new(ExpressionDesc::Seq(
                    Box::new(Expression::cond(
                        test,
                        consequent_effect.as_ref().clone(),
                        alternate_effect.as_ref().clone(),
                    )),
                    Box::new(Expression::undefined(false)),
                ));
            }
        }

        match &test.desc {
            ExpressionDesc::Bool(false) | ExpressionDesc::Number(Number::Int { i: 0, .. }) => {
                return alternate;
            }
            ExpressionDesc::Bool(true) => return consequent,
            ExpressionDesc::Number(_)
            | ExpressionDesc::Array(_, _)
            | ExpressionDesc::CamlBlock(_, _, _, _)
                if expression_has_no_side_effects(&test) =>
            {
                return consequent;
            }
            _ => {}
        }

        if matches!(
            (&consequent.desc, &alternate.desc),
            (ExpressionDesc::Bool(true), ExpressionDesc::Bool(false))
        ) {
            return test;
        }

        if ocaml_eq_expression(&consequent, &alternate) {
            if expression_has_no_side_effects(&test) {
                return consequent;
            }

            return Self::new(ExpressionDesc::Seq(
                Box::new(test),
                Box::new(consequent),
            ));
        }

        if let ExpressionDesc::Cond(inner_test, inner_then, inner_else) = &consequent.desc {
            if ocaml_eq_expression(inner_else, &alternate) {
                return Self::cond(
                    js_and_expression(test, inner_test.as_ref().clone()),
                    inner_then.as_ref().clone(),
                    alternate,
                );
            }

            if ocaml_eq_expression(inner_then, &alternate) {
                return Self::cond(
                    js_and_expression(test, Expression::not(inner_test.as_ref().clone())),
                    inner_else.as_ref().clone(),
                    alternate,
                );
            }
        }

        if let ExpressionDesc::Cond(inner_test, inner_then, inner_else) = &alternate.desc {
            if ocaml_eq_expression(&consequent, inner_then) {
                return Self::cond(
                    js_or_expression(test, inner_test.as_ref().clone()),
                    consequent,
                    inner_else.as_ref().clone(),
                );
            }

            if ocaml_eq_expression(&consequent, inner_else) {
                return Self::cond(
                    js_or_expression(test, Expression::not(inner_test.as_ref().clone())),
                    consequent,
                    inner_then.as_ref().clone(),
                );
            }
        }

        if let ExpressionDesc::JsNot(inner) = test.desc {
            if expression_branch_is_not_empty(&alternate) {
                return Self::cond(*inner, alternate, consequent);
            }

            return Self::new(ExpressionDesc::Cond(
                Box::new(Expression::new(ExpressionDesc::JsNot(inner))),
                Box::new(consequent),
                Box::new(alternate),
            ));
        }

        if matches!(alternate.desc, ExpressionDesc::Bool(false)) {
            if let Some(expr) = simplify_and_expression(&test, &consequent) {
                return expr;
            }
        }

        if matches!(consequent.desc, ExpressionDesc::Bool(false)) {
            if let Some(expr) = simplify_and_expression(&Expression::not(test.clone()), &alternate)
            {
                return expr;
            }
        }

        Self::new(ExpressionDesc::Cond(
            Box::new(test),
            Box::new(consequent),
            Box::new(alternate),
        ))
    }

    /// Create a negated boolean expression, mirroring OCaml `Js_exp_make.not`.
    pub fn not(expr: Expression) -> Self {
        let Expression { desc, comment } = expr;
        match desc {
            ExpressionDesc::Number(Number::Int { i, .. }) => Expression {
                desc: ExpressionDesc::Bool(i == 0),
                comment,
            },
            ExpressionDesc::JsNot(inner) => *inner,
            ExpressionDesc::Bool(value) => Expression {
                desc: ExpressionDesc::Bool(!value),
                comment,
            },
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::NotEqEq, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::NotEqEq, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::EqEqEq, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Lt, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Ge, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Ge, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Lt, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Le, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Gt, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Gt, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Le, left, right),
                comment,
            },
            other => {
                let expr = Expression {
                    desc: other,
                    comment,
                };
                push_negation(expr.clone()).unwrap_or_else(|| Expression {
                    desc: ExpressionDesc::JsNot(Box::new(expr)),
                    comment: None,
                })
            }
        }
    }
}

fn fold_strict_comparison(op: BinOp, left: &Expression, right: &Expression) -> Option<bool> {
    let equality = match op {
        BinOp::EqEqEq => true,
        BinOp::NotEqEq => false,
        _ => return None,
    };

    if let Some(equal) = fold_strict_equality(left, right) {
        return Some(if equality { equal } else { !equal });
    }

    None
}

fn fold_strict_equality(left: &Expression, right: &Expression) -> Option<bool> {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::OptionalBlock(left_inner, _),
            ExpressionDesc::OptionalBlock(right_inner, _),
        ) => {
            return fold_strict_equality(left_inner, right_inner);
        }
        (
            ExpressionDesc::Number(Number::Int { i: left_int, .. }),
            ExpressionDesc::Number(Number::Int { i: right_int, .. }),
        ) => {
            return Some(left_int == right_int);
        }
        (
            ExpressionDesc::Str {
                txt: left_txt,
                delim: left_delim,
            },
            ExpressionDesc::Str {
                txt: right_txt,
                delim: right_delim,
            },
        ) => {
            return fold_strict_string_equality(left_txt, left_delim, right_txt, right_delim);
        }
        _ => {}
    }

    let same_nullish = matches!(
        (&left.desc, &right.desc),
        (ExpressionDesc::Null, ExpressionDesc::Null)
            | (
                ExpressionDesc::Undefined { .. },
                ExpressionDesc::Undefined { .. }
            )
    );
    if same_nullish {
        return Some(true);
    }

    let mismatched_nullish = matches!(
        (&left.desc, &right.desc),
        (ExpressionDesc::Null, ExpressionDesc::Undefined { .. })
            | (ExpressionDesc::Undefined { .. }, ExpressionDesc::Null)
    );
    if mismatched_nullish {
        return Some(false);
    }

    let undefined_optional_block_mismatch = matches!(
        (&left.desc, &right.desc),
        (
            ExpressionDesc::Undefined { .. },
            ExpressionDesc::OptionalBlock(_, _)
        ) | (
            ExpressionDesc::OptionalBlock(_, _),
            ExpressionDesc::Undefined { .. }
        )
    );
    if undefined_optional_block_mismatch
        && expression_has_no_side_effects(left)
        && expression_has_no_side_effects(right)
    {
        return Some(false);
    }

    if is_nullish_literal(left) && is_nullish_eq_impossible_non_null_expr(right) {
        return Some(false);
    }

    if is_nullish_literal(right) && is_nullish_eq_impossible_non_null_expr(left) {
        return Some(false);
    }

    None
}

fn fold_strict_string_equality(
    left_txt: &str,
    left_delim: &Delim,
    right_txt: &str,
    right_delim: &Delim,
) -> Option<bool> {
    if left_delim != right_delim {
        return None;
    }

    if left_txt == right_txt {
        Some(true)
    } else if is_simple_string_comparison(left_txt) && is_simple_string_comparison(right_txt) {
        Some(false)
    } else {
        None
    }
}

fn is_simple_string_comparison(text: &str) -> bool {
    text.is_ascii() && !text.as_bytes().contains(&b'\\')
}

fn is_nullish_literal(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Null | ExpressionDesc::Undefined { .. }
    )
}

fn is_nullish_eq_impossible_non_null_expr(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Bool(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Typeof(_)
            | ExpressionDesc::Fun { .. }
            | ExpressionDesc::Array(_, _)
            | ExpressionDesc::CamlBlock(_, _, _, _)
    ) && expression_has_no_side_effects(expr)
}

pub(crate) fn expression_has_no_side_effects(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. } => true,
        ExpressionDesc::StaticIndex(target, _, _) => expression_has_no_side_effects(target),
        ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right) => {
            expression_has_no_side_effects(left) && expression_has_no_side_effects(right)
        }
        ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Length(inner, _)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _) => expression_has_no_side_effects(inner),
        ExpressionDesc::Array(items, _) => items.iter().all(expression_has_no_side_effects),
        ExpressionDesc::CamlBlock(items, _, _, _) => {
            items.iter().all(expression_has_no_side_effects)
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref().is_none_or(expression_has_no_side_effects)
                && props
                    .iter()
                    .all(|(_, value)| expression_has_no_side_effects(value))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_has_no_side_effects(test)
                && expression_has_no_side_effects(consequent)
                && expression_has_no_side_effects(alternate)
        }
        ExpressionDesc::Bin(op, left, right) => {
            *op != BinOp::Eq
                && expression_has_no_side_effects(left)
                && expression_has_no_side_effects(right)
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_has_no_side_effects(tag)
                && strings.iter().all(expression_has_no_side_effects)
                && values.iter().all(expression_has_no_side_effects)
        }
        ExpressionDesc::FlatCall(_, _)
        | ExpressionDesc::Call(_, _, _)
        | ExpressionDesc::New(_, _)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Await(_)
        | ExpressionDesc::Spread(_) => false,
    }
}

fn rewrite_plus_negative_int_rhs(
    op: BinOp,
    left: &Expression,
    right: &Expression,
) -> Option<Expression> {
    match (op, &right.desc) {
        (BinOp::Plus, ExpressionDesc::Number(Number::Int { i, .. })) if *i < 0 => {
            let mut positive = right.clone();
            if let ExpressionDesc::Number(Number::Int { i, .. }) = &mut positive.desc {
                *i = i.wrapping_neg();
            }
            Some(Expression::new(ExpressionDesc::Bin(
                BinOp::Minus,
                Box::new(left.clone()),
                Box::new(positive),
            )))
        }
        _ => None,
    }
}

fn expression_branch_is_not_empty(expr: &Expression) -> bool {
    !matches!(
        expr.desc,
        ExpressionDesc::Number(Number::Int { i: 0, .. }) | ExpressionDesc::Undefined { .. }
    )
}

fn push_negation(expr: Expression) -> Option<Expression> {
    let Expression { desc, comment } = expr;
    match desc {
        ExpressionDesc::JsNot(inner) => Some(*inner),
        ExpressionDesc::Bool(value) => Some(Expression {
            desc: ExpressionDesc::Bool(!value),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => Some(Expression {
            desc: ExpressionDesc::Bin(BinOp::NotEqEq, left, right),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::NotEqEq, left, right) => Some(Expression {
            desc: ExpressionDesc::Bin(BinOp::EqEqEq, left, right),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::And, left, right) => {
            let left = push_negation(*left)?;
            let right = push_negation(*right)?;
            Some(Expression {
                desc: ExpressionDesc::Bin(BinOp::Or, Box::new(left), Box::new(right)),
                comment,
            })
        }
        ExpressionDesc::Bin(BinOp::Or, left, right) => {
            let left = push_negation(*left)?;
            let right = push_negation(*right)?;
            Some(Expression {
                desc: ExpressionDesc::Bin(BinOp::And, Box::new(left), Box::new(right)),
                comment,
            })
        }
        _ => None,
    }
}

/// Switch case clause
#[derive(Debug, Clone)]
pub struct CaseClause {
    /// Case body
    pub body: Block,
    /// Should break after this case?
    pub should_break: bool,
    /// Optional comment
    pub comment: Option<String>,
}

/// Integer switch clause
pub type IntClause = (i32, CaseClause);

/// String switch clause (tag type, case clause)
#[derive(Debug, Clone)]
pub struct StringClause {
    /// Tag type (from Ast_untagged_variants)
    pub tag_type: SwitchCaseTag,
    /// Case clause
    pub clause: CaseClause,
}

/// Variable declaration
#[derive(Debug, Clone)]
pub struct VariableDeclaration {
    /// Variable identifier
    pub ident: Ident,
    /// Initial value
    pub value: Option<Expression>,
    /// Declaration property (let, const, var semantics)
    pub property: Property,
    /// Usage info
    pub ident_info: IdentInfo,
}

/// JavaScript statement description
#[derive(Debug, Clone)]
pub enum StatementDesc {
    /// Block of statements
    Block(Block),

    /// Variable declaration
    Variable(VariableDeclaration),

    /// Expression statement
    Exp(Expression),

    /// If statement
    If(Expression, Block, Block),

    /// While loop
    While(Expression, Block),

    /// For loop (init, end, ident, direction, body)
    ForRange(Option<Expression>, Expression, Ident, ForDirection, Block),

    /// Continue statement
    Continue,

    /// Break statement
    Break,

    /// Return statement
    Return(Expression),

    /// Integer switch
    IntSwitch(Expression, Vec<IntClause>, Option<Block>),

    /// String switch
    StringSwitch(Expression, Vec<StringClause>, Option<Block>),

    /// Throw statement
    Throw(Expression),

    /// Try statement (body, catch, finally)
    Try(Block, Option<(Ident, Block)>, Option<Block>),

    /// Debugger statement
    Debugger,
}

/// JavaScript statement
#[derive(Debug, Clone)]
pub struct Statement {
    /// Statement description
    pub desc: StatementDesc,
    /// Optional comment
    pub comment: Option<String>,
}

impl Statement {
    /// Create a new statement
    pub fn new(desc: StatementDesc) -> Self {
        Self {
            desc,
            comment: None,
        }
    }

    /// Create a new statement with a comment
    pub fn with_comment(desc: StatementDesc, comment: impl Into<String>) -> Self {
        Self {
            desc,
            comment: Some(comment.into()),
        }
    }

    /// Create an expression statement
    pub fn exp(expr: Expression) -> Self {
        Self::new(StatementDesc::Exp(expr))
    }

    /// Create an if statement
    pub fn if_(cond: Expression, then_: Block, else_: Block) -> Self {
        simplify_if_statement(cond, then_, else_)
    }

    /// Create a while loop
    pub fn while_(cond: Expression, body: Block) -> Self {
        Self::new(StatementDesc::While(cond, body))
    }

    /// Create a return statement
    pub fn return_(expr: Expression) -> Self {
        Self::new(StatementDesc::Return(expr))
    }

    /// Create a throw statement
    pub fn throw(expr: Expression) -> Self {
        Self::new(StatementDesc::Throw(expr))
    }

    /// Create a break statement
    pub fn break_() -> Self {
        Self::new(StatementDesc::Break)
    }

    /// Create a continue statement
    pub fn continue_() -> Self {
        Self::new(StatementDesc::Continue)
    }

    /// Create a debugger statement
    pub fn debugger() -> Self {
        Self::new(StatementDesc::Debugger)
    }

    /// Create a variable declaration
    pub fn variable(decl: VariableDeclaration) -> Self {
        Self::new(StatementDesc::Variable(decl))
    }
}

fn simplify_if_statement(cond: Expression, then_: Block, else_: Block) -> Statement {
    match cond.desc {
        ExpressionDesc::Bool(value) => {
            return Statement::new(StatementDesc::Block(if value { then_ } else { else_ }));
        }
        ExpressionDesc::JsNot(inner) if !else_.is_empty() => {
            return simplify_if_statement(*inner, else_, then_);
        }
        _ => {}
    }

    if then_.is_empty() {
        if else_.is_empty() {
            return Statement::exp(cond);
        }
        return simplify_if_statement(negate_condition(cond), else_, vec![]);
    }

    if let (Some(then_ret), Some(else_ret)) =
        (single_return_expr(&then_), single_return_expr(&else_))
    {
        return Statement::return_(Expression::cond(cond, then_ret, else_ret));
    }

    if let Some(else_ret) = single_return_expr(&else_) {
        let mut block = Vec::with_capacity(1 + then_.len());
        block.push(Statement::new(StatementDesc::If(
            negate_condition(cond),
            vec![Statement::return_(else_ret)],
            vec![],
        )));
        block.extend(then_);
        return Statement::new(StatementDesc::Block(block));
    }

    if block_last_is_terminal(&then_) {
        let mut block = Vec::with_capacity(1 + else_.len());
        block.push(Statement::new(StatementDesc::If(cond, then_, vec![])));
        block.extend(else_);
        return Statement::new(StatementDesc::Block(block));
    }

    if let (Some((lhs_then, rhs_then)), Some((lhs_else, rhs_else))) = (
        single_assignment_expr(&then_),
        single_assignment_expr(&else_),
    ) {
        if same_assignment_target(&lhs_then, &lhs_else) {
            return Statement::exp(Expression::bin(
                BinOp::Eq,
                lhs_then,
                Expression::cond(cond, rhs_then, rhs_else),
            ));
        }
    }

    if let (Some(then_expr), Some(else_expr)) = (single_exp_expr(&then_), single_exp_expr(&else_)) {
        return Statement::exp(Expression::cond(cond, then_expr, else_expr));
    }

    if let Some((nested_cond, nested_then, nested_else)) = single_if_block(&then_) {
        if ocaml_eq_block(nested_else, &else_) {
            return simplify_if_statement(
                js_and_expression(cond, nested_cond.clone()),
                nested_then.clone(),
                nested_else.clone(),
            );
        }

        if ocaml_eq_block(nested_then, &else_) {
            return simplify_if_statement(
                js_and_expression(cond, Expression::not(nested_cond.clone())),
                nested_else.clone(),
                nested_then.clone(),
            );
        }
    }

    if let Some((nested_cond, nested_then, nested_else)) = single_if_block(&else_) {
        if ocaml_eq_block(&then_, nested_then) {
            return simplify_if_statement(
                js_or_expression(cond, nested_cond.clone()),
                then_,
                nested_else.clone(),
            );
        }

        if ocaml_eq_block(&then_, nested_else) {
            return simplify_if_statement(
                js_or_expression(cond, Expression::not(nested_cond.clone())),
                then_,
                nested_then.clone(),
            );
        }
    }

    Statement::new(StatementDesc::If(cond, then_, else_))
}

fn block_last_is_terminal(block: &Block) -> bool {
    matches!(
        block.last().map(|stmt| &stmt.desc),
        Some(StatementDesc::Return(_))
            | Some(StatementDesc::Throw(_))
            | Some(StatementDesc::Continue)
    )
}

fn single_return_expr(block: &Block) -> Option<Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    match &stmt.desc {
        StatementDesc::Return(expr) => Some(expr.clone()),
        _ => None,
    }
}

fn single_assignment_expr(block: &Block) -> Option<(Expression, Expression)> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::Exp(expr) = &stmt.desc else {
        return None;
    };
    let ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) = &expr.desc else {
        return None;
    };
    Some(((*lhs.clone()), (*rhs.clone())))
}

fn same_assignment_target(lhs: &Expression, rhs: &Expression) -> bool {
    match (&lhs.desc, &rhs.desc) {
        (ExpressionDesc::Var(left), ExpressionDesc::Var(right)) => left == right,
        (
            ExpressionDesc::StaticIndex(left_obj, left_field, left_pos),
            ExpressionDesc::StaticIndex(right_obj, right_field, right_pos),
        ) => {
            left_field == right_field
                && left_pos == right_pos
                && same_assignment_target(left_obj, right_obj)
        }
        (
            ExpressionDesc::ArrayIndex(left_obj, left_index),
            ExpressionDesc::ArrayIndex(right_obj, right_index),
        )
        | (
            ExpressionDesc::StringIndex(left_obj, left_index),
            ExpressionDesc::StringIndex(right_obj, right_index),
        ) => {
            same_assignment_target(left_obj, right_obj)
                && same_assignment_target(left_index, right_index)
        }
        _ => false,
    }
}

fn single_exp_expr(block: &Block) -> Option<Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::Exp(expr) = &stmt.desc else {
        return None;
    };
    Some(expr.clone())
}

fn single_if_block(block: &Block) -> Option<(&Expression, &Block, &Block)> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    match &stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => Some((cond, then_block, else_block)),
        _ => None,
    }
}

fn negate_condition(cond: Expression) -> Expression {
    Expression::not(cond)
}

fn raw_bin_expression(op: BinOp, left: Expression, right: Expression) -> Expression {
    Expression::new(ExpressionDesc::Bin(op, Box::new(left), Box::new(right)))
}

fn js_and_expression(left: Expression, right: Expression) -> Expression {
    simplify_and_expression(&left, &right)
        .unwrap_or_else(|| raw_bin_expression(BinOp::And, left, right))
}

fn js_or_expression(left: Expression, right: Expression) -> Expression {
    simplify_or_expression(&left, &right)
        .unwrap_or_else(|| raw_bin_expression(BinOp::Or, left, right))
}

fn simplify_and_expression(left: &Expression, right: &Expression) -> Option<Expression> {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Bool(false), _) | (_, ExpressionDesc::Bool(false)) => {
            return Some(Expression::bool(false));
        }
        (ExpressionDesc::Bool(true), _) => return Some(right.clone()),
        (_, ExpressionDesc::Bool(true)) => return Some(left.clone()),
        _ => {}
    }

    if ocaml_eq_expression(left, right) {
        return Some(left.clone());
    }

    if let Some(expr) = simplify_typeof_and_literal_and(left, right) {
        return Some(expr);
    }
    if let Some(expr) = simplify_typeof_and_literal_and(right, left) {
        return Some(expr);
    }

    if let Some(expr) = simplify_array_is_array_and_literal_and(left, right) {
        return Some(expr);
    }
    if let Some(expr) = simplify_array_is_array_and_literal_and(right, left) {
        return Some(expr);
    }

    if let Some(expr) = simplify_same_var_literal_and(left, right) {
        return Some(expr);
    }

    None
}

fn simplify_or_expression(left: &Expression, right: &Expression) -> Option<Expression> {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Bool(true), _) | (_, ExpressionDesc::Bool(true)) => {
            return Some(Expression::bool(true));
        }
        (ExpressionDesc::Bool(false), _) => return Some(right.clone()),
        (_, ExpressionDesc::Bool(false)) => return Some(left.clone()),
        _ => {}
    }

    let left_not = push_negation(left.clone())?;
    let right_not = push_negation(right.clone())?;
    let simplified = simplify_and_expression(&left_not, &right_not)?;
    push_negation(simplified)
}

fn simplify_typeof_and_literal_and(typeof_expr: &Expression, other: &Expression) -> Option<Expression> {
    let (vident, type_name) = typeof_var_type_test(typeof_expr)?;

    match &other.desc {
        ExpressionDesc::Var(other_vident) if type_name == "boolean" && same_vident(vident, other_vident) => {
            return Some(Expression::bin(
                BinOp::EqEqEq,
                Expression::new(ExpressionDesc::Var(other_vident.clone())),
                Expression::bool(true),
            ));
        }
        ExpressionDesc::JsNot(inner)
            if type_name == "boolean"
                && matches!(&inner.desc, ExpressionDesc::Var(other_vident) if same_vident(vident, other_vident)) =>
        {
            let ExpressionDesc::Var(other_vident) = &inner.desc else {
                unreachable!();
            };
            return Some(Expression::bin(
                BinOp::EqEqEq,
                Expression::new(ExpressionDesc::Var(other_vident.clone())),
                Expression::bool(false),
            ));
        }
        _ => {}
    }

    let (op, other_vident, literal) = strict_var_literal_comparison(other)?;
    if !same_vident(vident, other_vident) {
        return None;
    }

    if op == BinOp::EqEqEq {
        if literal_matches_type_name(literal, type_name) {
            return Some(other.clone());
        }
        if matches!(type_name, "boolean" | "string" | "number")
            && is_scalar_nullish_literal(literal)
        {
            return Some(Expression::bool(false));
        }
        return None;
    }

    if type_name == "boolean" {
        if let ExpressionDesc::Bool(value) = literal.desc {
            return Some(Expression::bool(!value));
        }
    }

    if matches!(type_name, "string" | "number") && literal_matches_type_name(literal, type_name) {
        return None;
    }

    if type_name == "object" && matches!(literal.desc, ExpressionDesc::Null) {
        return None;
    }

    if matches!(type_name, "boolean" | "string" | "number" | "object")
        && is_scalar_nullish_literal(literal)
    {
        return Some(typeof_expr.clone());
    }

    None
}

fn simplify_array_is_array_and_literal_and(array_test: &Expression, other: &Expression) -> Option<Expression> {
    let vident = array_is_array_var(array_test)?;
    let (op, other_vident, literal) = strict_var_literal_comparison(other)?;
    if !same_vident(vident, other_vident) || !is_scalar_nullish_literal(literal) {
        return None;
    }

    match op {
        BinOp::EqEqEq => Some(Expression::bool(false)),
        BinOp::NotEqEq => Some(array_test.clone()),
        _ => None,
    }
}

fn simplify_same_var_literal_and(left: &Expression, right: &Expression) -> Option<Expression> {
    let (left_op, left_vident, left_literal) = strict_var_literal_comparison(left)?;
    let (right_op, right_vident, right_literal) = strict_var_literal_comparison(right)?;
    if !same_vident(left_vident, right_vident) {
        return None;
    }

    if left_op == right_op {
        if ocaml_eq_expression(left_literal, right_literal) {
            return Some(left.clone());
        }
        if matches!(left_op, BinOp::EqEqEq) {
            return Some(Expression::bool(false));
        }
        return None;
    }

    if ocaml_eq_expression(left_literal, right_literal) {
        return Some(Expression::bool(false));
    }

    if matches!(left_op, BinOp::EqEqEq) {
        return Some(left.clone());
    }

    Some(right.clone())
}

fn typeof_var_type_test(expr: &Expression) -> Option<(&VIdent, &str)> {
    let ExpressionDesc::Bin(BinOp::EqEqEq, left, right) = &expr.desc else {
        return None;
    };
    let ExpressionDesc::Typeof(value) = &left.desc else {
        return None;
    };
    let ExpressionDesc::Var(vident) = &value.desc else {
        return None;
    };
    let ExpressionDesc::Str { txt, .. } = &right.desc else {
        return None;
    };
    Some((vident, txt.as_str()))
}

fn strict_var_literal_comparison(expr: &Expression) -> Option<(BinOp, &VIdent, &Expression)> {
    let ExpressionDesc::Bin(op @ (BinOp::EqEqEq | BinOp::NotEqEq), left, right) = &expr.desc else {
        return None;
    };
    let ExpressionDesc::Var(vident) = &left.desc else {
        return None;
    };
    if !is_scalar_nullish_literal(right) {
        return None;
    }
    Some((*op, vident, right))
}

fn array_is_array_var(expr: &Expression) -> Option<&VIdent> {
    let ExpressionDesc::Call(func, args, _) = &expr.desc else {
        return None;
    };
    let ExpressionDesc::Str { txt, .. } = &func.desc else {
        return None;
    };
    if txt != "Array.isArray" {
        return None;
    }
    let [arg] = args.as_slice() else {
        return None;
    };
    let ExpressionDesc::Var(vident) = &arg.desc else {
        return None;
    };
    Some(vident)
}

fn literal_matches_type_name(literal: &Expression, type_name: &str) -> bool {
    matches!(
        (&literal.desc, type_name),
        (ExpressionDesc::Bool(_), "boolean")
            | (ExpressionDesc::Str { .. }, "string")
            | (ExpressionDesc::Number(_), "number")
    )
}

fn is_scalar_nullish_literal(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Bool(_)
            | ExpressionDesc::Null
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
    )
}

fn ocaml_eq_block(left: &Block, right: &Block) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left_stmt, right_stmt)| ocaml_eq_statement(left_stmt, right_stmt))
}

fn ocaml_eq_statement(left: &Statement, right: &Statement) -> bool {
    match (&left.desc, &right.desc) {
        (StatementDesc::Exp(left_expr), StatementDesc::Exp(right_expr))
        | (StatementDesc::Return(left_expr), StatementDesc::Return(right_expr)) => {
            ocaml_eq_expression(left_expr, right_expr)
        }
        (StatementDesc::Debugger, StatementDesc::Debugger)
        | (StatementDesc::Break, StatementDesc::Break) => true,
        (StatementDesc::Block(left_block), StatementDesc::Block(right_block)) => {
            ocaml_eq_block(left_block, right_block)
        }
        _ => false,
    }
}

fn ocaml_eq_expression(left: &Expression, right: &Expression) -> bool {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Null, ExpressionDesc::Null) => true,
        (
            ExpressionDesc::Undefined {
                is_unit: left_is_unit,
            },
            ExpressionDesc::Undefined {
                is_unit: right_is_unit,
            },
        ) => left_is_unit == right_is_unit,
        (
            ExpressionDesc::Number(Number::Int { i: left_int, .. }),
            ExpressionDesc::Number(Number::Int { i: right_int, .. }),
        ) => left_int == right_int,
        (
            ExpressionDesc::Number(Number::BigInt(left_bigint)),
            ExpressionDesc::Number(Number::BigInt(right_bigint)),
        ) => left_bigint == right_bigint,
        (ExpressionDesc::Number(Number::Float(_)), ExpressionDesc::Number(Number::Float(_))) => false,
        (ExpressionDesc::StringIndex(left_obj, left_index), ExpressionDesc::StringIndex(right_obj, right_index))
        | (ExpressionDesc::ArrayIndex(left_obj, left_index), ExpressionDesc::ArrayIndex(right_obj, right_index)) => {
            ocaml_eq_expression(left_obj, right_obj) && ocaml_eq_expression(left_index, right_index)
        }
        (ExpressionDesc::Call(left_fn, left_args, _), ExpressionDesc::Call(right_fn, right_args, _)) => {
            ocaml_eq_expression(left_fn, right_fn)
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left_arg, right_arg)| ocaml_eq_expression(left_arg, right_arg))
        }
        (ExpressionDesc::Var(left_vident), ExpressionDesc::Var(right_vident)) => {
            same_vident(left_vident, right_vident)
        }
        (ExpressionDesc::Bin(left_op, left_lhs, left_rhs), ExpressionDesc::Bin(right_op, right_lhs, right_rhs)) => {
            left_op == right_op
                && ocaml_eq_expression(left_lhs, right_lhs)
                && ocaml_eq_expression(left_rhs, right_rhs)
        }
        (
            ExpressionDesc::Str {
                delim: left_delim,
                txt: left_txt,
            },
            ExpressionDesc::Str {
                delim: right_delim,
                txt: right_txt,
            },
        ) => left_delim == right_delim && left_txt == right_txt,
        (
            ExpressionDesc::StaticIndex(left_obj, left_field, left_pos),
            ExpressionDesc::StaticIndex(right_obj, right_field, right_pos),
        ) => {
            left_field == right_field
                && left_pos == right_pos
                && ocaml_eq_expression(left_obj, right_obj)
        }
        (ExpressionDesc::Seq(left_first, left_second), ExpressionDesc::Seq(right_first, right_second)) => {
            ocaml_eq_expression(left_first, right_first)
                && ocaml_eq_expression(left_second, right_second)
        }
        (ExpressionDesc::Bool(left_bool), ExpressionDesc::Bool(right_bool)) => left_bool == right_bool,
        (
            ExpressionDesc::OptionalBlock(left_inner, left_identity),
            ExpressionDesc::OptionalBlock(right_inner, right_identity),
        ) => left_identity == right_identity && ocaml_eq_expression(left_inner, right_inner),
        (
            ExpressionDesc::CamlBlock(left_items, left_mutable, left_tag, _),
            ExpressionDesc::CamlBlock(right_items, right_mutable, right_tag, _),
        ) => {
            left_mutable == right_mutable
                && left_items.len() == right_items.len()
                && left_items
                    .iter()
                    .zip(right_items)
                    .all(|(left_item, right_item)| ocaml_eq_expression(left_item, right_item))
                && ocaml_eq_expression(left_tag, right_tag)
        }
        _ => false,
    }
}

fn same_vident(left: &VIdent, right: &VIdent) -> bool {
    match (left, right) {
        (VIdent::Id(left_id), VIdent::Id(right_id)) => left_id.same(right_id),
        (
            VIdent::Qualified(left_module, left_member),
            VIdent::Qualified(right_module, right_member),
        ) => {
            left_module.id.same(&right_module.id)
                && same_vident_kind(&left_module.kind, &right_module.kind)
                && left_member == right_member
        }
        _ => false,
    }
}

fn same_vident_kind(left: &Kind, right: &Kind) -> bool {
    match (left, right) {
        (Kind::Ml, Kind::Ml) | (Kind::Runtime, Kind::Runtime) => true,
        (Kind::External { name: left_name, .. }, Kind::External { name: right_name, .. }) => {
            left_name == right_name
        }
        _ => false,
    }
}

/// Block of statements
pub type Block = Vec<Statement>;

/// Exports from a module
pub type Exports = Vec<Ident>;

/// Required (imported) modules
pub type RequiredModules = Vec<ModuleId>;

/// JavaScript program
#[derive(Debug, Clone)]
pub struct Program {
    /// Program statements
    pub block: Block,
    /// Exported identifiers
    pub exports: Exports,
    /// Set of exported identifiers
    pub export_set: std::collections::HashSet<Ident>,
}

impl Program {
    /// Create a new program
    pub fn new(block: Block, exports: Exports) -> Self {
        let export_set = exports.iter().cloned().collect();
        Self {
            block,
            exports,
            export_set,
        }
    }

    /// Create an empty program
    pub fn empty() -> Self {
        Self {
            block: vec![],
            exports: vec![],
            export_set: std::collections::HashSet::new(),
        }
    }
}

/// Program with dependencies
#[derive(Debug, Clone)]
pub struct DepsProgram {
    /// The program
    pub program: Program,
    /// Required modules
    pub modules: RequiredModules,
    /// Side effect reason (None = no side effects)
    pub side_effect: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_expression_creation() {
        let expr = Expression::bool(true);
        match expr.desc {
            ExpressionDesc::Bool(true) => {}
            _ => panic!("Expected Bool(true)"),
        }
    }

    #[test]
    fn test_variable_expression() {
        let id = Ident::create_local("x");
        let expr = Expression::var(id.clone());
        match &expr.desc {
            ExpressionDesc::Var(VIdent::Id(i)) => {
                assert_eq!(i.name(), "x");
            }
            _ => panic!("Expected Var(Id)"),
        }
    }

    #[test]
    fn test_string_expression() {
        let expr = Expression::string("hello");
        match &expr.desc {
            ExpressionDesc::Str {
                delim: Delim::None,
                txt,
            } => {
                assert_eq!(txt, "hello");
            }
            _ => panic!("Expected Str"),
        }
    }

    #[test]
    fn test_binary_expression() {
        let left = Expression::number(Number::int(1));
        let right = Expression::number(Number::int(2));
        let expr = Expression::bin(BinOp::Plus, left, right);

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Plus, _, _) => {}
            _ => panic!("Expected Bin(Plus)"),
        }
    }

    #[test]
    fn test_plus_with_negative_int_rhs_rewrites_to_minus() {
        let left = Expression::var(Ident::create_local("x"));
        let right = Expression::number(Number::int(-1));
        let expr = Expression::bin(BinOp::Plus, left, right);

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Minus, left, right) => {
                assert!(matches!(left.as_ref().desc, ExpressionDesc::Var(_)));
                assert!(matches!(
                    right.as_ref().desc,
                    ExpressionDesc::Number(Number::Int { i: 1, .. })
                ));
            }
            other => panic!("Expected Bin(Minus, _, 1), got {other:?}"),
        }
    }

    #[test]
    fn test_strict_eq_null_against_number_folds_false() {
        let expr = Expression::bin(
            BinOp::EqEqEq,
            Expression::null(),
            Expression::number(Number::int(5)),
        );

        assert!(matches!(expr.desc, ExpressionDesc::Bool(false)));
    }

    #[test]
    fn test_strict_neq_undefined_against_number_folds_true() {
        let expr = Expression::bin(
            BinOp::NotEqEq,
            Expression::undefined(false),
            Expression::number(Number::int(5)),
        );

        assert!(matches!(expr.desc, ExpressionDesc::Bool(true)));
    }

    #[test]
    fn test_strict_eq_int_literals_folds_true() {
        let expr = Expression::bin(
            BinOp::EqEqEq,
            Expression::number(Number::int(2)),
            Expression::number(Number::int(2)),
        );

        assert!(matches!(expr.desc, ExpressionDesc::Bool(true)));
    }

    #[test]
    fn test_strict_eq_optional_blocks_compares_inner_values() {
        let expr = Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::OptionalBlock(
                Box::new(Expression::number(Number::int(1))),
                true,
            )),
            Expression::new(ExpressionDesc::OptionalBlock(
                Box::new(Expression::number(Number::int(1))),
                true,
            )),
        );

        assert!(matches!(expr.desc, ExpressionDesc::Bool(true)));
    }

    #[test]
    fn test_strict_eq_simple_string_literals_fold_false() {
        let expr = Expression::bin(
            BinOp::EqEqEq,
            Expression::string("A"),
            Expression::string("B"),
        );

        assert!(matches!(expr.desc, ExpressionDesc::Bool(false)));
    }

    #[test]
    fn test_strict_eq_null_against_variable_is_preserved() {
        let expr = Expression::bin(
            BinOp::EqEqEq,
            Expression::null(),
            Expression::var(Ident::create_local("value")),
        );

        assert!(matches!(
            expr.desc,
            ExpressionDesc::Bin(BinOp::EqEqEq, _, _)
        ));
    }

    #[test]
    fn test_not_simplifies_equality_negation() {
        let expr = Expression::not(Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::null(),
        ));

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::NotEqEq, _, _) => {}
            other => panic!("Expected !== after negating ===, got {other:?}"),
        }
    }

    #[test]
    fn test_not_pushes_negation_through_and() {
        let left = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(1)),
        );
        let right = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("y")),
            Expression::number(Number::int(2)),
        );
        let expr = Expression::not(Expression::bin(BinOp::And, left, right));

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Or, left, right) => {
                assert!(matches!(
                    left.desc,
                    ExpressionDesc::Bin(BinOp::NotEqEq, _, _)
                ));
                assert!(matches!(
                    right.desc,
                    ExpressionDesc::Bin(BinOp::NotEqEq, _, _)
                ));
            }
            other => panic!("Expected De Morgan rewrite after negating &&, got {other:?}"),
        }
    }

    #[test]
    fn test_cond_true_simplifies_to_consequent() {
        let expr = Expression::cond(
            Expression::bool(true),
            Expression::number(Number::int(1)),
            Expression::number(Number::int(2)),
        );

        assert!(matches!(
            expr.desc,
            ExpressionDesc::Number(Number::Int { i: 1, .. })
        ));
    }

    #[test]
    fn test_cond_negated_test_swaps_non_empty_branches() {
        let value = Ident::create_local("value");
        let expr = Expression::cond(
            Expression::new(ExpressionDesc::JsNot(Box::new(Expression::var(
                value.clone(),
            )))),
            Expression::number(Number::int(1)),
            Expression::number(Number::int(2)),
        );

        match expr.desc {
            ExpressionDesc::Cond(test, consequent, alternate) => {
                assert!(matches!(
                    test.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
                assert!(matches!(
                    consequent.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }
                ));
                assert!(matches!(
                    alternate.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }
                ));
            }
            other => panic!("Expected negated condition to be swapped, got {other:?}"),
        }
    }

    #[test]
    fn test_statement_creation() {
        let stmt = Statement::break_();
        match stmt.desc {
            StatementDesc::Break => {}
            _ => panic!("Expected Break"),
        }
    }

    #[test]
    fn resolve_local_module_fallback_path_uses_sibling_source_file() {
        let project = tempdir().expect("failed to create tempdir");
        let source_dir = project.path().join("src");
        std::fs::create_dir_all(&source_dir).expect("failed to create source dir");

        let current_source = source_dir.join("include_side_effect.res");
        let target_source = source_dir.join("side_effect.res");
        std::fs::write(&current_source, "").expect("failed to write current source");
        std::fs::write(&target_source, "").expect("failed to write target source");

        let resolver = ModulePathResolver::from_compile_options(
            Some(current_source.to_str().expect("utf8 current source")),
            Some(source_dir.join("include_side_effect.mjs").as_path()),
            None,
            None,
        );
        let module = ModuleId {
            id: Ident::create_local("Side_effect"),
            kind: Kind::Ml,
            dynamic_import: false,
        };

        assert_eq!(
            resolver
                .resolve_local_module_fallback_path(module.id.name())
                .as_deref(),
            Some("./side_effect.mjs")
        );
    }

    #[test]
    fn test_if_statement() {
        let cond = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(1)),
        );
        let then_ = vec![Statement::exp(Expression::number(Number::int(10)))];
        let else_ = vec![Statement::return_(Expression::number(Number::int(20)))];
        let stmt = Statement::if_(cond, then_, else_);

        match &stmt.desc {
            StatementDesc::Block(block) => {
                let [guard, fallthrough] = block.as_slice() else {
                    panic!("Expected a guard if and a fallthrough statement");
                };
                match &guard.desc {
                    StatementDesc::If(guard_cond, then_block, else_block) => {
                        match &guard_cond.desc {
                            ExpressionDesc::Bin(BinOp::NotEqEq, _, _) => {}
                            _ => panic!("Expected a negated equality guard"),
                        }
                        assert!(matches!(
                            then_block.as_slice(),
                            [Statement {
                                desc: StatementDesc::Return(_),
                                ..
                            }]
                        ));
                        assert!(else_block.is_empty());
                    }
                    _ => panic!("Expected guard if"),
                }
                assert!(matches!(fallthrough.desc, StatementDesc::Exp(_)));
            }
            _ => panic!("Expected simplified guard block"),
        }
    }

    #[test]
    fn test_if_statement_merges_two_returns_into_a_conditional_return() {
        let stmt = Statement::if_(
            Expression::var(Ident::create_local("cond")),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::return_(Expression::number(Number::int(2)))],
        );

        match &stmt.desc {
            StatementDesc::Return(expr) => match &expr.desc {
                ExpressionDesc::Cond(_, consequent, alternate) => {
                    assert!(matches!(consequent.desc, ExpressionDesc::Number(_)));
                    assert!(matches!(alternate.desc, ExpressionDesc::Number(_)));
                }
                _ => panic!("Expected a conditional return expression"),
            },
            _ => panic!("Expected a single return statement"),
        }
    }

    #[test]
    fn test_if_statement_merges_matching_assignments_into_a_conditional_assignment() {
        let target = Ident::create_local("result");
        let stmt = Statement::if_(
            Expression::var(Ident::create_local("cond")),
            vec![Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target.clone()),
                Expression::number(Number::int(1)),
            ))],
            vec![Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target.clone()),
                Expression::number(Number::int(2)),
            ))],
        );

        match &stmt.desc {
            StatementDesc::Exp(expr) => match &expr.desc {
                ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) => {
                    assert!(matches!(lhs.desc, ExpressionDesc::Var(_)));
                    assert!(matches!(rhs.desc, ExpressionDesc::Cond(_, _, _)));
                }
                _ => panic!("Expected a merged assignment"),
            },
            _ => panic!("Expected a single assignment expression"),
        }
    }

    #[test]
    fn test_if_statement_merges_nested_then_if_with_shared_else_into_and_condition() {
        let outer = Ident::create_local("outer");
        let inner = Ident::create_local("inner");
        let stmt = Statement::if_(
            Expression::var(outer.clone()),
            vec![Statement::new(StatementDesc::If(
                Expression::var(inner.clone()),
                vec![Statement::exp(Expression::number(Number::int(1)))],
                vec![Statement::exp(Expression::number(Number::int(0)))],
            ))],
            vec![Statement::exp(Expression::number(Number::int(0)))],
        );

        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Cond(test, consequent, alternate),
            ..
        }) = &stmt.desc
        else {
            panic!("expected the nested then-if to collapse into one conditional expression");
        };

        assert!(matches!(
            test.as_ref(),
            Expression {
                desc: ExpressionDesc::Bin(BinOp::And, left, right),
                ..
            } if matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&outer)
            ) && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&inner)
            )
        ));
        assert!(matches!(
            consequent.as_ref().desc,
            ExpressionDesc::Number(Number::Int { i: 1, .. })
        ));
        assert!(matches!(
            alternate.as_ref().desc,
            ExpressionDesc::Number(Number::Int { i: 0, .. })
        ));
    }

    #[test]
    fn test_if_statement_merges_nested_else_if_with_shared_then_into_or_condition() {
        let outer = Ident::create_local("outer");
        let inner = Ident::create_local("inner");
        let stmt = Statement::if_(
            Expression::var(outer.clone()),
            vec![Statement::exp(Expression::number(Number::int(1)))],
            vec![Statement::new(StatementDesc::If(
                Expression::var(inner.clone()),
                vec![Statement::exp(Expression::number(Number::int(1)))],
                vec![Statement::exp(Expression::number(Number::int(0)))],
            ))],
        );

        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Cond(test, consequent, alternate),
            ..
        }) = &stmt.desc
        else {
            panic!("expected the nested else-if to collapse into one conditional expression");
        };

        assert!(matches!(
            test.as_ref(),
            Expression {
                desc: ExpressionDesc::Bin(BinOp::Or, left, right),
                ..
            } if matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&outer)
            ) && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&inner)
            )
        ));
        assert!(matches!(
            consequent.as_ref().desc,
            ExpressionDesc::Number(Number::Int { i: 1, .. })
        ));
        assert!(matches!(
            alternate.as_ref().desc,
            ExpressionDesc::Number(Number::Int { i: 0, .. })
        ));
    }

    #[test]
    fn test_js_and_simplifies_boolean_typeof_nullish_guards_like_ocaml() {
        let value = Ident::create_local("value");
        let typeof_boolean = Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                value.clone(),
            )))),
            Expression::string("boolean"),
        );

        let equals_null = Expression::bin(BinOp::EqEqEq, Expression::var(value.clone()), Expression::null());
        let not_equals_null =
            Expression::bin(BinOp::NotEqEq, Expression::var(value.clone()), Expression::null());
        let equals_undefined = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(value.clone()),
            Expression::undefined(false),
        );
        let not_equals_undefined = Expression::bin(
            BinOp::NotEqEq,
            Expression::var(value.clone()),
            Expression::undefined(false),
        );

        assert!(matches!(
            js_and_expression(typeof_boolean.clone(), equals_null).desc,
            ExpressionDesc::Bool(false)
        ));
        assert!(matches!(
            js_and_expression(typeof_boolean.clone(), not_equals_null).desc,
            ExpressionDesc::Bin(BinOp::EqEqEq, _, _)
        ));
        assert!(matches!(
            js_and_expression(typeof_boolean.clone(), equals_undefined).desc,
            ExpressionDesc::Bool(false)
        ));
        assert!(matches!(
            js_and_expression(typeof_boolean, not_equals_undefined).desc,
            ExpressionDesc::Bin(BinOp::EqEqEq, _, _)
        ));
    }

    #[test]
    fn test_cond_merges_nested_alternate_to_drop_impossible_boolean_null_checks() {
        let value = Ident::create_local("value");
        let typeof_boolean = Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                value.clone(),
            )))),
            Expression::string("boolean"),
        );
        let nested = Expression::cond(
            Expression::bin(BinOp::EqEqEq, Expression::var(value), Expression::null()),
            Expression::number(Number::int(3)),
            Expression::number(Number::int(4)),
        );

        let merged = Expression::cond(typeof_boolean, nested, Expression::number(Number::int(4)));
        assert!(matches!(
            merged.desc,
            ExpressionDesc::Number(Number::Int { i: 4, .. })
        ));
    }

    #[test]
    fn test_cond_merges_nested_alternate_to_keep_only_boolean_typeof_guard() {
        let value = Ident::create_local("value");
        let typeof_boolean = Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                value.clone(),
            )))),
            Expression::string("boolean"),
        );
        let nested = Expression::cond(
            Expression::bin(BinOp::NotEqEq, Expression::var(value), Expression::null()),
            Expression::number(Number::int(3)),
            Expression::number(Number::int(4)),
        );

        let merged = Expression::cond(typeof_boolean, nested, Expression::number(Number::int(4)));
        assert!(
            matches!(
                &merged,
                Expression {
                    desc: ExpressionDesc::Cond(_, consequent, alternate),
                    ..
                } if !matches!(consequent.as_ref().desc, ExpressionDesc::Cond(_, _, _))
                    && matches!(
                        consequent.as_ref().desc,
                        ExpressionDesc::Number(Number::Int { i: 3, .. })
                    )
                    && matches!(
                        alternate.as_ref().desc,
                        ExpressionDesc::Number(Number::Int { i: 4, .. })
                    )
            ),
            "expected the nested conditional to collapse to a single outer guard, got {merged:?}"
        );
    }

    #[test]
    fn test_program_creation() {
        let stmt = Statement::return_(Expression::undefined(true));
        let program = Program::new(vec![stmt], vec![]);

        assert_eq!(program.block.len(), 1);
        assert!(program.exports.is_empty());
    }
}
