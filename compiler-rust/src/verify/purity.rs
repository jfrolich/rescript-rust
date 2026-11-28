//! Checks `@pure` and `@mutates` (docs/verify/pure.md).
//!
//! A binding marked `@pure` promises that evaluating it, and calling any
//! function in it, reads nothing that can change and changes nothing the
//! caller can see. The check walks the typed tree of the binding:
//!
//! - a value from outside the binding must itself be `@pure`, a primitive
//!   without effects, or immutable data;
//! - a change (a field assignment, a call to a `@mutates` function) must be to
//!   a value the binding created itself and bound with `let`;
//! - a function that changes such a value must not outlive the call that
//!   created it.
//!
//! Functions of the same file that carry no annotation are looked into the
//! first time a pure binding uses them, so only what crosses a file needs an
//! annotation.
//!
//! Cost: nothing for a file without `@pure` or `@mutates` (the parser records
//! whether it saw one). Otherwise one walk of the typed tree to index its
//! bindings, and one walk of each checked binding.

use std::collections::{HashMap, HashSet};

use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::types::asttypes::MutableFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{
    Attribute, ConstructorArguments, PrimKind, TypeKind, ValueDescription, ValueKind,
};
use crate::types::external_ffi_types::{DeclKind, ExternalFfi};
use crate::types::path::PathView;
use crate::types::tast_iterator::{self as ti, TastIterator};
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree::*;
use crate::types::{Env, Path, TypeExprRef};

/// The attribute that marks a binding or declaration as pure.
pub const PURE: &str = "pure";
/// The attribute that marks a function that changes its first argument and
/// does nothing else.
pub const MUTATES: &str = "mutates";

/// Whether an attribute name declares an effect.
pub fn is_effect_attribute(name: &str) -> bool {
    name == PURE || name == MUTATES
}

/// One violation.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Where the violation is.
    pub loc: Location,
    /// The report text.
    pub message: String,
}

/// A signature declares an effect for a value, and the value matched
/// against it does not declare the same one. The check discharges it on the
/// value's binding.
#[derive(Debug, Clone, Copy)]
pub struct Obligation {
    /// The identifier of the value matched against the signature.
    pub stamp: i32,
    /// Its name.
    pub name: &'static str,
    /// What the signature declares.
    pub declared: Declared,
    /// Where the signature declares it.
    pub signature_loc: crate::types::DeclLoc,
    /// The type of the value matched against the signature.
    pub ty: TypeExprRef,
}

/// What a declaration states about its effects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Declared {
    /// `@pure`.
    Pure,
    /// `@mutates`.
    Mutates,
}

impl Declared {
    /// The attribute as it is written.
    pub fn marker(self) -> &'static str {
        match self {
            Declared::Pure => "@pure",
            Declared::Mutates => "@mutates",
        }
    }
}

/// The effect annotation among a declaration's attributes, as they are kept
/// in signatures.
pub fn declared_of_decl_attributes(attributes: &[Attribute]) -> Option<Declared> {
    attributes
        .iter()
        .find_map(|attribute| match attribute.attr_name.txt.as_str() {
            PURE => Some(Declared::Pure),
            MUTATES => Some(Declared::Mutates),
            _ => None,
        })
}

/// The effect annotation among a binding's attributes, as the parser left
/// them.
pub fn declared_of_attributes(arena: &ParseArena, attributes: &Attributes) -> Option<Declared> {
    effect_attribute(arena, attributes).map(|(declared, _)| declared)
}

/// What an effect attribute's payload asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Payload {
    /// No payload: the binding is checked.
    Checked,
    /// `@pure(unchecked)`: the compiler takes the author's word.
    Unchecked,
    /// Anything else.
    Unknown,
}

fn effect_attribute(arena: &ParseArena, attributes: &Attributes) -> Option<(Declared, Payload)> {
    use crate::parser::ast::{
        ExpressionDesc as Parsed, Payload as Written, StructureItemDesc as Item,
    };
    use crate::parser::longident::Longident;
    attributes.iter().find_map(|(name, payload)| {
        let declared = match arena.get_string(name.txt) {
            PURE => Declared::Pure,
            MUTATES => Declared::Mutates,
            _ => return None,
        };
        let payload = match payload {
            Written::PStr(items) if items.is_empty() => Payload::Checked,
            Written::PStr(items) if items.len() == 1 => match &items[0].pstr_desc {
                Item::Pstr_eval(eval) => match &arena.get_expr(eval.0).pexp_desc {
                    Parsed::Pexp_ident(lid) => match arena.get_longident(lid.txt) {
                        Longident::Lident(word) if arena.get_string(*word) == "unchecked" => {
                            Payload::Unchecked
                        }
                        _ => Payload::Unknown,
                    },
                    _ => Payload::Unknown,
                },
                _ => Payload::Unknown,
            },
            _ => Payload::Unknown,
        };
        Some((declared, payload))
    })
}

/// A `let` of the file that binds one name.
#[derive(Debug, Clone, Copy)]
struct Binding {
    expr: TExprIdx,
    loc: LocIdx,
    declared: Option<Declared>,
    /// What the attribute's payload says, when the binding has one.
    payload: Payload,
    /// Why the binding is checked when nothing declares it: a law or a spec
    /// is pure by definition (set by the callers that know those).
    name: &'static str,
}

/// The names a module of the file defines, for values reached by a path.
#[derive(Debug, Default)]
struct Scope {
    values: HashMap<&'static str, i32>,
    modules: HashMap<&'static str, i32>,
}

/// Every single-name `let` of the file by identifier, and its modules.
#[derive(Default)]
pub(super) struct Index {
    bindings: HashMap<i32, Binding>,
    /// Bindings with an annotation, in source order.
    annotated: Vec<i32>,
    modules: HashMap<i32, Scope>,
}

impl Index {
    /// The expression and the name of a binding.
    pub(super) fn definition(&self, stamp: i32) -> Option<(TExprIdx, &'static str)> {
        self.bindings.get(&stamp).map(|binding| (binding.expr, binding.name))
    }

    /// The binding a path of this file names, if it is one the index knows.
    pub(super) fn resolve(&self, path: &Path) -> Option<i32> {
        match path.view() {
            PathView::Pident(id) => self.bindings.contains_key(&id.stamp()).then(|| id.stamp()),
            PathView::Pdot(parent, name, _) => {
                let scope = self.modules.get(&self.resolve_module(parent)?)?;
                scope.values.get(name.as_str()).copied()
            }
            PathView::Papply(..) => None,
        }
    }

    fn resolve_module(&self, path: &Path) -> Option<i32> {
        match path.view() {
            PathView::Pident(id) => self.modules.contains_key(&id.stamp()).then(|| id.stamp()),
            PathView::Pdot(parent, name, _) => {
                let scope = self.modules.get(&self.resolve_module(parent)?)?;
                scope.modules.get(name.as_str()).copied()
            }
            PathView::Papply(..) => None,
        }
    }
}

struct Indexer<'a> {
    ta: &'a TypedArena,
    arena: &'a ParseArena,
    index: Index,
    /// Extra roots: bindings that are pure without saying so.
    implied: &'a dyn Fn(&Attributes) -> bool,
}

/// The identifier a pattern binds when it binds exactly one name.
fn bound_name(ta: &TypedArena, pat: TPatIdx) -> Option<&crate::ident::Ident> {
    match &ta.pattern(pat).pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id),
        PatternDesc::Tpat_alias(inner, id, _) => {
            matches!(ta.pattern(*inner).pat_desc, PatternDesc::Tpat_any).then_some(id)
        }
        _ => None,
    }
}

impl<'a> Indexer<'a> {
    fn scope_of(&self, structure: &Structure) -> Scope {
        let mut scope = Scope::default();
        for item in self.ta.structure_items(structure.str_items) {
            match &item.str_desc {
                StructureItemDesc::Tstr_value(_, bindings) => {
                    for binding in self.ta.value_bindings(*bindings) {
                        if let Some(id) = bound_name(self.ta, binding.vb_pat) {
                            scope.values.insert(id.name(), id.stamp());
                        }
                    }
                }
                StructureItemDesc::Tstr_module(binding) => {
                    scope
                        .modules
                        .insert(binding.mb_id.name(), binding.mb_id.stamp());
                }
                StructureItemDesc::Tstr_recmodule(bindings) => {
                    for binding in bindings {
                        scope
                            .modules
                            .insert(binding.mb_id.name(), binding.mb_id.stamp());
                    }
                }
                _ => {}
            }
        }
        scope
    }

    /// The structure a module expression is, behind constraints.
    fn structure_of(&self, mut module: &'a ModuleExpr) -> Option<&'a Structure> {
        loop {
            match &module.mod_desc {
                ModuleExprDesc::Tmod_structure(structure) => return Some(structure),
                ModuleExprDesc::Tmod_constraint(inner, ..) => module = self.ta.module_expr(*inner),
                _ => return None,
            }
        }
    }
}

impl<'a> TastIterator<'a> for Indexer<'a> {
    fn arena(&self) -> &'a TypedArena {
        self.ta
    }

    fn value_binding(&mut self, binding: &ValueBinding) {
        if let Some(id) = bound_name(self.ta, binding.vb_pat) {
            let written = effect_attribute(self.arena, &binding.vb_attributes);
            let declared = written
                .map(|(declared, _)| declared)
                .or_else(|| (self.implied)(&binding.vb_attributes).then_some(Declared::Pure));
            self.index.bindings.insert(
                id.stamp(),
                Binding {
                    expr: binding.vb_expr,
                    loc: binding.vb_loc,
                    declared,
                    payload: written.map_or(Payload::Checked, |(_, payload)| payload),
                    name: id.name(),
                },
            );
            if declared.is_some() {
                self.index.annotated.push(id.stamp());
            }
        }
        self.pat(self.ta.pattern(binding.vb_pat));
        self.expr(self.ta.expr(binding.vb_expr));
    }

    fn module_binding(&mut self, binding: &ModuleBinding) {
        let module = self.ta.module_expr(binding.mb_expr);
        if let Some(structure) = self.structure_of(module) {
            let scope = self.scope_of(structure);
            self.index.modules.insert(binding.mb_id.stamp(), scope);
        }
        ti::walk_module_expr(self, module);
    }
}

/// What a use of a compiler intrinsic does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Intrinsic {
    Pure,
    /// Returns a new mutable value.
    Fresh,
    /// Changes its first argument.
    Mutates,
    Impure,
}

fn intrinsic(name: &str) -> Intrinsic {
    match name {
        "%makeref" | "%makedict" | "%makemutablelist" | "#makemutablelist" => Intrinsic::Fresh,
        "%refset" | "%array_unsafe_set" | "%array_safe_set" | "%obj_set_field" | "%setfield" => {
            Intrinsic::Mutates
        }
        // Scheduling, loading code and stopping in a debugger are effects.
        // `%raw` runs JavaScript the checker cannot see.
        "%await" | "%import" | "#import" | "%debugger" | RAW_EXPR | "#raw_stmt" => {
            Intrinsic::Impure
        }
        _ => Intrinsic::Pure,
    }
}

/// The primitive `%raw(...)` in an expression applies.
const RAW_EXPR: &str = "#raw_expr";

/// The state of a binding the checker looks into.
#[derive(Debug, Clone)]
enum Known {
    /// Being checked: a recursive use counts as pure.
    InProgress,
    Pure,
    /// The first violation found in it.
    Impure(Location, String),
}

/// A function the walk is inside.
#[derive(Debug, Clone, Copy)]
struct Frame {
    /// The function is an argument written at a call whose result cannot
    /// hold it, so it does not outlive the call.
    consumed: bool,
    /// The `let` that names the function, if one does.
    bound: Option<i32>,
    /// The function changes a value created outside it.
    stateful: bool,
}

/// How an identifier is used where it is written.
#[derive(Clone, Copy)]
enum Use {
    /// As a value.
    Value,
    /// As the function of a call, with the call's first argument.
    Callee(Option<TExprIdx>),
    /// As an argument of a call that does not keep it.
    Consumed,
}

struct Shared<'a> {
    ctx: &'a TypeContext,
    ta: &'a TypedArena,
    arena: &'a ParseArena,
    index: Index,
    known: HashMap<i32, Known>,
    /// Whether a function of the file returns a value it made itself.
    fresh: HashMap<i32, bool>,
}

struct Checker<'a, 's> {
    shared: &'s mut Shared<'a>,
    /// The binding being checked, for messages.
    root: &'static str,
    root_declared: Declared,
    /// Identifiers bound inside the binding.
    locals: HashSet<i32>,
    /// Values the binding created, with the depth of the function that did.
    owned: HashMap<i32, usize>,
    /// Functions bound inside the binding that change a value created
    /// outside them, with the depth they were bound at.
    stateful: HashMap<i32, usize>,
    frames: Vec<Frame>,
    diagnostics: Vec<Diagnostic>,
    /// Stop at the first violation (when looking into an unannotated
    /// binding).
    first_only: bool,
}

/// Collects the identifiers bound inside an expression.
struct Locals<'a> {
    ta: &'a TypedArena,
    bound: HashSet<i32>,
}

impl<'a> TastIterator<'a> for Locals<'a> {
    fn arena(&self) -> &'a TypedArena {
        self.ta
    }

    fn pat(&mut self, p: &Pattern) {
        match &p.pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                self.bound.insert(id.stamp());
            }
            PatternDesc::Tpat_record(_, _, Some(rest)) => {
                self.bound.insert(rest.rest_ident.stamp());
            }
            _ => {}
        }
        ti::walk_pat(self, p);
    }

    fn expr(&mut self, e: &Expression) {
        match &e.exp_desc {
            ExpressionDesc::Texp_function { params, .. } => {
                for param in self.ta.function_params(*params) {
                    self.bound.insert(param.fp_param.stamp());
                }
            }
            ExpressionDesc::Texp_for(id, ..)
            | ExpressionDesc::Texp_for_of(id, ..)
            | ExpressionDesc::Texp_for_await_of(id, ..) => {
                self.bound.insert(id.stamp());
            }
            _ => {}
        }
        ti::walk_expr(self, e);
    }
}

impl<'a, 's> Checker<'a, 's> {
    fn new(
        shared: &'s mut Shared<'a>,
        root: &'static str,
        declared: Declared,
        first_only: bool,
    ) -> Self {
        Checker {
            shared,
            root,
            root_declared: declared,
            locals: HashSet::new(),
            owned: HashMap::new(),
            stateful: HashMap::new(),
            frames: vec![Frame {
                consumed: false,
                bound: None,
                stateful: false,
            }],
            diagnostics: Vec::new(),
            first_only,
        }
    }

    fn done(&self) -> bool {
        self.first_only && !self.diagnostics.is_empty()
    }

    fn report(&mut self, loc: LocIdx, message: String) {
        if !self.done() {
            self.diagnostics.push(Diagnostic {
                loc: self.shared.arena.to_location(loc),
                message,
            });
        }
    }

    fn depth(&self) -> usize {
        self.frames.len() - 1
    }

    /// `@pure` or `@mutates`, as the binding being checked is declared.
    fn marker(&self) -> &'static str {
        self.root_declared.marker()
    }

    fn run(&mut self, expr: TExprIdx) {
        let ta = self.shared.ta;
        let mut locals = Locals {
            ta,
            bound: HashSet::new(),
        };
        locals.expr(ta.expr(expr));
        self.locals = locals.bound;
        let root = ta.expr(expr);
        if self.root_declared == Declared::Mutates {
            // The first parameter is the value a `@mutates` function may
            // change.
            if let ExpressionDesc::Texp_function { params, .. } = &root.exp_desc {
                if let Some(first) = ta.function_params(*params).first() {
                    // The function's own frame is at depth 1.
                    self.owned.insert(first.fp_param.stamp(), 1);
                    if let Some(id) = bound_name(ta, first.fp_pat) {
                        self.owned.insert(id.stamp(), 1);
                    }
                }
            }
        }
        self.expr_at(expr, Use::Value);
    }

    /// A change, written inside the current function, to a value created at
    /// `owner_depth`: every function between the two must be one that does
    /// not outlive the value.
    fn change_from(&mut self, owner_depth: usize, loc: LocIdx, what: &str) {
        for depth in (owner_depth + 1)..self.frames.len() {
            let frame = &mut self.frames[depth];
            if frame.consumed {
                continue;
            }
            if frame.bound.is_some() {
                frame.stateful = true;
                continue;
            }
            self.report(
                loc,
                format!(
                    "This function changes {what}, which was created outside it, and the function is used as a value: it could be called after `{}` has returned.\n\n\
                     Pass the function directly to the call that uses it, or bind it with `let` and only call it.",
                    self.root
                ),
            );
            return;
        }
    }

    /// The target of a change must be a value this binding created.
    fn change(&mut self, target: TExprIdx, loc: LocIdx) {
        let ta = self.shared.ta;
        let target = ta.expr(target);
        if let ExpressionDesc::Texp_ident(path, _, _) = &target.exp_desc {
            if let PathView::Pident(id) = path.view() {
                if let Some(depth) = self.owned.get(&id.stamp()).copied() {
                    let what = format!("`{}`", id.name());
                    self.change_from(depth, loc, &what);
                    return;
                }
                let name = id.name();
                let origin = if self.locals.contains(&id.stamp()) {
                    format!("`{}` did not create it", self.root)
                } else {
                    "it is defined outside this function".to_string()
                };
                self.report(
                    loc,
                    format!(
                        "This changes `{name}`, and {origin}.\n\n\
                         `{}` is {}, so it can only change values it creates itself: a `let` bound to a literal (`[]`, `{{...}}`, `dict{{}}`), to `ref(...)`, or to a call of a @pure external that returns a new value.",
                        self.root,
                        self.marker()
                    ),
                );
                return;
            }
        }
        self.report(
            loc,
            format!(
                "This changes a value that `{}` did not create itself.\n\n\
                 `{}` is {}, so it can only change values it creates and binds with `let`. A part of another value (a field, an element) may be shared with the caller.",
                self.root,
                self.root,
                self.marker()
            ),
        );
    }

    /// A use of a function bound in this binding that changes a value
    /// created outside itself.
    fn stateful_use(
        &mut self,
        id: &crate::ident::Ident,
        bound_depth: usize,
        usage: Use,
        loc: LocIdx,
    ) {
        match usage {
            Use::Callee(_) | Use::Consumed => {
                let what = format!("values `{}` changes", id.name());
                self.change_from(bound_depth, loc, &what);
            }
            Use::Value => self.report(
                loc,
                format!(
                    "`{}` changes a value created outside it, so it can only be called or passed directly to a call here. Used as a value it could be called after `{}` has returned.",
                    id.name(),
                    self.root
                ),
            ),
        }
    }

    fn env_of(&self, e: &Expression) -> Option<std::rc::Rc<Env>> {
        self.shared.ctx.get_typed_env(e.exp_env)
    }

    fn reference(
        &mut self,
        e: &Expression,
        path: &Path,
        name: &str,
        vd: &ValueDescription,
        usage: Use,
    ) {
        if let PathView::Pident(id) = path.view() {
            if self.locals.contains(&id.stamp()) {
                if let Some(depth) = self.stateful.get(&id.stamp()).copied() {
                    self.stateful_use(id, depth, usage, e.exp_loc);
                }
                return;
            }
        }
        match &vd.val_kind {
            ValueKind::ValPrim(prim) => match &prim.prim_kind {
                PrimKind::KindIntrinsic => match intrinsic(&prim.prim_name) {
                    Intrinsic::Pure | Intrinsic::Fresh => {}
                    Intrinsic::Mutates => self.mutator(e, name, usage),
                    Intrinsic::Impure if prim.prim_name == RAW_EXPR => self.report(
                        e.exp_loc,
                        format!(
                            "%raw is JavaScript, which the compiler cannot check, and `{}` is {}.\n\n\
                             Bind the JavaScript with `let name = %raw(...)` and mark that binding @pure if it has no side effects.",
                            self.root,
                            self.marker()
                        ),
                    ),
                    Intrinsic::Impure => self.report(
                        e.exp_loc,
                        format!(
                            "`{name}` has an effect, and `{}` is {}.",
                            self.root,
                            self.marker()
                        ),
                    ),
                },
                PrimKind::KindInlineConst(_) => {}
                PrimKind::KindExternal(_) => match declared_of_decl_attributes(&vd.val_attributes) {
                    Some(Declared::Pure) => {}
                    Some(Declared::Mutates) => self.mutator(e, name, usage),
                    None => self.report(
                        e.exp_loc,
                        format!(
                            "The external `{name}` is not marked @pure, and `{}` is {}.\n\n\
                             The compiler cannot see what JavaScript does, so an external has an effect unless its declaration says otherwise. If `{name}` is your binding and it only computes a result from its arguments, mark its declaration with @pure.",
                            self.root,
                            self.marker()
                        ),
                    ),
                },
            },
            ValueKind::ValReg => {
                let binding = self.shared.index.resolve(path);
                let declared = declared_of_decl_attributes(&vd.val_attributes)
                    .or_else(|| binding.and_then(|stamp| self.shared.index.bindings[&stamp].declared));
                match declared {
                    Some(Declared::Pure) => {}
                    Some(Declared::Mutates) => self.mutator(e, name, usage),
                    None => self.undeclared(e, name, binding),
                }
            }
        }
    }

    /// A use of a function that changes its first argument.
    fn mutator(&mut self, e: &Expression, name: &str, usage: Use) {
        match usage {
            Use::Callee(Some(first)) => self.change(first, e.exp_loc),
            _ => self.report(
                e.exp_loc,
                format!(
                    "`{name}` changes its first argument, so `{}` can only call it directly, on a value it created itself. Here it is used as a value.",
                    self.root
                ),
            ),
        }
    }

    /// A value from outside the binding that declares nothing.
    fn undeclared(&mut self, e: &Expression, name: &str, binding: Option<i32>) {
        let env = self.env_of(e);
        let ctx = self.shared.ctx;
        let shape = Shape::of(ctx, env.as_deref(), e.exp_type);
        if shape == Shape::Data {
            // A constant: nothing can change it.
            return;
        }
        if let Some(stamp) = binding {
            if shape == Shape::Functions {
                // A function of this file: look into it.
                match self.look_into(stamp) {
                    Known::Pure | Known::InProgress => {}
                    Known::Impure(loc, reason) => {
                        let line = loc.loc_start.line;
                        self.report(
                            e.exp_loc,
                            format!(
                                "`{name}` is not pure, and `{}` is {}.\n\nLine {line}: {reason}.",
                                self.root,
                                self.marker()
                            ),
                        );
                    }
                }
                return;
            }
        }
        match shape {
            Shape::Mutable => self.report(
                e.exp_loc,
                format!(
                    "`{name}` is defined outside `{}` and its type lets it change, so two calls of `{}` could read different values.\n\n\
                     `{}` is {}: pass the value as an argument, or mark `{name}` with @pure if nothing ever changes it.",
                    self.root,
                    self.root,
                    self.root,
                    self.marker()
                ),
            ),
            _ => self.report(
                e.exp_loc,
                format!(
                    "`{name}` is not marked @pure, and `{}` is {}.\n\n\
                     A {} function can only use values that are @pure themselves. If `{name}` has no side effects, mark it with @pure where it is defined.",
                    self.root,
                    self.marker(),
                    self.marker()
                ),
            ),
        }
    }

    /// Whether an unannotated binding of this file is pure, checking it the
    /// first time it is asked.
    fn look_into(&mut self, stamp: i32) -> Known {
        if let Some(known) = self.shared.known.get(&stamp) {
            return known.clone();
        }
        self.shared.known.insert(stamp, Known::InProgress);
        let binding = self.shared.index.bindings[&stamp];
        let mut checker = Checker::new(self.shared, binding.name, Declared::Pure, true);
        checker.run(binding.expr);
        let known = match checker.diagnostics.into_iter().next() {
            None => Known::Pure,
            Some(diagnostic) => Known::Impure(diagnostic.loc, what_happens(&diagnostic.message)),
        };
        self.shared.known.insert(stamp, known.clone());
        known
    }

    /// Whether an expression makes a new mutable value nothing else refers
    /// to.
    fn is_fresh(&mut self, e: &Expression) -> bool {
        let ta = self.shared.ta;
        match &e.exp_desc {
            ExpressionDesc::Texp_record { .. }
            | ExpressionDesc::Texp_array(_)
            | ExpressionDesc::Texp_dict(_)
            | ExpressionDesc::Texp_object_literal(_)
            | ExpressionDesc::Texp_spread(..) => true,
            ExpressionDesc::Texp_apply {
                funct,
                partial: false,
                ..
            } => {
                let ExpressionDesc::Texp_ident(path, _, vd) = &ta.expr(*funct).exp_desc else {
                    return false;
                };
                let ValueKind::ValPrim(prim) = &vd.val_kind else {
                    // A function of this file whose result is a value it
                    // made itself.
                    return match self.shared.index.resolve(path) {
                        Some(stamp) => self.returns_fresh(stamp),
                        None => false,
                    };
                };
                match &prim.prim_kind {
                    PrimKind::KindIntrinsic => intrinsic(&prim.prim_name) == Intrinsic::Fresh,
                    PrimKind::KindInlineConst(_) => false,
                    PrimKind::KindExternal(ffi) => {
                        declared_of_decl_attributes(&vd.val_attributes) == Some(Declared::Pure)
                            && match &**ffi {
                                ExternalFfi::FfiObjCreate(_) => true,
                                // A property read gives a value the object
                                // already holds.
                                ExternalFfi::FfiBs(_, _, decl) => matches!(
                                    decl.kind,
                                    DeclKind::DeclVal { .. }
                                        | DeclKind::DeclSend { .. }
                                        | DeclKind::DeclNew { .. }
                                ),
                            }
                            && self.returns_constructed(vd)
                    }
                }
            }
            _ => false,
        }
    }

    /// Whether a function of this file always returns a value it made
    /// itself: every result is a new value, or a local bound to one.
    fn returns_fresh(&mut self, stamp: i32) -> bool {
        if let Some(known) = self.shared.fresh.get(&stamp) {
            return *known;
        }
        // A recursive call does not make the result new by itself.
        self.shared.fresh.insert(stamp, false);
        let ta = self.shared.ta;
        let binding = self.shared.index.bindings[&stamp];
        let fresh = match &ta.expr(binding.expr).exp_desc {
            ExpressionDesc::Texp_function { body, .. } => {
                self.result_is_fresh(*body, &mut HashSet::new())
            }
            _ => false,
        };
        self.shared.fresh.insert(stamp, fresh);
        fresh
    }

    fn result_is_fresh(&mut self, idx: TExprIdx, made: &mut HashSet<i32>) -> bool {
        let ta = self.shared.ta;
        let e = ta.expr(idx);
        match &e.exp_desc {
            ExpressionDesc::Texp_let(_, bindings, body) => {
                for binding in ta.value_bindings(*bindings) {
                    if let Some(id) = bound_name(ta, binding.vb_pat) {
                        if self.is_fresh(ta.expr(binding.vb_expr)) {
                            made.insert(id.stamp());
                        }
                    }
                }
                self.result_is_fresh(*body, made)
            }
            ExpressionDesc::Texp_sequence(_, rest) => self.result_is_fresh(*rest, made),
            ExpressionDesc::Texp_ifthenelse(_, then, Some(otherwise)) => {
                self.result_is_fresh(*then, made) && self.result_is_fresh(*otherwise, made)
            }
            ExpressionDesc::Texp_match(_, cases, exception_cases, _) => ta
                .cases(*cases)
                .iter()
                .chain(ta.cases(*exception_cases))
                .all(|case| self.result_is_fresh(case.c_rhs, made)),
            ExpressionDesc::Texp_ident(path, _, _) => {
                matches!(path.view(), PathView::Pident(id) if made.contains(&id.stamp()))
            }
            // A branch that raises returns nothing.
            ExpressionDesc::Texp_apply { funct, .. } if is_raise(ta, *funct) => true,
            _ => self.is_fresh(e),
        }
    }

    /// Whether a function's declared result is a constructed type and not a
    /// type variable, which would be a value taken out of an argument.
    fn returns_constructed(&self, vd: &ValueDescription) -> bool {
        let ctx = self.shared.ctx;
        let ty = ctx.repr(vd.val_type);
        match &*ctx.borrow_desc(ty) {
            TypeDesc::Tarrow { ret, .. } => {
                matches!(&*ctx.borrow_desc(ctx.repr(*ret)), TypeDesc::Tconstr { .. })
            }
            _ => false,
        }
    }

    fn function(&mut self, e: &Expression, consumed: bool, bound: Option<i32>) {
        let ExpressionDesc::Texp_function {
            params,
            body,
            async_,
        } = &e.exp_desc
        else {
            unreachable!("function is called on functions")
        };
        if *async_ {
            self.report(
                e.exp_loc,
                format!(
                    "An async function is not pure: it creates a promise and schedules work. `{}` is {}.",
                    self.root,
                    self.marker()
                ),
            );
        }
        let depth_bound = self.depth();
        self.frames.push(Frame {
            consumed,
            bound,
            stateful: false,
        });
        let ta = self.shared.ta;
        for param in ta.function_params(*params) {
            self.pat(ta.pattern(param.fp_pat));
        }
        self.expr_at(*body, Use::Value);
        let frame = self.frames.pop().expect("the frame pushed above");
        if frame.stateful {
            if let Some(stamp) = bound {
                self.stateful.insert(stamp, depth_bound);
            }
        }
    }

    fn binding(&mut self, binding: &ValueBinding) {
        let ta = self.shared.ta;
        let value = ta.expr(binding.vb_expr);
        let name = bound_name(ta, binding.vb_pat).map(|id| id.stamp());
        if matches!(value.exp_desc, ExpressionDesc::Texp_function { .. }) {
            self.function(value, false, name);
            return;
        }
        self.expr_at(binding.vb_expr, Use::Value);
        if let Some(stamp) = name {
            if self.is_fresh(value) {
                self.owned.insert(stamp, self.depth());
            }
        }
    }

    fn expr_at(&mut self, idx: TExprIdx, usage: Use) {
        let ta = self.shared.ta;
        self.visit(ta.expr(idx), usage);
    }

    fn visit(&mut self, e: &Expression, usage: Use) {
        if self.done() {
            return;
        }
        let ta = self.shared.ta;
        match &e.exp_desc {
            ExpressionDesc::Texp_ident(path, lid, vd) => {
                let name =
                    written_name(self.shared.arena, self.shared.arena.get_longident(lid.txt));
                self.reference(e, path, &name, vd, usage)
            }
            ExpressionDesc::Texp_apply { funct, args, .. } => {
                let args = ta.apply_args(*args);
                let first = args.iter().find_map(|arg| arg.expression);
                self.expr_at(*funct, Use::Callee(first));
                // A function passed to a call whose result holds no function
                // cannot outlive the call: the callee is pure, so it has
                // nowhere else to keep it.
                let env = self.env_of(e);
                let keeps = Shape::holds_function(self.shared.ctx, env.as_deref(), e.exp_type);
                for arg in args {
                    let Some(arg) = arg.expression else { continue };
                    let value = ta.expr(arg);
                    if keeps {
                        self.visit(value, Use::Value);
                    } else if matches!(value.exp_desc, ExpressionDesc::Texp_function { .. }) {
                        self.function(value, true, None);
                    } else {
                        self.visit(value, Use::Consumed);
                    }
                }
            }
            ExpressionDesc::Texp_function { .. } => self.function(e, false, None),
            ExpressionDesc::Texp_let(_, bindings, body) => {
                for binding in ta.value_bindings(*bindings) {
                    self.binding(binding);
                }
                self.expr_at(*body, usage);
            }
            ExpressionDesc::Texp_sequence(first, second) => {
                self.expr_at(*first, Use::Value);
                self.expr_at(*second, usage);
            }
            ExpressionDesc::Texp_setfield(target, _, _, value)
            | ExpressionDesc::Texp_object_set(target, _, value) => {
                self.change(*target, e.exp_loc);
                self.expr_at(*value, Use::Value);
            }
            ExpressionDesc::Texp_for_await_of(..) => self.report(
                e.exp_loc,
                format!(
                    "`for await` waits for promises, which is an effect. `{}` is {}.",
                    self.root,
                    self.marker()
                ),
            ),
            _ => ti::walk_expr(self, e),
        }
    }
}

impl<'a> TastIterator<'a> for Checker<'a, '_> {
    fn arena(&self) -> &'a TypedArena {
        self.shared.ta
    }

    fn expr(&mut self, e: &Expression) {
        // A child reached through the generic walk is a plain value.
        self.visit(e, Use::Value);
    }

    fn value_binding(&mut self, binding: &ValueBinding) {
        // A `let` inside a module expression of the binding.
        self.binding(binding);
    }
}

/// What a type says about the values it has, for a value read from outside
/// a pure binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// Immutable data with no function in it: a constant.
    Data,
    /// Holds a function (and nothing mutable was found before it).
    Functions,
    /// Can change, or is abstract so that it might.
    Mutable,
}

impl Shape {
    fn of(ctx: &TypeContext, env: Option<&Env>, ty: TypeExprRef) -> Shape {
        let mut walk = ShapeWalk {
            ctx,
            env,
            seen: HashSet::new(),
            function: false,
            mutable: false,
            opaque: false,
            fuel: 2_000,
        };
        walk.ty(ty);
        if walk.mutable {
            Shape::Mutable
        } else if walk.function {
            Shape::Functions
        } else {
            Shape::Data
        }
    }

    /// Whether a value of the type can hold a function. A type whose
    /// values the check cannot see into (an abstract type, a type variable,
    /// an object) counts as holding one.
    fn holds_function(ctx: &TypeContext, env: Option<&Env>, ty: TypeExprRef) -> bool {
        let mut walk = ShapeWalk {
            ctx,
            env,
            seen: HashSet::new(),
            function: false,
            mutable: false,
            opaque: false,
            fuel: 2_000,
        };
        walk.ty(ty);
        walk.function || walk.opaque
    }
}

struct ShapeWalk<'a> {
    ctx: &'a TypeContext,
    env: Option<&'a Env>,
    /// Type constructors already looked into, by name: a recursive type is
    /// looked into once.
    seen: HashSet<String>,
    function: bool,
    mutable: bool,
    /// Found a type whose values cannot be seen into.
    opaque: bool,
    /// Bounds the walk on very large types.
    fuel: u32,
}

impl ShapeWalk<'_> {
    fn ty(&mut self, ty: TypeExprRef) {
        if self.fuel == 0 {
            self.mutable = true;
            self.opaque = true;
            return;
        }
        self.fuel -= 1;
        let ctx = self.ctx;
        let ty = ctx.repr(ty);
        match &*ctx.borrow_desc(ty) {
            // A type variable stands for any type; as the type of a value
            // read from outside it is a constant's.
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => self.opaque = true,
            TypeDesc::Tnil => {}
            TypeDesc::Tarrow { .. } => self.function = true,
            TypeDesc::Ttuple(parts) => {
                for part in ctx.type_list(*parts).iter() {
                    self.ty(part);
                }
            }
            TypeDesc::Tpoly { body, .. } => self.ty(*body),
            TypeDesc::Tconstr { path, args, .. } => {
                let args: Vec<TypeExprRef> = ctx.type_list(*args).iter().collect();
                self.constr(path, &args);
            }
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(*row);
                for (_, field) in crate::types::btype::row_repr(ctx, &row).row_fields.iter() {
                    if let crate::types::RowField::Rpresent(Some(payload)) = field {
                        self.ty(*payload);
                    }
                }
            }
            // JavaScript objects and first-class modules can hold anything.
            _ => {
                self.mutable = true;
                self.opaque = true;
            }
        }
    }

    fn constr(&mut self, path: &Path, args: &[TypeExprRef]) {
        use crate::types::predef;
        let immutable_container = path.same(&predef::path_option())
            || path.same(&predef::path_list())
            || path.same(&predef::path_result());
        let scalar = path.same(&predef::path_int())
            || path.same(&predef::path_char())
            || path.same(&predef::path_float())
            || path.same(&predef::path_bool())
            || path.same(&predef::path_unit())
            || path.same(&predef::path_bigint())
            || path.same(&predef::path_string());
        if scalar {
            return;
        }
        if immutable_container {
            for arg in args {
                self.ty(*arg);
            }
            return;
        }
        if path.same(&predef::path_array())
            || path.same(&predef::path_dict())
            || path.same(&predef::path_promise())
            || path.same(&predef::path_exn())
        {
            self.mutable = true;
            if path.same(&predef::path_promise()) || path.same(&predef::path_exn()) {
                self.opaque = true;
            }
            for arg in args {
                self.ty(*arg);
            }
            return;
        }
        for arg in args {
            self.ty(*arg);
        }
        if !self.seen.insert(path.name()) {
            return;
        }
        let Some(decl) = self.env.and_then(|env| env.lookup_type(path).ok()) else {
            // Unknown here: it might be mutable.
            self.mutable = true;
            self.opaque = true;
            return;
        };
        match &decl.type_kind {
            TypeKind::TypeRecord(labels, _) => {
                for label in labels.iter() {
                    if label.ld_mutable == MutableFlag::Mutable {
                        self.mutable = true;
                    }
                    self.ty(label.ld_type);
                }
            }
            TypeKind::TypeVariant(constructors, _) => {
                for constructor in constructors.iter() {
                    match &constructor.cd_args {
                        ConstructorArguments::CstrTuple(types) => {
                            for ty in types {
                                self.ty(*ty);
                            }
                        }
                        ConstructorArguments::CstrRecord(labels) => {
                            for label in labels {
                                if label.ld_mutable == MutableFlag::Mutable {
                                    self.mutable = true;
                                }
                                self.ty(label.ld_type);
                            }
                        }
                    }
                }
            }
            TypeKind::TypeAbstract => match decl.type_manifest {
                Some(manifest) => self.ty(manifest),
                // An abstract type hides what its values are.
                None => {
                    self.mutable = true;
                    self.opaque = true;
                }
            },
            TypeKind::TypeOpen => {
                self.mutable = true;
                self.opaque = true;
            }
        }
    }
}

/// Whether an expression is `%raw(...)` itself. The frontend writes it as
/// `{ module J = { external unsafe_expr: ... = "#raw_expr" }; J.unsafe_expr(...) }`.
fn is_raw(ta: &TypedArena, expr: TExprIdx) -> bool {
    let mut expr = ta.expr(expr);
    if let ExpressionDesc::Texp_letmodule(_, _, _, body) = &expr.exp_desc {
        expr = ta.expr(*body);
    }
    let ExpressionDesc::Texp_apply { funct, .. } = &expr.exp_desc else {
        return false;
    };
    let ExpressionDesc::Texp_ident(_, _, vd) = &ta.expr(*funct).exp_desc else {
        return false;
    };
    matches!(&vd.val_kind, ValueKind::ValPrim(prim) if prim.prim_name == RAW_EXPR)
}

/// Whether an expression is the primitive that raises.
fn is_raise(ta: &TypedArena, funct: TExprIdx) -> bool {
    let ExpressionDesc::Texp_ident(_, _, vd) = &ta.expr(funct).exp_desc else {
        return false;
    };
    matches!(&vd.val_kind, ValueKind::ValPrim(prim) if prim.prim_name == "%raise")
}

/// A name as it is written in the source.
fn written_name(arena: &ParseArena, lid: &crate::parser::longident::Longident) -> String {
    use crate::parser::longident::Longident;
    match lid {
        Longident::Lident(name) => arena.get_string(*name).to_string(),
        Longident::Ldot(prefix, name) => {
            format!(
                "{}.{}",
                written_name(arena, prefix),
                arena.get_string(*name)
            )
        }
        Longident::Lapply(function, argument) => {
            format!(
                "{}({})",
                written_name(arena, function),
                written_name(arena, argument)
            )
        }
    }
}

/// What a report says happens, without the part that names the binding
/// being checked: reports read "<what happens>, and `f` is @pure." or
/// "<what happens>. ...".
fn what_happens(message: &str) -> String {
    let first = message.split("\n\n").next().unwrap_or(message);
    let first = first.split(", and `").next().unwrap_or(first);
    let first = first.split(". ").next().unwrap_or(first);
    first.trim_end_matches('.').replace('\n', " ")
}

/// The bindings of a type checked implementation.
/// Cost: one walk of the typed tree.
pub(super) fn index(ta: &TypedArena, arena: &ParseArena, structure: &Structure) -> Index {
    let mut indexer = Indexer {
        ta,
        arena,
        index: Index::default(),
        implied: &|_| false,
    };
    indexer.structure(structure);
    indexer.index
}

/// Check every `@pure` and `@mutates` binding of a type checked
/// implementation. `implied` names further bindings that are pure by what
/// they are (a law, a spec), from their attributes. `obligations` are the
/// effects signatures required of values while the unit was typed: a
/// binding of the unit is checked as if it declared the effect.
pub fn check(
    ctx: &TypeContext,
    ta: &TypedArena,
    arena: &ParseArena,
    structure: &Structure,
    implied: &dyn Fn(&Attributes) -> bool,
    obligations: &[Obligation],
) -> Vec<Diagnostic> {
    let mut indexer = Indexer {
        ta,
        arena,
        index: Index::default(),
        implied,
    };
    indexer.structure(structure);
    let mut shared = Shared {
        ctx,
        ta,
        arena,
        index: indexer.index,
        known: HashMap::new(),
        fresh: HashMap::new(),
    };
    let mut diagnostics = Vec::new();
    for obligation in obligations {
        let name = obligation.name;
        let required = obligation.declared;
        let Some(binding) = shared.index.bindings.get_mut(&obligation.stamp) else {
            if Shape::of(ctx, None, obligation.ty) == Shape::Data {
                // A constant: nothing can change it.
                continue;
            }
            // Not a `let` of this file: nothing here can be checked.
            diagnostics.push(Diagnostic {
                loc: ctx.resolve_loc(obligation.signature_loc),
                message: format!(
                    "A signature declares `{name}` {}, and the `{name}` given for it is not marked {}.\n\n\
                     It is not a `let` of this file, so it cannot be checked here. Mark it {} where it is defined.",
                    required.marker(),
                    required.marker(),
                    required.marker()
                ),
            });
            continue;
        };
        match binding.declared {
            None => {
                binding.declared = Some(required);
                shared.index.annotated.push(obligation.stamp);
            }
            Some(own) if own != required => diagnostics.push(Diagnostic {
                loc: arena.to_location(binding.loc),
                message: format!(
                    "A signature declares `{name}` {}, and this binding is {}.",
                    required.marker(),
                    own.marker()
                ),
            }),
            Some(_) => {}
        }
    }
    let mut annotated = shared.index.annotated.clone();
    annotated.sort_unstable();
    annotated.dedup();
    for stamp in annotated {
        let binding = shared.index.bindings[&stamp];
        let declared = binding
            .declared
            .expect("annotated bindings declare an effect");
        shared.known.insert(stamp, Known::Pure);
        match binding.payload {
            Payload::Checked => {}
            // The author vouches for the binding, as for an external.
            Payload::Unchecked => continue,
            Payload::Unknown => {
                diagnostics.push(Diagnostic {
                    loc: arena.to_location(binding.loc),
                    message: format!(
                        "{} takes no argument, or `unchecked` to skip the check: {}(unchecked).",
                        declared.marker(),
                        declared.marker()
                    ),
                });
                continue;
            }
        }
        if is_raw(ta, binding.expr) {
            // `%raw` is JavaScript: like an external, it is taken on trust.
            continue;
        }
        let mut checker = Checker::new(&mut shared, binding.name, declared, false);
        checker.run(binding.expr);
        diagnostics.append(&mut checker.diagnostics);
    }
    diagnostics.sort_by_key(|diagnostic| {
        let start = &diagnostic.loc.loc_start;
        (start.line, start.cnum)
    });
    diagnostics
}
