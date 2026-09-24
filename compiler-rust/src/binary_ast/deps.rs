//! Module dependency extraction from AST
//!
//! This module provides functionality to extract module dependencies from
//! ReScript AST, matching the OCaml implementation in `compiler/frontend/ast_extract.ml`.
//!
//! Dependencies are extracted by walking the AST and collecting all module references
//! from Longidents. Only uppercase module names are collected (lowercase names are
//! local bindings, not module references).

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LidentIdx, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::{
    Attributes, Case, ConstructorArguments, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExtensionConstructor, ExtensionConstructorKind, IncludeDeclaration, IncludeDescription,
    LabelDeclaration, ModuleBinding, ModuleDeclaration, ModuleExpr, ModuleExprDesc, ModuleType,
    ModuleTypeDeclaration, ModuleTypeDesc, ObjectField, OpenDescription, Pattern, PatternDesc,
    Payload, RowField, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc,
    TypeDeclaration, TypeExtension, TypeKind, ValueDescription, WithConstraint,
};
use crate::parser::ast::{PexpApply, PexpFun};
use crate::parser::longident::Longident;

/// A set of module dependencies, sorted for deterministic output.
pub type Dependencies = BTreeSet<String>;

/// Extract module dependencies from a structure (implementation).
pub fn extract_structure_deps(arena: &ParseArena, structure: &[StructureItem]) -> Dependencies {
    let mut collector = DependencyCollector::new(arena);
    collector.add_structure(structure);
    collector.finish()
}

/// Extract module dependencies from a signature (interface).
pub fn extract_signature_deps(arena: &ParseArena, signature: &[SignatureItem]) -> Dependencies {
    let mut collector = DependencyCollector::new(arena);
    collector.add_signature(signature);
    collector.finish()
}

/// Collector for module dependencies.
struct DependencyCollector<'a> {
    arena: &'a ParseArena,
    deps: BTreeSet<String>,
    /// Bound module names (from letmodule, module, etc.) that should not be added as dependencies
    bound_modules: HashSet<String>,
    /// For locally-bound modules, track names introduced by their inner structure/signature.
    /// Used to model OCaml `open_module` behavior (`open M` brings submodules into scope).
    module_members: HashMap<String, HashSet<String>>,
}

impl<'a> DependencyCollector<'a> {
    fn new(arena: &'a ParseArena) -> Self {
        Self {
            arena,
            deps: BTreeSet::new(),
            bound_modules: HashSet::new(),
            module_members: HashMap::new(),
        }
    }

    /// Finish collecting and return the filtered dependencies.
    fn finish(self) -> Dependencies {
        // Filter out:
        // - Empty strings
        // - Strings starting with '*' (like *predef*)
        self.deps
            .into_iter()
            .filter(|s| !s.is_empty() && !s.starts_with('*'))
            .collect()
    }

    // ========== Arena index helper methods ==========

    fn add_expr_idx(&mut self, idx: ExprIdx) {
        let arena = self.arena;
        let expr = arena.get_expr(idx);
        self.add_expression(expr);
    }

    fn add_pat_idx(&mut self, idx: PatIdx) {
        let arena = self.arena;
        let pat = arena.get_pat(idx);
        self.add_pattern(pat);
    }

    fn add_pat_idx_collecting_unpack(&mut self, idx: PatIdx) -> HashSet<String> {
        let arena = self.arena;
        let pat = arena.get_pat(idx);
        self.add_pattern_collecting_unpack(pat)
    }

    fn add_pat_idx_inner(&mut self, idx: PatIdx, unpack_names: &mut HashSet<String>) {
        let arena = self.arena;
        let pat = arena.get_pat(idx);
        self.add_pattern_inner(&pat, unpack_names);
    }

    fn add_core_type_idx(&mut self, idx: CoreTypeIdx) {
        let arena = self.arena;
        let ty = arena.get_core_type(idx);
        self.add_core_type(ty);
    }

    fn add_mod_expr_idx(&mut self, idx: ModExprIdx) {
        let arena = self.arena;
        let me = arena.get_mod_expr(idx);
        self.add_module_expr(me);
    }

    fn add_mod_type_idx(&mut self, idx: ModTypeIdx) {
        let arena = self.arena;
        let mt = arena.get_mod_type(idx);
        self.add_module_type(mt);
    }

    // ========== Longident methods ==========

    /// Add a module reference from a Longident (full path).
    /// This is used for module-level references like `open Foo` or `include Bar`.
    fn add_longident_full(&mut self, lid: &Longident) {
        // Get the root module name
        let parts = lid.flatten_idx();
        if let Some(first) = parts.first() {
            // Look up the string content
            let first_str = self.arena.get_string(*first);
            // Only add if it starts with uppercase (module reference)
            // Lowercase identifiers are local bindings
            // Also skip if it's a bound module name (from letmodule, etc.)
            if first_str
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase())
                && !self.bound_modules.contains(first_str)
            {
                self.deps.insert(first_str.to_string());
            }
        }

        // Also collect from functor applications
        if let Longident::Lapply(func, arg) = lid {
            self.add_longident_full(func);
            self.add_longident_full(arg);
        }
    }

    /// Add a module reference from a Longident, but only the parent module.
    /// This matches OCaml's `add_parent` function: for `Foo.bar` it adds `Foo`,
    /// but for `bar` alone it adds nothing.
    ///
    /// This is used for value/type/constructor references where a simple Lident
    /// like `None` or `Some` refers to a local constructor, not a module dependency.
    fn add_longident_parent(&mut self, lid: &Longident) {
        match lid {
            Longident::Ldot(parent, _) => {
                // For dotted paths like Foo.bar, add the parent path
                self.add_longident_full(parent);
            }
            Longident::Lapply(func, arg) => {
                // For functor applications, add both parts
                self.add_longident_full(func);
                self.add_longident_full(arg);
            }
            Longident::Lident(_) => {
                // For simple identifiers like `None` or `foo`, don't add anything
                // These are local values/constructors, not module references
            }
        }
    }

    /// Add a module reference from a LidentIdx (arena-allocated longident).
    /// Uses add_parent semantics - only parent modules, not simple identifiers.
    fn add_lident_idx(&mut self, lid_idx: LidentIdx) {
        let lid = self.arena.get_longident(lid_idx);
        self.add_longident_parent(lid);
    }

    /// Add a full module path reference from a LidentIdx.
    /// Used for module-level references like `open Foo`, `include Bar`, or module idents.
    fn add_lident_idx_full(&mut self, lid_idx: LidentIdx) {
        let lid = self.arena.get_longident(lid_idx);
        self.add_longident_full(lid);
    }

    fn lident_simple_name(&self, lid_idx: LidentIdx) -> Option<String> {
        match self.arena.get_longident(lid_idx) {
            Longident::Lident(name_idx) => Some(self.arena.get_string(*name_idx).to_string()),
            _ => None,
        }
    }

    /// Bind names brought into scope by `open <module>`.
    /// Returns names newly inserted into bound_modules (for local-open unwinding).
    fn bind_opened_members(&mut self, lid_idx: LidentIdx) -> Vec<String> {
        let Some(opened_module) = self.lident_simple_name(lid_idx) else {
            return Vec::new();
        };

        let Some(members) = self.module_members.get(&opened_module) else {
            return Vec::new();
        };

        let members: Vec<String> = members.iter().cloned().collect();
        members
            .into_iter()
            .filter(|name| self.bound_modules.insert(name.clone()))
            .collect()
    }

    // ========== Structure ==========

    fn add_structure(&mut self, structure: &[StructureItem]) {
        for item in structure {
            self.add_structure_item(item);
        }
    }

    fn add_structure_item(&mut self, item: &StructureItem) {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (ref expr, ref _attrs) = **inner;
                self.add_expr_idx(*expr);
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (ref _rec_flag, ref bindings) = **inner;
                // OCaml's add_bindings collects pattern bindings (including Ppat_unpack)
                // and adds them to bound_modules so later references don't add dependencies.
                // First collect all unpack names from patterns
                let mut unpack_names = HashSet::new();
                for binding in bindings {
                    let names = self.add_pat_idx_collecting_unpack(binding.pvb_pat);
                    unpack_names.extend(names);
                }
                // Add collected unpack names to bound_modules
                // This must happen before processing expressions so that references
                // to these modules in the same or later bindings don't add dependencies
                self.bound_modules.extend(unpack_names);
                // Now process expressions
                for binding in bindings {
                    self.add_expr_idx(binding.pvb_expr);
                }
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                self.add_value_description(vd);
            }
            StructureItemDesc::Pstr_type(inner) => {
                let (ref _rec_flag, ref decls) = **inner;
                for decl in decls {
                    self.add_type_declaration(decl);
                }
            }
            StructureItemDesc::Pstr_typext(ext) => {
                self.add_type_extension(ext);
            }
            StructureItemDesc::Pstr_exception(ext_ctor) => {
                self.add_extension_constructor(ext_ctor);
            }
            StructureItemDesc::Pstr_module(mb) => {
                let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                // OCaml's `add_module_binding` returns a local map for the module body.
                // Nested module bindings inside that body must NOT leak into outer scope.
                // Keep the body traversal for dependency collection, then restore outer
                // bindings before adding the module's own binding at this level.
                let outer_bound_modules = self.bound_modules.clone();
                self.add_module_binding(mb);
                let nested_members: HashSet<String> = self
                    .bound_modules
                    .difference(&outer_bound_modules)
                    .cloned()
                    .collect();
                self.bound_modules = outer_bound_modules;
                self.bound_modules.insert(module_name);
                if !nested_members.is_empty() {
                    let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                    self.module_members.insert(module_name, nested_members);
                }
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                // First bind all module names so they're not added as dependencies
                for mb in &**mbs {
                    let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                    self.bound_modules.insert(module_name);
                }
                // Then process all module expressions
                for mb in &**mbs {
                    // Match OCaml's functional scoping: nested bindings inside each
                    // module body do not escape the recursive-module item scope.
                    let outer_bound_modules = self.bound_modules.clone();
                    self.add_module_binding(mb);
                    let nested_members: HashSet<String> = self
                        .bound_modules
                        .difference(&outer_bound_modules)
                        .cloned()
                        .collect();
                    self.bound_modules = outer_bound_modules;
                    if !nested_members.is_empty() {
                        let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                        self.module_members.insert(module_name, nested_members);
                    }
                }
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                self.add_module_type_declaration(mtd);
            }
            StructureItemDesc::Pstr_open(od) => {
                self.add_open_description(od);
            }
            StructureItemDesc::Pstr_include(incl) => {
                self.add_include_declaration(incl);
            }
            StructureItemDesc::Pstr_attribute(_attr) => {
                // Attributes don't contribute dependencies
            }
            StructureItemDesc::Pstr_extension(inner) => {
                // Extension payload ignored for dependency extraction
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
        }
    }

    // ========== Signature ==========

    fn add_signature(&mut self, signature: &[SignatureItem]) {
        for item in signature {
            self.add_signature_item(item);
        }
    }

    fn add_signature_item(&mut self, item: &SignatureItem) {
        match &*item.psig_desc {
            SignatureItemDesc::Psig_value(vd) => {
                self.add_value_description(vd);
            }
            SignatureItemDesc::Psig_type(inner) => {
                let (ref _rec_flag, ref decls) = **inner;
                for decl in decls {
                    self.add_type_declaration(decl);
                }
            }
            SignatureItemDesc::Psig_typext(ext) => {
                self.add_type_extension(ext);
            }
            SignatureItemDesc::Psig_exception(ext_ctor) => {
                self.add_extension_constructor(ext_ctor);
            }
            SignatureItemDesc::Psig_module(md) => {
                // Bind the module name so it's not added as a dependency when referenced
                let module_name = self.arena.get_string(md.pmd_name.txt).to_string();
                self.bound_modules.insert(module_name);
                // Like OCaml `add_modtype_binding`, nested signature bindings are local
                // to this module declaration and must not leak to outer scope.
                let outer_bound_modules = self.bound_modules.clone();
                self.add_module_declaration(md);
                let nested_members: HashSet<String> = self
                    .bound_modules
                    .difference(&outer_bound_modules)
                    .cloned()
                    .collect();
                self.bound_modules = outer_bound_modules;
                if !nested_members.is_empty() {
                    let module_name = self.arena.get_string(md.pmd_name.txt).to_string();
                    self.module_members.insert(module_name, nested_members);
                }
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                // First bind all module names
                for md in &**mds {
                    let module_name = self.arena.get_string(md.pmd_name.txt).to_string();
                    self.bound_modules.insert(module_name);
                }
                // Then process all module declarations
                for md in &**mds {
                    let outer_bound_modules = self.bound_modules.clone();
                    self.add_module_declaration(md);
                    let nested_members: HashSet<String> = self
                        .bound_modules
                        .difference(&outer_bound_modules)
                        .cloned()
                        .collect();
                    self.bound_modules = outer_bound_modules;
                    if !nested_members.is_empty() {
                        let module_name = self.arena.get_string(md.pmd_name.txt).to_string();
                        self.module_members.insert(module_name, nested_members);
                    }
                }
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                self.add_module_type_declaration(mtd);
            }
            SignatureItemDesc::Psig_open(od) => {
                self.add_open_description(od);
            }
            SignatureItemDesc::Psig_include(incl) => {
                self.add_include_description(incl);
            }
            SignatureItemDesc::Psig_attribute(_attr) => {
                // Attributes don't contribute dependencies
            }
            SignatureItemDesc::Psig_extension(inner) => {
                // Extension payload ignored for dependency extraction
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
        }
    }

    // ========== Expressions ==========

    fn add_expression(&mut self, expr: &Expression) {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_ident(lid) => {
                self.add_lident_idx(lid.txt);
            }
            ExpressionDesc::Pexp_constant(_) => {}
            ExpressionDesc::Pexp_break | ExpressionDesc::Pexp_continue => {}
            ExpressionDesc::Pexp_let(inner) => {
                let (ref _rec_flag, ref bindings, ref body) = **inner;
                // OCaml's add_bindings collects pattern bindings (including Ppat_unpack)
                // First collect all unpack names from patterns
                let mut unpack_names = HashSet::new();
                for binding in bindings {
                    let names = self.add_pat_idx_collecting_unpack(binding.pvb_pat);
                    unpack_names.extend(names);
                }
                // Add collected unpack names to bound_modules for the body expression,
                // then remove them after processing (OCaml scopes bv functionally).
                // Only track names that are NEWLY added (not already bound) to avoid
                // removing outer bindings when the scope exits.
                let newly_added: HashSet<String> = unpack_names
                    .into_iter()
                    .filter(|name| self.bound_modules.insert(name.clone()))
                    .collect();
                // Process expressions
                for binding in bindings {
                    self.add_expr_idx(binding.pvb_expr);
                }
                // body is ExprIdx
                let body = *body;
                self.add_expr_idx(body);
                for name in &newly_added {
                    self.bound_modules.remove(name);
                }
            }
            ExpressionDesc::Pexp_fun(inner) => {
                // OCaml Depend.add_expr folds over all n-ary parameters
                // (compiler/ml/depend.ml:215-226): for each parameter visit its
                // default expression then its pattern, threading bound module
                // names through the parameter list, before visiting the body.
                // The parser-facing parameter list lives in a sparse side table;
                // only the first parameter is kept in the compact node payload.
                let nary_params: Vec<crate::parser::ast::FunParam> =
                    match self.arena.stored_nary_fun_params(inner) {
                        Some(params) => params.to_vec(),
                        None => Vec::new(),
                    };
                if !nary_params.is_empty() {
                    let mut newly_added: Vec<String> = Vec::new();
                    for param in &nary_params {
                        if let Some(default) = param.p_default {
                            self.add_expr_idx(default);
                        }
                        let unpack_names = self.add_pat_idx_collecting_unpack(param.p_pat);
                        for name in unpack_names {
                            if self.bound_modules.insert(name.clone()) {
                                newly_added.push(name);
                            }
                        }
                    }
                    self.add_expr_idx(inner.rhs);
                    for name in newly_added {
                        self.bound_modules.remove(&name);
                    }
                    return;
                }
                let PexpFun {
                    default, lhs, rhs, ..
                } = &**inner;
                if let Some(default) = default {
                    // default is ExprIdx
                    let default = *default;
                    self.add_expr_idx(default);
                }
                // OCaml: add_expr (add_pattern bv p) e
                // Collect unpack names from pattern and add to bound_modules for rhs,
                // then remove them after processing (OCaml scopes bv functionally)
                let unpack_names = self.add_pat_idx_collecting_unpack(*lhs);
                // Only track names that are NEWLY added (not already bound) to avoid
                // removing outer bindings when the scope exits.
                let newly_added: Vec<String> = unpack_names
                    .into_iter()
                    .filter(|name| self.bound_modules.insert(name.clone()))
                    .collect();
                // rhs is ExprIdx
                let rhs = *rhs;
                self.add_expr_idx(rhs);
                for name in &newly_added {
                    self.bound_modules.remove(name);
                }
            }
            ExpressionDesc::Pexp_apply(inner) => {
                let PexpApply {
                    ref funct,
                    ref args,
                    ..
                } = **inner;
                // funct is ExprIdx
                let funct = *funct;
                self.add_expr_idx(funct);
                for (_label, arg) in args {
                    self.add_expr_idx(*arg);
                }
            }
            ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
                let (ref expr, ref cases) = **inner;
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
                for case in cases {
                    self.add_case(case);
                }
            }
            ExpressionDesc::Pexp_tuple(exprs) | ExpressionDesc::Pexp_array(exprs) => {
                for expr in &**exprs {
                    self.add_expr_idx(*expr);
                }
            }
            ExpressionDesc::Pexp_construct(lid, arg) => {
                self.add_lident_idx(lid.txt);
                if let Some(arg) = arg {
                    // arg is ExprIdx
                    let arg = *arg;
                    self.add_expr_idx(arg);
                }
            }
            ExpressionDesc::Pexp_variant(inner) => {
                let (ref _label, ref arg) = **inner;
                if let Some(arg) = arg {
                    // arg is ExprIdx
                    let arg = *arg;
                    self.add_expr_idx(arg);
                }
            }
            ExpressionDesc::Pexp_record(inner) => {
                let (ref fields, ref spread) = **inner;
                for field in fields {
                    self.add_lident_idx(field.lid.txt);
                    self.add_expr_idx(field.expr);
                }
                if let Some(spread) = spread {
                    // spread is ExprIdx
                    let spread = *spread;
                    self.add_expr_idx(spread);
                }
            }
            ExpressionDesc::Pexp_field(expr, lid) => {
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
                self.add_lident_idx(lid.txt);
            }
            ExpressionDesc::Pexp_setfield(inner) => {
                let (ref expr1, ref lid, ref expr2) = **inner;
                // expr1 and expr2 are ExprIdx
                let expr1 = *expr1;
                let expr2 = *expr2;
                self.add_expr_idx(expr1);
                self.add_lident_idx(lid.txt);
                self.add_expr_idx(expr2);
            }
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (ref cond, ref then_expr, ref else_expr) = **inner;
                // cond, then_expr, else_expr are ExprIdx
                let cond = *cond;
                let then_expr = *then_expr;
                self.add_expr_idx(cond);
                self.add_expr_idx(then_expr);
                if let Some(else_expr) = else_expr {
                    let else_expr = *else_expr;
                    self.add_expr_idx(else_expr);
                }
            }
            ExpressionDesc::Pexp_sequence(e1, e2) => {
                // e1 and e2 are ExprIdx
                let e1 = *e1;
                let e2 = *e2;
                self.add_expr_idx(e1);
                self.add_expr_idx(e2);
            }
            ExpressionDesc::Pexp_while(cond, body) => {
                // cond and body are ExprIdx
                let cond = *cond;
                let body = *body;
                self.add_expr_idx(cond);
                self.add_expr_idx(body);
            }
            ExpressionDesc::Pexp_for(inner) => {
                let (ref _pat, ref start, ref end, ref _dir, ref body) = **inner;
                // OCaml: Pexp_for (_, e1, e2, _, e3) - ignores the pattern
                // The for-loop pattern doesn't add dependencies
                // start, end, body are ExprIdx
                let start = *start;
                let end = *end;
                let body = *body;
                self.add_expr_idx(start);
                self.add_expr_idx(end);
                self.add_expr_idx(body);
            }
            ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
                // Upstream #7887: pattern is `_` or var, contributes no deps.
                let (ref _pat, ref iterable, ref body) = **inner;
                let iterable = *iterable;
                let body = *body;
                self.add_expr_idx(iterable);
                self.add_expr_idx(body);
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                let (ref expr, ref ty) = **inner;
                // expr is ExprIdx, ty is CoreTypeIdx
                let expr = *expr;
                let ty = *ty;
                self.add_expr_idx(expr);
                self.add_core_type_idx(ty);
            }
            ExpressionDesc::Pexp_coerce(inner) => {
                let (ref expr, ref ty1, ref ty2) = **inner;
                // expr is ExprIdx, ty1 is Option<CoreTypeIdx>, ty2 is CoreTypeIdx
                let expr = *expr;
                self.add_expr_idx(expr);
                if let Some(ty1) = ty1 {
                    self.add_core_type_idx(*ty1);
                }
                self.add_core_type_idx(*ty2);
            }
            ExpressionDesc::Pexp_send(inner) => {
                let (ref expr, ref _label) = **inner;
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
            }
            ExpressionDesc::Pexp_letmodule(inner) => {
                let (ref name, ref me, ref body) = **inner;
                // Bind the module name so it's not added as a dependency
                let module_name = self.arena.get_string(name.txt).to_string();
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let newly_added = self.bound_modules.insert(module_name.clone());
                // me is ModExprIdx
                self.add_mod_expr_idx(*me);
                // body is ExprIdx
                let body = *body;
                self.add_expr_idx(body);
                if newly_added {
                    self.bound_modules.remove(&module_name);
                }
            }
            ExpressionDesc::Pexp_letexception(inner) => {
                let (ref ext_ctor, ref body) = **inner;
                self.add_extension_constructor(ext_ctor);
                // body is ExprIdx
                let body = *body;
                self.add_expr_idx(body);
            }
            ExpressionDesc::Pexp_assert(expr) => {
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
            }
            ExpressionDesc::Pexp_newtype(inner) => {
                let (ref _name, ref body) = **inner;
                // body is ExprIdx
                let body = *body;
                self.add_expr_idx(body);
            }
            ExpressionDesc::Pexp_pack(me) => {
                // me is ModExprIdx
                let me = *me;
                self.add_mod_expr_idx(me);
            }
            ExpressionDesc::Pexp_open(inner) => {
                let (ref _override, ref lid, ref body) = **inner;
                // Local open uses full module path
                self.add_lident_idx_full(lid.txt);
                let newly_opened_members = self.bind_opened_members(lid.txt);
                // body is ExprIdx
                let body = *body;
                self.add_expr_idx(body);
                for name in &newly_opened_members {
                    self.bound_modules.remove(name);
                }
            }
            ExpressionDesc::Pexp_extension(_ext_inner) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
            ExpressionDesc::Pexp_await(expr) => {
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
            }
            ExpressionDesc::Pexp_jsx_element(jsx) => {
                self.add_jsx_element(jsx);
            }
            ExpressionDesc::Pexp_inline_for(inner) => {
                let (ref _pat, ref collection, ref body) = **inner;
                self.add_expr_idx(*collection);
                self.add_expr_idx(*body);
            }
            ExpressionDesc::Pexp_comptime_typeinfo(_)
            | ExpressionDesc::Pexp_comptime_typename(_) => {
                // No expression dependencies to scan
            }
            ExpressionDesc::Pexp_comptime_field(inner) => {
                let (ref value, ref field) = **inner;
                self.add_expr_idx(*value);
                self.add_expr_idx(*field);
            }
            ExpressionDesc::Pexp_comptime_compile_error(expr) => {
                self.add_expr_idx(*expr);
            }
            ExpressionDesc::Pexp_comptime_record(inner) => {
                let (ref _ct, ref fields_expr) = **inner;
                self.add_expr_idx(*fields_expr);
            }
            ExpressionDesc::Pexp_comptime_variant(inner) => {
                let (ref _ct, ref expr, ref opt_expr) = **inner;
                self.add_expr_idx(*expr);
                if let Some(e) = opt_expr {
                    self.add_expr_idx(*e);
                }
            }
            ExpressionDesc::Pexp_comptime_build_variant(e) => {
                self.add_expr_idx(*e);
            }
            ExpressionDesc::Pexp_comptime_variant_case(e) => {
                self.add_expr_idx(*e);
            }
            ExpressionDesc::Pexp_comptime_build_record(e) => {
                self.add_expr_idx(*e);
            }
            ExpressionDesc::Pexp_comptime_record_field(e) => {
                self.add_expr_idx(*e);
            }
        }
    }

    fn add_jsx_element(&mut self, jsx: &crate::parser::ast::JsxElement) {
        use crate::parser::ast::{JsxElement, JsxTagName};

        match jsx {
            JsxElement::Fragment(frag) => {
                for child in &frag.children {
                    // child is ExprIdx
                    self.add_expr_idx(*child);
                }
            }
            JsxElement::Unary(elem) => {
                // Add dependency from tag name if it's a component
                // JSX components like <Foo /> are module references and use full path
                match &elem.tag_name.txt {
                    JsxTagName::Upper(lid) => {
                        self.add_lident_idx_full(*lid);
                    }
                    JsxTagName::QualifiedLower { path, .. } => {
                        self.add_lident_idx_full(*path);
                    }
                    JsxTagName::Lower(_) | JsxTagName::Invalid(_) => {}
                }
                for prop in &elem.props {
                    self.add_jsx_prop(prop);
                }
            }
            JsxElement::Container(elem) => {
                match &elem.tag_name_start.txt {
                    JsxTagName::Upper(lid) => {
                        self.add_lident_idx_full(*lid);
                    }
                    JsxTagName::QualifiedLower { path, .. } => {
                        self.add_lident_idx_full(*path);
                    }
                    JsxTagName::Lower(_) | JsxTagName::Invalid(_) => {}
                }
                for prop in &elem.props {
                    self.add_jsx_prop(prop);
                }
                for child in &elem.children {
                    // child is ExprIdx
                    self.add_expr_idx(*child);
                }
            }
        }
    }

    fn add_jsx_prop(&mut self, prop: &crate::parser::ast::JsxProp) {
        use crate::parser::ast::JsxProp;
        match prop {
            JsxProp::Punning { .. } => {}
            JsxProp::Value { value, .. } => {
                // value is ExprIdx
                self.add_expr_idx(*value);
            }
            JsxProp::Spreading { expr, .. } => {
                // expr is ExprIdx
                self.add_expr_idx(*expr);
            }
        }
    }

    // ========== Patterns ==========

    /// Add dependencies from a pattern, and collect any module names bound by Ppat_unpack.
    /// Returns the set of module names bound by unpack patterns.
    fn add_pattern_collecting_unpack(&mut self, pat: &Pattern) -> HashSet<String> {
        let mut unpack_names = HashSet::new();
        self.add_pattern_inner(pat, &mut unpack_names);
        unpack_names
    }

    fn add_pattern(&mut self, pat: &Pattern) {
        let mut unpack_names = HashSet::new();
        self.add_pattern_inner(pat, &mut unpack_names);
        // Note: we don't use unpack_names here because add_pattern is called
        // in contexts where the unpack bindings don't persist (e.g., match cases)
    }

    fn add_pattern_inner(&mut self, pat: &Pattern, unpack_names: &mut HashSet<String>) {
        match &*pat.ppat_desc {
            PatternDesc::Ppat_any | PatternDesc::Ppat_var(_) | PatternDesc::Ppat_constant(_) => {}
            PatternDesc::Ppat_alias(pat_idx, _name) => {
                // pat is PatIdx
                let pat_idx = *pat_idx;
                self.add_pat_idx_inner(pat_idx, unpack_names);
            }
            PatternDesc::Ppat_interval(inner) => {
                let (_, _) = &**inner;
            }
            PatternDesc::Ppat_tuple(pats) | PatternDesc::Ppat_array(pats) => {
                for pat in &**pats {
                    // pat is PatIdx
                    self.add_pat_idx_inner(*pat, unpack_names);
                }
            }
            PatternDesc::Ppat_construct(lid, arg) => {
                self.add_lident_idx(lid.txt);
                if let Some(arg) = arg {
                    // arg is PatIdx
                    let arg = *arg;
                    self.add_pat_idx_inner(arg, unpack_names);
                }
            }
            PatternDesc::Ppat_variant(inner) => {
                let (ref _label, ref arg) = **inner;
                if let Some(arg) = arg {
                    // arg is PatIdx
                    let arg = *arg;
                    self.add_pat_idx_inner(arg, unpack_names);
                }
            }
            PatternDesc::Ppat_record(inner) => {
                let (ref fields, ref _closed) = **inner;
                for field in fields {
                    self.add_lident_idx(field.lid.txt);
                    // field.pat is PatIdx
                    self.add_pat_idx_inner(field.pat, unpack_names);
                }
                // OCaml Depend visits the rest pattern's type annotation
                // (compiler/ml/depend.ml:187): `...M.t as rest` records a
                // dependency on M. The rest row lives in a sparse side table
                // keyed by the pattern location.
                if let Some(rest) = self.arena.record_pat_rest(pat.ppat_loc)
                    && let Some(rest_type) = rest.rest_type
                {
                    self.add_core_type_idx(rest_type);
                }
            }
            PatternDesc::Ppat_or(p1, p2) => {
                // p1 and p2 are PatIdx
                let p1 = *p1;
                let p2 = *p2;
                self.add_pat_idx_inner(p1, unpack_names);
                self.add_pat_idx_inner(p2, unpack_names);
            }
            PatternDesc::Ppat_constraint(inner) => {
                let (ref pat_idx, ref ty) = **inner;
                // pat is PatIdx, ty is CoreTypeIdx
                let pat_idx = *pat_idx;
                self.add_pat_idx_inner(pat_idx, unpack_names);
                self.add_core_type_idx(*ty);
            }
            PatternDesc::Ppat_type(lid) => {
                self.add_lident_idx(lid.txt);
            }
            PatternDesc::Ppat_unpack(name) => {
                // OCaml: pattern_bv := StringMap.add id.txt bound !pattern_bv
                // Collect the unpack'd module name so it can be added to bound_modules
                let module_name = self.arena.get_string(name.txt).to_string();
                unpack_names.insert(module_name);
            }
            PatternDesc::Ppat_exception(pat_idx) => {
                // pat is PatIdx
                let pat_idx = *pat_idx;
                self.add_pat_idx_inner(pat_idx, unpack_names);
            }
            PatternDesc::Ppat_extension(_ext_inner) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
            PatternDesc::Ppat_open(lid, pat_idx) => {
                // Pattern open uses full module path
                self.add_lident_idx_full(lid.txt);
                // pat is PatIdx
                let pat_idx = *pat_idx;
                self.add_pat_idx_inner(pat_idx, unpack_names);
            }
        }
    }

    // ========== Core Types ==========

    fn add_core_type(&mut self, ty: &CoreType) {
        match &*ty.ptyp_desc {
            CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => {}
            CoreTypeDesc::Ptyp_arrow(inner) => {
                let (ref arg, ref ret, arity) = **inner;
                // OCaml Depend.add_type visits every n-ary arrow parameter
                // (compiler/ml/depend.ml:102-105); the compact payload keeps
                // only the first argument, so recover the full list here.
                for a in self.arena.nary_arrow_args(arg, arity).iter() {
                    self.add_core_type_idx(a.typ);
                }
                let ret = *ret;
                self.add_core_type_idx(ret);
            }
            CoreTypeDesc::Ptyp_tuple(tys) => {
                for ty in &**tys {
                    // ty is CoreTypeIdx
                    self.add_core_type_idx(*ty);
                }
            }
            CoreTypeDesc::Ptyp_constr(inner) => {
                let (ref lid, ref args) = **inner;
                self.add_lident_idx(lid.txt);
                for arg in args {
                    // arg is CoreTypeIdx
                    self.add_core_type_idx(*arg);
                }
            }
            CoreTypeDesc::Ptyp_object(inner) => {
                let (ref fields, ref _closed) = **inner;
                for field in fields {
                    match field {
                        ObjectField::Otag(_label, _attrs, ty) => {
                            // ty is CoreTypeIdx
                            self.add_core_type_idx(*ty);
                        }
                        ObjectField::Oinherit(ty) => {
                            // ty is CoreTypeIdx
                            self.add_core_type_idx(*ty);
                        }
                    }
                }
            }
            CoreTypeDesc::Ptyp_alias(inner) => {
                let (ref ty, ref _name) = **inner;
                // ty is CoreTypeIdx
                let ty = *ty;
                self.add_core_type_idx(ty);
            }
            CoreTypeDesc::Ptyp_variant(inner) => {
                let (ref rows, ref _closed, ref _labels) = **inner;
                for row in rows {
                    match row {
                        RowField::Rtag(_label, _attrs, _bool, tys) => {
                            for ty in tys {
                                // ty is CoreTypeIdx
                                self.add_core_type_idx(*ty);
                            }
                        }
                        RowField::Rinherit(ty) => {
                            // ty is CoreTypeIdx
                            self.add_core_type_idx(*ty);
                        }
                    }
                }
            }
            CoreTypeDesc::Ptyp_poly(inner) => {
                let (ref _names, ref ty) = **inner;
                // ty is CoreTypeIdx
                let ty = *ty;
                self.add_core_type_idx(ty);
            }
            CoreTypeDesc::Ptyp_package(pkg_inner) => {
                let (ref lid, ref constraints) = **pkg_inner;
                self.add_lident_idx(lid.txt);
                for (lid, ty) in constraints {
                    self.add_lident_idx(lid.txt);
                    // ty is CoreTypeIdx
                    self.add_core_type_idx(*ty);
                }
            }
            CoreTypeDesc::Ptyp_extension(_ext_inner) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
        }
    }

    // ========== Modules ==========

    fn add_module_expr(&mut self, me: &ModuleExpr) {
        match &*me.pmod_desc {
            ModuleExprDesc::Pmod_ident(lid) => {
                // Module ident uses full path (OCaml: addmodule)
                self.add_lident_idx_full(lid.txt);
            }
            ModuleExprDesc::Pmod_structure(str) => {
                self.add_structure(str);
            }
            ModuleExprDesc::Pmod_functor(inner) => {
                let (ref name, ref mt, ref body) = **inner;
                if let Some(mt) = mt {
                    // mt is ModTypeIdx
                    let mt = *mt;
                    self.add_mod_type_idx(mt);
                }
                // Bind the functor parameter name so it's not added as a dependency in the body.
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let param_name = self.arena.get_string(name.txt).to_string();
                let newly_added = self.bound_modules.insert(param_name.clone());
                // body is ModExprIdx
                let body = *body;
                self.add_mod_expr_idx(body);
                if newly_added {
                    self.bound_modules.remove(&param_name);
                }
            }
            ModuleExprDesc::Pmod_apply(me1, me2) => {
                // me1 and me2 are ModExprIdx
                let me1 = *me1;
                let me2 = *me2;
                self.add_mod_expr_idx(me1);
                self.add_mod_expr_idx(me2);
            }
            ModuleExprDesc::Pmod_constraint(me, mt) => {
                // me is ModExprIdx, mt is ModTypeIdx
                let me = *me;
                let mt = *mt;
                self.add_mod_expr_idx(me);
                self.add_mod_type_idx(mt);
            }
            ModuleExprDesc::Pmod_unpack(expr) => {
                // expr is ExprIdx
                let expr = *expr;
                self.add_expr_idx(expr);
            }
            ModuleExprDesc::Pmod_extension(_ext_inner) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
        }
    }

    fn add_module_type(&mut self, mt: &ModuleType) {
        match &*mt.pmty_desc {
            ModuleTypeDesc::Pmty_ident(lid) => {
                // Pmty_ident uses add = add_parent (OCaml: add bv l)
                // For simple Lidents like `Tree` or `Intf`, this adds nothing (correct)
                self.add_lident_idx(lid.txt);
            }
            ModuleTypeDesc::Pmty_alias(lid) => {
                // Pmty_alias uses addmodule (full path)
                self.add_lident_idx_full(lid.txt);
            }
            ModuleTypeDesc::Pmty_signature(sig) => {
                self.add_signature(sig);
            }
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref name, ref mt1, ref mt2) = **inner;
                if let Some(mt1) = mt1 {
                    // mt1 is ModTypeIdx
                    let mt1 = *mt1;
                    self.add_mod_type_idx(mt1);
                }
                // Bind the functor parameter name so it's not added as a dependency in the body.
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let param_name = self.arena.get_string(name.txt).to_string();
                let newly_added = self.bound_modules.insert(param_name.clone());
                // mt2 is ModTypeIdx
                let mt2 = *mt2;
                self.add_mod_type_idx(mt2);
                if newly_added {
                    self.bound_modules.remove(&param_name);
                }
            }
            ModuleTypeDesc::Pmty_with(inner) => {
                let (ref mt, ref constraints) = **inner;
                // mt is ModTypeIdx
                let mt = *mt;
                self.add_mod_type_idx(mt);
                for constraint in constraints {
                    self.add_with_constraint(constraint);
                }
            }
            ModuleTypeDesc::Pmty_typeof(me) => {
                // me is ModExprIdx
                let me = *me;
                self.add_mod_expr_idx(me);
            }
            ModuleTypeDesc::Pmty_extension(_ext_inner) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
        }
    }

    fn add_with_constraint(&mut self, constraint: &WithConstraint) {
        match constraint {
            WithConstraint::Pwith_type(_lid, td) | WithConstraint::Pwith_typesubst(_lid, td) => {
                // OCaml: Pwith_type (_, td) -> add_type_declaration bv td
                // Only add dependencies from the type declaration, not the path being constrained
                // lid is the type path being constrained (e.g., `t` in `with type t = string`)
                // which is not an external dependency reference
                self.add_type_declaration(td);
            }
            WithConstraint::Pwith_module(_lid1, lid2)
            | WithConstraint::Pwith_modsubst(_lid1, lid2) => {
                // OCaml: Pwith_module (_, lid) -> addmodule bv lid
                // Only add the right-hand side (lid2) as a dependency
                // lid1 is the path being substituted (e.g., `Bar` in `with module Bar = Array`)
                // which is not an external dependency reference
                self.add_lident_idx_full(lid2.txt);
            }
        }
    }

    // ========== Declarations ==========

    fn add_value_description(&mut self, vd: &ValueDescription) {
        // pval_type is CoreTypeIdx
        self.add_core_type_idx(vd.pval_type);
    }

    fn add_type_declaration(&mut self, td: &TypeDeclaration) {
        for (ty, _variance) in &td.ptype_params {
            // ty is CoreTypeIdx
            self.add_core_type_idx(*ty);
        }
        for (ty1, ty2, _loc) in &td.ptype_cstrs {
            // ty1 and ty2 are CoreTypeIdx
            self.add_core_type_idx(*ty1);
            self.add_core_type_idx(*ty2);
        }
        match &td.ptype_kind {
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
            TypeKind::Ptype_variant(ctors) => {
                for ctor in ctors {
                    self.add_constructor_arguments(&ctor.pcd_args);
                    if let Some(res) = &ctor.pcd_res {
                        // res is CoreTypeIdx
                        self.add_core_type_idx(*res);
                    }
                }
            }
            TypeKind::Ptype_record(fields) => {
                for field in fields {
                    self.add_label_declaration(field);
                }
            }
        }
        if let Some(manifest) = &td.ptype_manifest {
            // manifest is CoreTypeIdx
            self.add_core_type_idx(*manifest);
        }
    }

    fn add_constructor_arguments(&mut self, args: &ConstructorArguments) {
        match args {
            ConstructorArguments::Pcstr_tuple(tys) => {
                for ty in tys {
                    // ty is CoreTypeIdx
                    self.add_core_type_idx(*ty);
                }
            }
            ConstructorArguments::Pcstr_record(fields) => {
                for field in fields {
                    self.add_label_declaration(field);
                }
            }
        }
    }

    fn add_label_declaration(&mut self, ld: &LabelDeclaration) {
        // pld_type is CoreTypeIdx
        self.add_core_type_idx(ld.pld_type);
    }

    fn add_type_extension(&mut self, te: &TypeExtension) {
        self.add_lident_idx(te.ptyext_path.txt);
        for (ty, _variance) in &te.ptyext_params {
            // ty is CoreTypeIdx
            self.add_core_type_idx(*ty);
        }
        for ctor in &te.ptyext_constructors {
            self.add_extension_constructor(ctor);
        }
    }

    fn add_extension_constructor(&mut self, ec: &ExtensionConstructor) {
        match &ec.pext_kind {
            ExtensionConstructorKind::Pext_decl(args, res) => {
                self.add_constructor_arguments(args);
                if let Some(res) = res {
                    // res is CoreTypeIdx
                    self.add_core_type_idx(*res);
                }
            }
            ExtensionConstructorKind::Pext_rebind(lid) => {
                self.add_lident_idx(lid.txt);
            }
        }
    }

    fn add_module_binding(&mut self, mb: &ModuleBinding) {
        // pmb_expr is ModExprIdx
        self.add_mod_expr_idx(mb.pmb_expr);
    }

    fn add_module_declaration(&mut self, md: &ModuleDeclaration) {
        // pmd_type is ModTypeIdx
        self.add_mod_type_idx(md.pmd_type);
    }

    fn add_module_type_declaration(&mut self, mtd: &ModuleTypeDeclaration) {
        if let Some(mt) = &mtd.pmtd_type {
            // mt is ModTypeIdx
            self.add_mod_type_idx(*mt);
        }
    }

    fn add_open_description(&mut self, od: &OpenDescription) {
        // Open uses full module path (like `open Array`)
        self.add_lident_idx_full(od.popen_lid.txt);
        let _ = self.bind_opened_members(od.popen_lid.txt);
    }

    fn add_include_declaration(&mut self, id: &IncludeDeclaration) {
        // pincl_mod is ModExprIdx
        self.add_mod_expr_idx(id.pincl_mod);
    }

    fn add_include_description(&mut self, id: &IncludeDescription) {
        // pincl_mod is ModTypeIdx
        self.add_mod_type_idx(id.pincl_mod);
    }

    fn add_case(&mut self, case: &Case) {
        // OCaml: let bv = add_pattern bv pc_lhs in
        // Collect unpack names from pattern for guard and rhs,
        // then remove them after processing (OCaml scopes bv functionally)
        // pc_lhs is PatIdx
        let unpack_names = self.add_pat_idx_collecting_unpack(case.pc_lhs);
        // Only track names that are NEWLY added (not already bound) to avoid
        // removing outer bindings when the scope exits.
        let newly_added: Vec<String> = unpack_names
            .into_iter()
            .filter(|name| self.bound_modules.insert(name.clone()))
            .collect();
        if let Some(guard) = &case.pc_guard {
            // guard is ExprIdx
            self.add_expr_idx(*guard);
        }
        // pc_rhs is ExprIdx
        self.add_expr_idx(case.pc_rhs);
        for name in &newly_added {
            self.bound_modules.remove(name);
        }
    }

    fn add_payload(&mut self, payload: &Payload) {
        match payload {
            Payload::PStr(str) => {
                self.add_structure(str);
            }
            Payload::PSig(sig) => {
                self.add_signature(sig);
            }
            Payload::PTyp(ty) => {
                // ty is CoreTypeIdx
                let ty = *ty;
                self.add_core_type_idx(ty);
            }
            Payload::PPat(inner) => {
                let (ref pat, ref guard) = **inner;
                // pat is PatIdx, guard is Option<ExprIdx>
                let pat = *pat;
                self.add_pat_idx(pat);
                if let Some(guard) = guard {
                    let guard = *guard;
                    self.add_expr_idx(guard);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_arena::{LocIdx, Located};

    /// Parse a dotted string like "Foo.Bar.baz" into a Longident using the arena.
    fn parse_longident(arena: &mut ParseArena, s: &str) -> Longident {
        let parts: Vec<&str> = s.split('.').collect();
        let mut lid = Longident::Lident(arena.intern_string(parts[0]));
        for part in &parts[1..] {
            lid = Longident::Ldot(Box::new(lid), arena.intern_string(part));
        }
        lid
    }

    fn make_ident_expr(arena: &mut ParseArena, lid: Longident) -> ExprIdx {
        let lid_idx = arena.push_longident(lid);
        let expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: lid_idx,
                loc: LocIdx::none(),
            })),
            pexp_loc: LocIdx::none(),
            pexp_attributes: Attributes::new(),
        };
        arena.push_expr(expr)
    }

    fn make_eval_item(expr_idx: ExprIdx) -> StructureItem {
        StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
                expr_idx,
                Attributes::new(),
            )))),
            pstr_loc: LocIdx::none(),
        }
    }

    #[test]
    fn test_simple_module_reference() {
        // Test: Array.map extracts "Array"
        let mut arena = ParseArena::default();
        let lid = parse_longident(&mut arena, "Array.map");
        let expr_idx = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr_idx)];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
    }

    #[test]
    fn test_nested_module_reference() {
        // Test: Belt.Array.map extracts "Belt"
        let mut arena = ParseArena::default();
        let lid = parse_longident(&mut arena, "Belt.Array.map");
        let expr_idx = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr_idx)];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Belt"));
    }

    #[test]
    fn test_lowercase_identifier_ignored() {
        // Test: lowercase identifiers are not module references
        let mut arena = ParseArena::default();
        let foo_idx = arena.intern_string("foo");
        let lid = Longident::lident(foo_idx);
        let expr_idx = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr_idx)];

        let deps = extract_structure_deps(&arena, &structure);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_uppercase_simple_identifier_ignored() {
        // Test: Simple uppercase identifiers like `None` or `Some` are NOT module references
        // OCaml's add_parent only adds the parent of dotted paths, not simple Lidents
        let mut arena = ParseArena::default();
        let none_idx = arena.intern_string("None");
        let lid = Longident::lident(none_idx);
        let expr_idx = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr_idx)];

        let deps = extract_structure_deps(&arena, &structure);
        // None is a simple identifier, not Foo.None, so it's not a module reference
        assert!(
            deps.is_empty(),
            "Simple uppercase identifier 'None' should not be a dependency"
        );
    }

    #[test]
    fn test_multiple_modules() {
        // Test: multiple module references are collected
        let mut arena = ParseArena::default();
        let lid1 = parse_longident(&mut arena, "Array.map");
        let lid2 = parse_longident(&mut arena, "Belt.Array.get");
        let lid3 = parse_longident(&mut arena, "Js.log");
        let e1 = make_ident_expr(&mut arena, lid1);
        let e2 = make_ident_expr(&mut arena, lid2);
        let e3 = make_ident_expr(&mut arena, lid3);
        let structure = vec![make_eval_item(e1), make_eval_item(e2), make_eval_item(e3)];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 3);
        assert!(deps.contains("Array"));
        assert!(deps.contains("Belt"));
        assert!(deps.contains("Js"));
    }

    #[test]
    fn test_sorted_output() {
        // Test: output is sorted alphabetically
        let mut arena = ParseArena::default();
        let lid1 = parse_longident(&mut arena, "Zebra.x");
        let lid2 = parse_longident(&mut arena, "Alpha.y");
        let lid3 = parse_longident(&mut arena, "Middle.z");
        let e1 = make_ident_expr(&mut arena, lid1);
        let e2 = make_ident_expr(&mut arena, lid2);
        let e3 = make_ident_expr(&mut arena, lid3);
        let structure = vec![make_eval_item(e1), make_eval_item(e2), make_eval_item(e3)];

        let deps = extract_structure_deps(&arena, &structure);
        let deps_vec: Vec<_> = deps.into_iter().collect();
        assert_eq!(deps_vec, vec!["Alpha", "Middle", "Zebra"]);
    }

    #[test]
    fn test_predef_filtered() {
        // Test: *predef* is filtered out
        let arena = ParseArena::default();
        let mut collector = DependencyCollector::new(&arena);
        collector.deps.insert("*predef*".to_string());
        collector.deps.insert("Array".to_string());

        let deps = collector.finish();
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
        assert!(!deps.contains("*predef*"));
    }

    #[test]
    fn test_empty_string_filtered() {
        // Test: empty strings are filtered out
        let arena = ParseArena::default();
        let mut collector = DependencyCollector::new(&arena);
        collector.deps.insert(String::new());
        collector.deps.insert("Array".to_string());

        let deps = collector.finish();
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
    }

    #[test]
    fn test_deduplicated() {
        // Test: duplicate modules are deduplicated
        let mut arena = ParseArena::default();
        let lid1 = parse_longident(&mut arena, "Array.map");
        let lid2 = parse_longident(&mut arena, "Array.length");
        let lid3 = parse_longident(&mut arena, "Array.get");
        let e1 = make_ident_expr(&mut arena, lid1);
        let e2 = make_ident_expr(&mut arena, lid2);
        let e3 = make_ident_expr(&mut arena, lid3);
        let structure = vec![make_eval_item(e1), make_eval_item(e2), make_eval_item(e3)];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
    }

    #[test]
    fn test_nested_module_bindings_do_not_leak_to_outer_scope() {
        let source = r#"
module Stdlib = {
  module Array = {
    let x = 1
  }
}

let y = Array.length
"#;
        let mut parser = crate::parser::state::Parser::new("scope.res", source);
        let structure = crate::parser::module::parse_structure(&mut parser);
        let arena = parser.into_arena();

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
    }

    #[test]
    fn test_open_brings_local_submodules_into_scope() {
        let source = r#"
module Stdlib = {
  module Type = {
    let typeof = x => x
  }
}

open Stdlib
let y = Type.typeof
"#;
        let mut parser = crate::parser::state::Parser::new("open_scope.res", source);
        let structure = crate::parser::module::parse_structure(&mut parser);
        let arena = parser.into_arena();

        let deps = extract_structure_deps(&arena, &structure);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_empty_structure() {
        let arena = ParseArena::default();
        let deps = extract_structure_deps(&arena, &[]);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_empty_signature() {
        let arena = ParseArena::default();
        let deps = extract_signature_deps(&arena, &[]);
        assert!(deps.is_empty());
    }
}
