//! Module dependency extraction from AST
//!
//! This module provides functionality to extract module dependencies from
//! ReScript AST, matching the OCaml implementation in `compiler/frontend/ast_extract.ml`.
//!
//! Dependencies are extracted by walking the AST and collecting all module references
//! from Longidents. Only uppercase module names are collected (lowercase names are
//! local bindings, not module references).

use std::collections::{BTreeSet, HashSet};

use crate::parser::ast::{
    Case, ConstructorArguments, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExtensionConstructor, ExtensionConstructorKind, IncludeDeclaration, IncludeDescription,
    LabelDeclaration, ModuleBinding, ModuleDeclaration, ModuleExpr, ModuleExprDesc, ModuleType,
    ModuleTypeDeclaration, ModuleTypeDesc, ObjectField, OpenDescription, Pattern, PatternDesc,
    Payload, RowField, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc,
    TypeDeclaration, TypeExtension, TypeKind, ValueBinding, ValueDescription, WithConstraint,
};
use crate::parse_arena::{LidentIdx, ParseArena};
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
}

impl<'a> DependencyCollector<'a> {
    fn new(arena: &'a ParseArena) -> Self {
        Self {
            arena,
            deps: BTreeSet::new(),
            bound_modules: HashSet::new(),
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
            if first_str.chars().next().is_some_and(|c| c.is_ascii_uppercase())
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

    // ========== Structure ==========

    fn add_structure(&mut self, structure: &[StructureItem]) {
        for item in structure {
            self.add_structure_item(item);
        }
    }

    fn add_structure_item(&mut self, item: &StructureItem) {
        match &*item.pstr_desc {
            StructureItemDesc::Pstr_eval(expr, _attrs) => {
                self.add_expression(expr);
            }
            StructureItemDesc::Pstr_value(_rec_flag, bindings) => {
                // OCaml's add_bindings collects pattern bindings (including Ppat_unpack)
                // and adds them to bound_modules so later references don't add dependencies.
                // First collect all unpack names from patterns
                let mut unpack_names = HashSet::new();
                for binding in bindings {
                    let names = self.add_pattern_collecting_unpack(&binding.pvb_pat);
                    unpack_names.extend(names);
                }
                // Add collected unpack names to bound_modules
                // This must happen before processing expressions so that references
                // to these modules in the same or later bindings don't add dependencies
                self.bound_modules.extend(unpack_names);
                // Now process expressions
                for binding in bindings {
                    self.add_expression(&binding.pvb_expr);
                }
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                self.add_value_description(vd);
            }
            StructureItemDesc::Pstr_type(_rec_flag, decls) => {
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
                // Process the module body FIRST (before binding the name), so that
                // references inside the body to a module with the same name are
                // treated as external dependencies. E.g., `module List = { include List }`
                // should add "List" as a dep from the `include List`.
                let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                self.add_module_binding(mb);
                self.bound_modules.insert(module_name);
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                // First bind all module names so they're not added as dependencies
                for mb in mbs {
                    let module_name = self.arena.get_string(mb.pmb_name.txt).to_string();
                    self.bound_modules.insert(module_name);
                }
                // Then process all module expressions
                for mb in mbs {
                    self.add_module_binding(mb);
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
            StructureItemDesc::Pstr_extension((_id, _payload), _attrs) => {
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
            SignatureItemDesc::Psig_type(_rec_flag, decls) => {
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
                self.add_module_declaration(md);
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                // First bind all module names
                for md in mds {
                    let module_name = self.arena.get_string(md.pmd_name.txt).to_string();
                    self.bound_modules.insert(module_name);
                }
                // Then process all module declarations
                for md in mds {
                    self.add_module_declaration(md);
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
            SignatureItemDesc::Psig_extension((_id, _payload), _attrs) => {
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
            ExpressionDesc::Pexp_let(_rec_flag, bindings, body) => {
                // OCaml's add_bindings collects pattern bindings (including Ppat_unpack)
                // First collect all unpack names from patterns
                let mut unpack_names = HashSet::new();
                for binding in bindings {
                    let names = self.add_pattern_collecting_unpack(&binding.pvb_pat);
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
                    self.add_expression(&binding.pvb_expr);
                }
                self.add_expression(body);
                for name in &newly_added {
                    self.bound_modules.remove(name);
                }
            }
            ExpressionDesc::Pexp_fun {
                default,
                lhs,
                rhs,
                ..
            } => {
                if let Some(default) = default {
                    self.add_expression(default);
                }
                // OCaml: add_expr (add_pattern bv p) e
                // Collect unpack names from pattern and add to bound_modules for rhs,
                // then remove them after processing (OCaml scopes bv functionally)
                let unpack_names = self.add_pattern_collecting_unpack(lhs);
                // Only track names that are NEWLY added (not already bound) to avoid
                // removing outer bindings when the scope exits.
                let newly_added: Vec<String> = unpack_names
                    .into_iter()
                    .filter(|name| self.bound_modules.insert(name.clone()))
                    .collect();
                self.add_expression(rhs);
                for name in &newly_added {
                    self.bound_modules.remove(name);
                }
            }
            ExpressionDesc::Pexp_apply { funct, args, .. } => {
                self.add_expression(funct);
                for (_label, arg) in args {
                    self.add_expression(arg);
                }
            }
            ExpressionDesc::Pexp_match(expr, cases) | ExpressionDesc::Pexp_try(expr, cases) => {
                self.add_expression(expr);
                for case in cases {
                    self.add_case(case);
                }
            }
            ExpressionDesc::Pexp_tuple(exprs) | ExpressionDesc::Pexp_array(exprs) => {
                for expr in exprs {
                    self.add_expression(expr);
                }
            }
            ExpressionDesc::Pexp_construct(lid, arg) => {
                self.add_lident_idx(lid.txt);
                if let Some(arg) = arg {
                    self.add_expression(arg);
                }
            }
            ExpressionDesc::Pexp_variant(_label, arg) => {
                if let Some(arg) = arg {
                    self.add_expression(arg);
                }
            }
            ExpressionDesc::Pexp_record(fields, spread) => {
                for field in fields {
                    self.add_lident_idx(field.lid.txt);
                    self.add_expression(&field.expr);
                }
                if let Some(spread) = spread {
                    self.add_expression(spread);
                }
            }
            ExpressionDesc::Pexp_field(expr, lid) => {
                self.add_expression(expr);
                self.add_lident_idx(lid.txt);
            }
            ExpressionDesc::Pexp_setfield(expr1, lid, expr2) => {
                self.add_expression(expr1);
                self.add_lident_idx(lid.txt);
                self.add_expression(expr2);
            }
            ExpressionDesc::Pexp_ifthenelse(cond, then_expr, else_expr) => {
                self.add_expression(cond);
                self.add_expression(then_expr);
                if let Some(else_expr) = else_expr {
                    self.add_expression(else_expr);
                }
            }
            ExpressionDesc::Pexp_sequence(e1, e2) => {
                self.add_expression(e1);
                self.add_expression(e2);
            }
            ExpressionDesc::Pexp_while(cond, body) => {
                self.add_expression(cond);
                self.add_expression(body);
            }
            ExpressionDesc::Pexp_for(_pat, start, end, _dir, body) => {
                // OCaml: Pexp_for (_, e1, e2, _, e3) - ignores the pattern
                // The for-loop pattern doesn't add dependencies
                self.add_expression(start);
                self.add_expression(end);
                self.add_expression(body);
            }
            ExpressionDesc::Pexp_constraint(expr, ty) => {
                self.add_expression(expr);
                self.add_core_type(ty);
            }
            ExpressionDesc::Pexp_coerce(expr, ty1, ty2) => {
                self.add_expression(expr);
                if let Some(ty1) = ty1 {
                    self.add_core_type(ty1);
                }
                self.add_core_type(ty2);
            }
            ExpressionDesc::Pexp_send(expr, _label) => {
                self.add_expression(expr);
            }
            ExpressionDesc::Pexp_letmodule(name, me, body) => {
                // Bind the module name so it's not added as a dependency
                let module_name = self.arena.get_string(name.txt).to_string();
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let newly_added = self.bound_modules.insert(module_name.clone());
                self.add_module_expr(me);
                self.add_expression(body);
                if newly_added {
                    self.bound_modules.remove(&module_name);
                }
            }
            ExpressionDesc::Pexp_letexception(ext_ctor, body) => {
                self.add_extension_constructor(ext_ctor);
                self.add_expression(body);
            }
            ExpressionDesc::Pexp_assert(expr) => {
                self.add_expression(expr);
            }
            ExpressionDesc::Pexp_newtype(_name, body) => {
                self.add_expression(body);
            }
            ExpressionDesc::Pexp_pack(me) => {
                self.add_module_expr(me);
            }
            ExpressionDesc::Pexp_open(_override, lid, body) => {
                // Local open uses full module path
                self.add_lident_idx_full(lid.txt);
                self.add_expression(body);
            }
            ExpressionDesc::Pexp_extension((_id, _payload)) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
            ExpressionDesc::Pexp_await(expr) => {
                self.add_expression(expr);
            }
            ExpressionDesc::Pexp_jsx_element(jsx) => {
                self.add_jsx_element(jsx);
            }
        }
    }

    fn add_jsx_element(&mut self, jsx: &crate::parser::ast::JsxElement) {
        use crate::parser::ast::{JsxElement, JsxTagName};

        match jsx {
            JsxElement::Fragment(frag) => {
                for child in &frag.children {
                    self.add_expression(child);
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
                    self.add_expression(child);
                }
            }
        }
    }

    fn add_jsx_prop(&mut self, prop: &crate::parser::ast::JsxProp) {
        use crate::parser::ast::JsxProp;
        match prop {
            JsxProp::Punning { .. } => {}
            JsxProp::Value { value, .. } => {
                self.add_expression(value);
            }
            JsxProp::Spreading { expr, .. } => {
                self.add_expression(expr);
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
            PatternDesc::Ppat_alias(pat, _name) => {
                self.add_pattern_inner(pat, unpack_names);
            }
            PatternDesc::Ppat_interval(_, _) => {}
            PatternDesc::Ppat_tuple(pats) | PatternDesc::Ppat_array(pats) => {
                for pat in pats {
                    self.add_pattern_inner(pat, unpack_names);
                }
            }
            PatternDesc::Ppat_construct(lid, arg) => {
                self.add_lident_idx(lid.txt);
                if let Some(arg) = arg {
                    self.add_pattern_inner(arg, unpack_names);
                }
            }
            PatternDesc::Ppat_variant(_label, arg) => {
                if let Some(arg) = arg {
                    self.add_pattern_inner(arg, unpack_names);
                }
            }
            PatternDesc::Ppat_record(fields, _closed) => {
                for field in fields {
                    self.add_lident_idx(field.lid.txt);
                    self.add_pattern_inner(&field.pat, unpack_names);
                }
            }
            PatternDesc::Ppat_or(p1, p2) => {
                self.add_pattern_inner(p1, unpack_names);
                self.add_pattern_inner(p2, unpack_names);
            }
            PatternDesc::Ppat_constraint(pat, ty) => {
                self.add_pattern_inner(pat, unpack_names);
                self.add_core_type(ty);
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
            PatternDesc::Ppat_exception(pat) => {
                self.add_pattern_inner(pat, unpack_names);
            }
            PatternDesc::Ppat_extension((_id, _payload)) => {
                // OCaml's handle_extension ignores extension payloads for dependency extraction
            }
            PatternDesc::Ppat_open(lid, pat) => {
                // Pattern open uses full module path
                self.add_lident_idx_full(lid.txt);
                self.add_pattern_inner(pat, unpack_names);
            }
        }
    }

    // ========== Core Types ==========

    fn add_core_type(&mut self, ty: &CoreType) {
        match &*ty.ptyp_desc {
            CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => {}
            CoreTypeDesc::Ptyp_arrow { arg, ret, .. } => {
                self.add_core_type(&arg.typ);
                self.add_core_type(ret);
            }
            CoreTypeDesc::Ptyp_tuple(tys) => {
                for ty in tys {
                    self.add_core_type(ty);
                }
            }
            CoreTypeDesc::Ptyp_constr(lid, args) => {
                self.add_lident_idx(lid.txt);
                for arg in args {
                    self.add_core_type(arg);
                }
            }
            CoreTypeDesc::Ptyp_object(fields, _closed) => {
                for field in fields {
                    match field {
                        ObjectField::Otag(_label, _attrs, ty) => {
                            self.add_core_type(ty);
                        }
                        ObjectField::Oinherit(ty) => {
                            self.add_core_type(ty);
                        }
                    }
                }
            }
            CoreTypeDesc::Ptyp_alias(ty, _name) => {
                self.add_core_type(ty);
            }
            CoreTypeDesc::Ptyp_variant(rows, _closed, _labels) => {
                for row in rows {
                    match row {
                        RowField::Rtag(_label, _attrs, _bool, tys) => {
                            for ty in tys {
                                self.add_core_type(ty);
                            }
                        }
                        RowField::Rinherit(ty) => {
                            self.add_core_type(ty);
                        }
                    }
                }
            }
            CoreTypeDesc::Ptyp_poly(_names, ty) => {
                self.add_core_type(ty);
            }
            CoreTypeDesc::Ptyp_package((lid, constraints)) => {
                self.add_lident_idx(lid.txt);
                for (lid, ty) in constraints {
                    self.add_lident_idx(lid.txt);
                    self.add_core_type(ty);
                }
            }
            CoreTypeDesc::Ptyp_extension((_id, _payload)) => {
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
            ModuleExprDesc::Pmod_functor(name, mt, body) => {
                if let Some(mt) = mt {
                    self.add_module_type(mt);
                }
                // Bind the functor parameter name so it's not added as a dependency in the body.
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let param_name = self.arena.get_string(name.txt).to_string();
                let newly_added = self.bound_modules.insert(param_name.clone());
                self.add_module_expr(body);
                if newly_added {
                    self.bound_modules.remove(&param_name);
                }
            }
            ModuleExprDesc::Pmod_apply(me1, me2) => {
                self.add_module_expr(me1);
                self.add_module_expr(me2);
            }
            ModuleExprDesc::Pmod_constraint(me, mt) => {
                self.add_module_expr(me);
                self.add_module_type(mt);
            }
            ModuleExprDesc::Pmod_unpack(expr) => {
                self.add_expression(expr);
            }
            ModuleExprDesc::Pmod_extension((_id, _payload)) => {
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
            ModuleTypeDesc::Pmty_functor(name, mt1, mt2) => {
                if let Some(mt1) = mt1 {
                    self.add_module_type(mt1);
                }
                // Bind the functor parameter name so it's not added as a dependency in the body.
                // Only track as newly added if not already bound, to avoid
                // removing outer bindings when the scope exits.
                let param_name = self.arena.get_string(name.txt).to_string();
                let newly_added = self.bound_modules.insert(param_name.clone());
                self.add_module_type(mt2);
                if newly_added {
                    self.bound_modules.remove(&param_name);
                }
            }
            ModuleTypeDesc::Pmty_with(mt, constraints) => {
                self.add_module_type(mt);
                for constraint in constraints {
                    self.add_with_constraint(constraint);
                }
            }
            ModuleTypeDesc::Pmty_typeof(me) => {
                self.add_module_expr(me);
            }
            ModuleTypeDesc::Pmty_extension((_id, _payload)) => {
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

    fn add_value_binding(&mut self, vb: &ValueBinding) {
        self.add_pattern(&vb.pvb_pat);
        self.add_expression(&vb.pvb_expr);
    }

    fn add_value_description(&mut self, vd: &ValueDescription) {
        self.add_core_type(&vd.pval_type);
    }

    fn add_type_declaration(&mut self, td: &TypeDeclaration) {
        for (ty, _variance) in &td.ptype_params {
            self.add_core_type(ty);
        }
        for (ty1, ty2, _loc) in &td.ptype_cstrs {
            self.add_core_type(ty1);
            self.add_core_type(ty2);
        }
        match &td.ptype_kind {
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
            TypeKind::Ptype_variant(ctors) => {
                for ctor in ctors {
                    self.add_constructor_arguments(&ctor.pcd_args);
                    if let Some(res) = &ctor.pcd_res {
                        self.add_core_type(res);
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
            self.add_core_type(manifest);
        }
    }

    fn add_constructor_arguments(&mut self, args: &ConstructorArguments) {
        match args {
            ConstructorArguments::Pcstr_tuple(tys) => {
                for ty in tys {
                    self.add_core_type(ty);
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
        self.add_core_type(&ld.pld_type);
    }

    fn add_type_extension(&mut self, te: &TypeExtension) {
        self.add_lident_idx(te.ptyext_path.txt);
        for (ty, _variance) in &te.ptyext_params {
            self.add_core_type(ty);
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
                    self.add_core_type(res);
                }
            }
            ExtensionConstructorKind::Pext_rebind(lid) => {
                self.add_lident_idx(lid.txt);
            }
        }
    }

    fn add_module_binding(&mut self, mb: &ModuleBinding) {
        self.add_module_expr(&mb.pmb_expr);
    }

    fn add_module_declaration(&mut self, md: &ModuleDeclaration) {
        self.add_module_type(&md.pmd_type);
    }

    fn add_module_type_declaration(&mut self, mtd: &ModuleTypeDeclaration) {
        if let Some(mt) = &mtd.pmtd_type {
            self.add_module_type(mt);
        }
    }

    fn add_open_description(&mut self, od: &OpenDescription) {
        // Open uses full module path (like `open Array`)
        self.add_lident_idx_full(od.popen_lid.txt);
    }

    fn add_include_declaration(&mut self, id: &IncludeDeclaration) {
        self.add_module_expr(&id.pincl_mod);
    }

    fn add_include_description(&mut self, id: &IncludeDescription) {
        self.add_module_type(&id.pincl_mod);
    }

    fn add_case(&mut self, case: &Case) {
        // OCaml: let bv = add_pattern bv pc_lhs in
        // Collect unpack names from pattern for guard and rhs,
        // then remove them after processing (OCaml scopes bv functionally)
        let unpack_names = self.add_pattern_collecting_unpack(&case.pc_lhs);
        // Only track names that are NEWLY added (not already bound) to avoid
        // removing outer bindings when the scope exits.
        let newly_added: Vec<String> = unpack_names
            .into_iter()
            .filter(|name| self.bound_modules.insert(name.clone()))
            .collect();
        if let Some(guard) = &case.pc_guard {
            self.add_expression(guard);
        }
        self.add_expression(&case.pc_rhs);
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
                self.add_core_type(ty);
            }
            Payload::PPat(pat, guard) => {
                self.add_pattern(pat);
                if let Some(guard) = guard {
                    self.add_expression(guard);
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

    fn make_ident_expr(arena: &mut ParseArena, lid: Longident) -> Expression {
        let lid_idx = arena.push_longident(lid);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: lid_idx,
                loc: LocIdx::none(),
            })),
            pexp_loc: LocIdx::none(),
            pexp_attributes: vec![],
        }
    }

    fn make_eval_item(expr: Expression) -> StructureItem {
        StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_eval(expr, vec![])),
            pstr_loc: LocIdx::none(),
        }
    }

    #[test]
    fn test_simple_module_reference() {
        // Test: Array.map extracts "Array"
        let mut arena = ParseArena::default();
        let lid = parse_longident(&mut arena, "Array.map");
        let expr = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr)];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
    }

    #[test]
    fn test_nested_module_reference() {
        // Test: Belt.Array.map extracts "Belt"
        let mut arena = ParseArena::default();
        let lid = parse_longident(&mut arena, "Belt.Array.map");
        let expr = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr)];

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
        let expr = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr)];

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
        let expr = make_ident_expr(&mut arena, lid);
        let structure = vec![make_eval_item(expr)];

        let deps = extract_structure_deps(&arena, &structure);
        // None is a simple identifier, not Foo.None, so it's not a module reference
        assert!(deps.is_empty(), "Simple uppercase identifier 'None' should not be a dependency");
    }

    #[test]
    fn test_multiple_modules() {
        // Test: multiple module references are collected
        let mut arena = ParseArena::default();
        let lid1 = parse_longident(&mut arena, "Array.map");
        let lid2 = parse_longident(&mut arena, "Belt.Array.get");
        let lid3 = parse_longident(&mut arena, "Js.log");
        let structure = vec![
            make_eval_item(make_ident_expr(&mut arena, lid1)),
            make_eval_item(make_ident_expr(&mut arena, lid2)),
            make_eval_item(make_ident_expr(&mut arena, lid3)),
        ];

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
        let structure = vec![
            make_eval_item(make_ident_expr(&mut arena, lid1)),
            make_eval_item(make_ident_expr(&mut arena, lid2)),
            make_eval_item(make_ident_expr(&mut arena, lid3)),
        ];

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
        let structure = vec![
            make_eval_item(make_ident_expr(&mut arena, lid1)),
            make_eval_item(make_ident_expr(&mut arena, lid2)),
            make_eval_item(make_ident_expr(&mut arena, lid3)),
        ];

        let deps = extract_structure_deps(&arena, &structure);
        assert_eq!(deps.len(), 1);
        assert!(deps.contains("Array"));
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
