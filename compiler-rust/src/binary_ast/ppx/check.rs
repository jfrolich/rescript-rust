//! The errors of the builtin PPX (`Bs_builtin_ppx.mapper`,
//! compiler/frontend/bs_builtin_ppx.ml:812-834), raised in the order the OCaml
//! mapper visits the tree.
//!
//! The mapper is `Ast_mapper.default_mapper` (compiler/ml/ast_mapper.ml) with
//! the builtin overrides. Its traversal order follows OCaml's evaluation
//! order: a node's attributes are mapped first, then the arguments of the
//! rebuilt constructor, function application or record right to left, while
//! `List.map`/`Ext_list.map` visit lists left to right and `Ext_list.fold_right`
//! right to left. Labelled arguments are evaluated in the order of the
//! function's parameters, whatever their order at the call: `Mb.mk name expr
//! ~attrs ~loc` (`Mb.mk ?loc ?attrs name expr`, ast_helper.ml:433) maps the
//! module expression before the attributes.
//!
//! The warnings the mapper prints (`Location.prerr_warning`) are collected in
//! the same walk, so only those emitted before the first error are reported.

use super::*;
use crate::parser::ast::{Extension, ModuleBinding, ModuleTypeDeclaration};

pub(super) struct Checker<'a> {
    arena: &'a mut ParseArena,
    /// `async_context` (bs_builtin_ppx.ml:815): whether `await` is allowed.
    async_context: bool,
    /// `Experimental_features.is_enabled LetUnwrap`, which decides the error
    /// a `let?` binding raises (bs_builtin_ppx.ml:273, 366, 565).
    let_unwrap: bool,
    /// Warnings emitted so far, in mapping order.
    pub(super) warnings: Vec<PpxWarning>,
}

impl<'a> Checker<'a> {
    pub(super) fn new(arena: &'a mut ParseArena) -> Self {
        let let_unwrap = arena.experimental_let_unwrap();
        Self {
            arena,
            async_context: true,
            let_unwrap,
            warnings: Vec::new(),
        }
    }

    // ------------------------------------------------------------------
    // Structures and signatures
    // ------------------------------------------------------------------

    /// `Bs_builtin_ppx.structure_mapper` (bs_builtin_ppx.ml:677-810).
    pub(super) fn structure(&mut self, items: &[StructureItem]) -> PpxResult<()> {
        // bs_builtin_ppx.ml:770-777: `module M = await List` may be in a
        // functor body or a module in a function, so `structure_mapper`
        // checks it against the async context when it reaches the item,
        // which is constant over the structure. That is after the items
        // before it that are mapped head first, and before every other item.
        let awaited = if self.async_context {
            None
        } else {
            items.iter().position(|item| {
                matches!(&item.pstr_desc, StructureItemDesc::Pstr_module(mb)
                    if awaited_module_path_kind(self.arena.get_mod_expr(mb.pmb_expr), self.arena)
                        .is_some())
            })
        };
        for index in structure_mapper_order(items, self.arena) {
            if let Some(awaited) = awaited
                && !(index < awaited && structure_mapper_maps_head_first(&items[index], self.arena))
            {
                let StructureItemDesc::Pstr_module(mb) = &items[awaited].pstr_desc else {
                    unreachable!("the awaited item is a module binding")
                };
                return Err(PpxError::at_loc(
                    self.arena.get_mod_expr(mb.pmb_expr).pmod_loc,
                    AWAIT_NOT_ASYNC_CONTEXT_ERROR,
                ));
            }
            self.structure_mapper_item(&items[index])?;
        }
        Ok(())
    }

    /// The work `structure_mapper` does for one item of the structure.
    pub(super) fn structure_mapper_item(&mut self, item: &StructureItem) -> PpxResult<()> {
        // bs_builtin_ppx.ml structure_mapper `Pstr_raw`.
        if let StructureItemDesc::Pstr_raw(raw) = &item.pstr_desc {
            check_raw_structure_node(raw, self.arena, &mut self.warnings);
            return Ok(());
        }
        if let StructureItemDesc::Pstr_extension(inner) = &item.pstr_desc {
            let ((ext_name, payload), _attrs) = &**inner;
            match self.arena.get_string(ext_name.txt) {
                // `Ast_exp_handle_external.handle_raw_structure`: the Flow
                // parse of a string payload warns about its errors.
                "raw" => {
                    validate_structure_extension_payload_error(&inner.0, self.arena)?;
                    push_raw_js_program_warning(payload, self.arena, &mut self.warnings);
                    return Ok(());
                }
                // `aux` maps each payload item with `self.structure_item`.
                "private" => {
                    for work in private_extension_structure_items(payload, ext_name.loc)? {
                        self.structure_item(work)?;
                    }
                    return Ok(());
                }
                _ => {}
            }
        }
        self.structure_item(item)
    }

    /// `Bs_builtin_ppx.structure_item_mapper` (bs_builtin_ppx.ml:513-637).
    fn structure_item(&mut self, item: &StructureItem) -> PpxResult<()> {
        // bs_builtin_ppx.ml:556-571: a top-level `let?` binding is an error.
        if let StructureItemDesc::Pstr_value(inner) = &item.pstr_desc
            && let Some(vb) = self
                .arena
                .vb_list(inner.1)
                .iter()
                .find(|vb| has_unwrap_attr(&vb.pvb_attributes, self.arena))
        {
            let loc = self.arena.get_pat(vb.pvb_pat).ppat_loc;
            let message = if self.let_unwrap {
                LET_UNWRAP_TOPLEVEL_ERROR
            } else {
                LET_UNWRAP_NOT_ENABLED_ERROR
            };
            return Err(PpxError::at_loc(loc, message));
        }
        match &item.pstr_desc {
            // A plan holds no syntax to check.
            StructureItemDesc::Pstr_derived(_) => Ok(()),
            StructureItemDesc::Pstr_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                self.type_declarations_with_deriving(tdcls, true)
            }
            StructureItemDesc::Pstr_primitive(vd)
                if is_rs_external(&vd.pval_attributes, &vd.pval_prim, self.arena) =>
            {
                self.external(vd)
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (rec_flag, bindings) = inner;
                let bindings = self.arena.vb_list(*bindings).to_vec();
                match (rec_flag, bindings.as_slice()) {
                    (RecFlag::Nonrecursive, [vb])
                        if matches!(
                            &self.arena.get_pat(vb.pvb_pat).ppat_desc,
                            PatternDesc::Ppat_var(_)
                        ) && self.arena.value_constraint(vb.pvb_pat).is_none() =>
                    {
                        // bs_builtin_ppx.ml:553-554: the expression, then the
                        // attributes; the pattern is not mapped.
                        self.expr(vb.pvb_expr)?;
                        self.attributes(&vb.pvb_attributes)?;
                        // bs_builtin_ppx.ml:590-601: an `@inline` string
                        // binding reads the expression's semantic string.
                        if find_inline_payload_expr(&vb.pvb_attributes, self.arena).is_some() {
                            let expr = self.arena.get_expr(vb.pvb_expr);
                            inline_string_semantic(
                                crate::ast_payload::unwrap_braces(self.arena, expr),
                                self.arena,
                            )?;
                        }
                        Ok(())
                    }
                    (RecFlag::Nonrecursive, _) => self.value_bindings_flattened(&bindings),
                    (RecFlag::Recursive, _) => {
                        for vb in &bindings {
                            self.value_binding(vb)?;
                        }
                        Ok(())
                    }
                }
            }
            // bs_builtin_ppx.ml:633: `@@config` is left untouched.
            StructureItemDesc::Pstr_attribute(attr) if is_config_attribute(attr, self.arena) => {
                Ok(())
            }
            _ => self.default_structure_item(item),
        }
    }

    /// `Ast_mapper.M.map_structure_item` (ast_mapper.ml:236-255).
    fn default_structure_item(&mut self, item: &StructureItem) -> PpxResult<()> {
        match &item.pstr_desc {
            StructureItemDesc::Pstr_derived(_) => Ok(()),
            StructureItemDesc::Pstr_eval(inner) => {
                let (expr, attrs) = &**inner;
                self.expr(*expr)?;
                self.attributes(attrs)
            }
            StructureItemDesc::Pstr_value(inner) => {
                for vb in &self.arena.vb_list(inner.1).to_vec() {
                    self.value_binding(vb)?;
                }
                Ok(())
            }
            StructureItemDesc::Pstr_primitive(vd) => self.value_description(vd),
            StructureItemDesc::Pstr_type(inner) => {
                for tdcl in &inner.1 {
                    self.type_declaration(tdcl, false)?;
                }
                Ok(())
            }
            StructureItemDesc::Pstr_typext(te) => self.type_extension(te),
            StructureItemDesc::Pstr_exception(ec) => self.extension_constructor(ec),
            StructureItemDesc::Pstr_module(mb) => self.module_binding(mb),
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    self.module_binding(mb)?;
                }
                Ok(())
            }
            StructureItemDesc::Pstr_modtype(mtd) => self.module_type_declaration(mtd),
            StructureItemDesc::Pstr_open(od) => self.attributes(&od.popen_attributes),
            // `Incl.mk ?loc ?attrs mexpr` (ast_helper.ml:448).
            StructureItemDesc::Pstr_include(incl) => {
                self.module_expr(incl.pincl_mod)?;
                self.attributes(&incl.pincl_attributes)
            }
            StructureItemDesc::Pstr_attribute(attr) => self.attribute(attr),
            // `Str.extension ?loc ?attrs a` (ast_helper.ml:323).
            StructureItemDesc::Pstr_extension(inner) => {
                let (extension, attrs) = &**inner;
                self.extension(extension)?;
                self.attributes(attrs)
            }
            StructureItemDesc::Pstr_raw(raw) => self.attributes(&raw.attrs),
        }
    }

    /// `signature = List.map signature_item` (ast_mapper.ml:473).
    pub(super) fn signature(&mut self, items: &[SignatureItem]) -> PpxResult<()> {
        for item in items {
            self.signature_item(item)?;
        }
        Ok(())
    }

    /// `Bs_builtin_ppx.signature_item_mapper` (bs_builtin_ppx.ml:435-511).
    fn signature_item(&mut self, item: &SignatureItem) -> PpxResult<()> {
        match &item.psig_desc {
            SignatureItemDesc::Psig_type(inner) => {
                let (_rec_flag, tdcls) = &**inner;
                self.type_declarations_with_deriving(tdcls, false)
            }
            SignatureItemDesc::Psig_value(vd) => {
                self.attributes(&vd.pval_attributes)?;
                if is_rs_external(&vd.pval_attributes, &vd.pval_prim, self.arena) {
                    self.external(vd)
                } else {
                    // bs_builtin_ppx.ml:471-480: the semantic string of an
                    // `@inline` string payload.
                    if let Some(expr) = find_inline_payload_expr(&vd.pval_attributes, self.arena) {
                        inline_string_semantic(expr, self.arena)?;
                    }
                    self.value_description(vd)
                }
            }
            SignatureItemDesc::Psig_typext(te) => self.type_extension(te),
            SignatureItemDesc::Psig_exception(ec) => self.extension_constructor(ec),
            // `Md.mk ?loc ?attrs name typ` (ast_helper.ml:423).
            SignatureItemDesc::Psig_module(md) => {
                self.module_type(md.pmd_type)?;
                self.attributes(&md.pmd_attributes)
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    self.module_type(md.pmd_type)?;
                    self.attributes(&md.pmd_attributes)?;
                }
                Ok(())
            }
            SignatureItemDesc::Psig_modtype(mtd) => self.module_type_declaration(mtd),
            SignatureItemDesc::Psig_open(od) => self.attributes(&od.popen_attributes),
            // `Incl.mk ?loc ?attrs mexpr` (ast_helper.ml:448).
            SignatureItemDesc::Psig_include(incl) => {
                self.module_type(incl.pincl_mod)?;
                self.attributes(&incl.pincl_attributes)
            }
            SignatureItemDesc::Psig_attribute(attr) => self.attribute(attr),
            // `Sig.extension ?loc ?attrs a` (ast_helper.ml:305).
            SignatureItemDesc::Psig_extension(inner) => {
                let (extension, attrs) = &**inner;
                self.extension(extension)?;
                self.attributes(attrs)
            }
        }
    }

    /// `Ast_tdcls.handle_tdcls_in_stru`/`handle_tdcls_in_sigi`
    /// (ast_tdcls.ml:38-108): `process_derive_type` on the last declaration,
    /// the declarations (without the `@deriving` attributes), then the
    /// derivers.
    fn type_declarations_with_deriving(
        &mut self,
        tdcls: &[TypeDeclaration],
        in_structure: bool,
    ) -> PpxResult<()> {
        match deriving_process_derive_type(tdcls, self.arena, &mut self.warnings)? {
            Some(payload) => {
                let last = tdcls.len() - 1;
                for (index, tdcl) in tdcls.iter().enumerate() {
                    self.type_declaration(tdcl, index == last)?;
                }
                run_derivers(tdcls, self.arena, in_structure, payload, &mut self.warnings)
            }
            None => {
                for tdcl in tdcls {
                    self.type_declaration(tdcl, false)?;
                }
                Ok(())
            }
        }
    }

    /// `Ast_external.handle_external_in_stru`/`handle_external_in_sig`
    /// (ast_external.ml:25-95): the type, the attributes, then the primitive.
    fn external(&mut self, vd: &ValueDescription) -> PpxResult<()> {
        self.typ(vd.pval_type)?;
        self.attributes(&vd.pval_attributes)?;
        validate_external_attribute_errors(vd, self.arena, &mut self.warnings)
    }

    // ------------------------------------------------------------------
    // Value bindings
    // ------------------------------------------------------------------

    /// `Ast_tuple_pattern_flatten.value_bindings_mapper`
    /// (ast_tuple_pattern_flatten.ml:108-112): `Ext_list.fold_right` over the
    /// bindings, so the last one is mapped first.
    fn value_bindings_flattened(&mut self, bindings: &[ValueBinding]) -> PpxResult<()> {
        for vb in bindings.iter().rev() {
            // `flattern_tuple_pattern_vb` (ast_tuple_pattern_flatten.ml:44-105).
            self.value_binding(vb)?;
            if self.arena.value_constraint(vb.pvb_pat).is_none() {
                validate_module_record_pattern_binding_error(vb, self.arena)?;
            }
        }
        Ok(())
    }

    /// `default_mapper.value_binding` (ast_mapper.ml:521-533): pattern,
    /// constraint type, expression, attributes.
    fn value_binding(&mut self, vb: &ValueBinding) -> PpxResult<()> {
        self.pat(vb.pvb_pat)?;
        if let Some(constraint) = self.arena.value_constraint(vb.pvb_pat).cloned() {
            self.typ(constraint.pvc_type)?;
        }
        self.expr(vb.pvb_expr)?;
        self.attributes(&vb.pvb_attributes)
    }

    fn cases(&mut self, cases: &[Case]) -> PpxResult<()> {
        for case in cases {
            // `{pc_lhs = pat; pc_guard = ...; pc_rhs = expr}` is evaluated
            // from the last field.
            self.expr(case.pc_rhs)?;
            if let Some(guard) = case.pc_guard {
                self.expr(guard)?;
            }
            self.pat(case.pc_lhs)?;
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Attributes and payloads
    // ------------------------------------------------------------------

    fn attributes(&mut self, attrs: &[Attribute]) -> PpxResult<()> {
        for attr in attrs {
            self.attribute(attr)?;
        }
        Ok(())
    }

    fn attribute(&mut self, attr: &Attribute) -> PpxResult<()> {
        self.payload(&attr.1)
    }

    fn extension(&mut self, extension: &Extension) -> PpxResult<()> {
        self.payload(&extension.1)
    }

    fn payload(&mut self, payload: &Payload) -> PpxResult<()> {
        match payload {
            Payload::PStr(items) => self.structure(items),
            Payload::PSig(items) => self.signature(items),
            Payload::PTyp(typ) => self.typ(*typ),
            Payload::PPat(inner) => {
                let (pat, guard) = &**inner;
                if let Some(guard) = guard {
                    self.expr(*guard)?;
                }
                self.pat(*pat)
            }
        }
    }

    // ------------------------------------------------------------------
    // Type declarations
    // ------------------------------------------------------------------

    /// `T.map_type_declaration` (ast_mapper.ml:142-164): `Type.mk ?loc ?attrs
    /// ?params ?cstrs ?kind ?priv ?manifest ?origin name` (ast_helper.ml:469)
    /// evaluates the manifest, kind, constraints, parameters, then the
    /// attributes. `strip_deriving` drops the `@deriving` attributes
    /// `process_derive_type` removed.
    fn type_declaration(&mut self, tdcl: &TypeDeclaration, strip_deriving: bool) -> PpxResult<()> {
        if let Some(manifest) = tdcl.ptype_manifest {
            self.typ(manifest)?;
        }
        match &tdcl.ptype_kind {
            TypeKind::Ptype_variant(constructors) => {
                for constructor in constructors {
                    self.constructor_declaration(constructor)?;
                }
            }
            TypeKind::Ptype_record(labels) => {
                for label in labels {
                    self.label_declaration(label)?;
                }
            }
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
        }
        for (left, right, _loc) in &tdcl.ptype_cstrs {
            self.typ(*right)?;
            self.typ(*left)?;
        }
        for (param, _variance) in &tdcl.ptype_params {
            self.typ(*param)?;
        }
        for attr in tdcl.ptype_attributes.iter() {
            if strip_deriving && self.arena.get_string(attr.0.txt) == "deriving" {
                continue;
            }
            self.attribute(attr)?;
        }
        Ok(())
    }

    /// `default_mapper.constructor_declaration` (ast_mapper.ml:614-620):
    /// `Type.constructor ?loc ?attrs ?args ?res ?runtime_tag name`
    /// (ast_helper.ml:500) evaluates the result type, the arguments, then the
    /// attributes.
    fn constructor_declaration(&mut self, constructor: &ConstructorDeclaration) -> PpxResult<()> {
        if let Some(res) = constructor.pcd_res {
            self.typ(res)?;
        }
        self.constructor_arguments(&constructor.pcd_args)?;
        self.attributes(&constructor.pcd_attributes)
    }

    fn constructor_arguments(&mut self, args: &ConstructorArguments) -> PpxResult<()> {
        match args {
            ConstructorArguments::Pcstr_tuple(types) => {
                for typ in types {
                    self.typ(*typ)?;
                }
                Ok(())
            }
            ConstructorArguments::Pcstr_record(labels) => {
                for label in labels {
                    self.label_declaration(label)?;
                }
                Ok(())
            }
        }
    }

    /// `default_mapper.label_declaration` (ast_mapper.ml:621-629):
    /// `Type.field ?loc ?attrs ?mut ?optional ?runtime_name name typ`
    /// (ast_helper.ml:566) evaluates the type, then the attributes.
    fn label_declaration(&mut self, label: &LabelDeclaration) -> PpxResult<()> {
        self.typ(label.pld_type)?;
        self.attributes(&label.pld_attributes)
    }

    /// `T.map_type_extension` (ast_mapper.ml:178-195): `Te.mk ?attrs ?params
    /// ?priv path constructors` (ast_helper.ml:633) evaluates the
    /// constructors, the parameters, then the attributes.
    fn type_extension(&mut self, te: &TypeExtension) -> PpxResult<()> {
        for constructor in &te.ptyext_constructors {
            self.extension_constructor(constructor)?;
        }
        for (param, _variance) in &te.ptyext_params {
            self.typ(*param)?;
        }
        self.attributes(&te.ptyext_attributes)
    }

    /// `T.map_extension_constructor` (ast_mapper.ml:193-203): `Te.constructor
    /// ?loc ?attrs name kind` (ast_helper.ml:642) evaluates the kind (the
    /// result type, then the arguments of `Pext_decl`), then the attributes.
    fn extension_constructor(&mut self, ec: &ExtensionConstructor) -> PpxResult<()> {
        match &ec.pext_kind {
            ExtensionConstructorKind::Pext_decl(args, res) => {
                if let Some(res) = res {
                    self.typ(*res)?;
                }
                self.constructor_arguments(args)?;
            }
            ExtensionConstructorKind::Pext_rebind(_) => {}
        }
        self.attributes(&ec.pext_attributes)
    }

    /// `default_mapper.value_description` (ast_mapper.ml:550-557): `Val.mk
    /// ?loc ?attrs ?prim name typ` (ast_helper.ml:407) evaluates the type, then
    /// the attributes.
    fn value_description(&mut self, vd: &ValueDescription) -> PpxResult<()> {
        self.typ(vd.pval_type)?;
        self.attributes(&vd.pval_attributes)
    }

    // ------------------------------------------------------------------
    // Modules
    // ------------------------------------------------------------------

    /// `default_mapper.module_binding`: `Mb.mk ?loc ?attrs name expr`
    /// (ast_helper.ml:433) evaluates the module expression, then the
    /// attributes.
    fn module_binding(&mut self, mb: &ModuleBinding) -> PpxResult<()> {
        self.module_expr(mb.pmb_expr)?;
        self.attributes(&mb.pmb_attributes)
    }

    /// `default_mapper.module_type_declaration`: `Mtd.mk ?loc ?attrs ?typ name`
    /// (ast_helper.ml:428) evaluates the module type, then the attributes.
    fn module_type_declaration(&mut self, mtd: &ModuleTypeDeclaration) -> PpxResult<()> {
        if let Some(typ) = mtd.pmtd_type {
            self.module_type(typ)?;
        }
        self.attributes(&mtd.pmtd_attributes)
    }

    /// `M.map` (ast_mapper.ml:218-234).
    fn module_expr(&mut self, idx: ModExprIdx) -> PpxResult<()> {
        let mod_expr = self.arena.get_mod_expr(idx).clone();
        self.attributes(&mod_expr.pmod_attributes)?;
        match &mod_expr.pmod_desc {
            ModuleExprDesc::Pmod_ident(_) => Ok(()),
            ModuleExprDesc::Pmod_structure(items) => self.structure(items),
            ModuleExprDesc::Pmod_functor(inner) => {
                // bs_builtin_ppx.ml:886-903: a functor compiles to a JS
                // function that is not async, so its body is not in an async
                // context, whatever the context around it. The parameter's
                // module type is mapped first and keeps the context.
                let (_name, arg_type, body) = &**inner;
                if let Some(arg_type) = arg_type {
                    self.module_type(*arg_type)?;
                }
                let async_saved = self.async_context;
                self.async_context = false;
                let result = self.module_expr(*body);
                self.async_context = async_saved;
                result
            }
            ModuleExprDesc::Pmod_apply(left, right) => {
                self.module_expr(*right)?;
                self.module_expr(*left)
            }
            ModuleExprDesc::Pmod_constraint(inner, mod_type) => {
                self.module_type(*mod_type)?;
                self.module_expr(*inner)
            }
            ModuleExprDesc::Pmod_unpack(expr) => self.expr(*expr),
            ModuleExprDesc::Pmod_extension(extension) => self.extension(extension),
            ModuleExprDesc::Pmod_await(inner) => self.module_expr(*inner),
        }
    }

    /// `MT.map` (ast_mapper.ml:162-181).
    fn module_type(&mut self, idx: ModTypeIdx) -> PpxResult<()> {
        let mod_type = self.arena.get_mod_type(idx).clone();
        self.attributes(&mod_type.pmty_attributes)?;
        match &mod_type.pmty_desc {
            ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => Ok(()),
            ModuleTypeDesc::Pmty_signature(items) => self.signature(items),
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (_name, arg_type, result) = &**inner;
                self.module_type(*result)?;
                if let Some(arg_type) = arg_type {
                    self.module_type(*arg_type)?;
                }
                Ok(())
            }
            ModuleTypeDesc::Pmty_with(inner) => {
                let (mod_type, constraints) = &**inner;
                for constraint in constraints {
                    match constraint {
                        WithConstraint::Pwith_type(_, tdcl)
                        | WithConstraint::Pwith_typesubst(_, tdcl) => {
                            self.type_declaration(tdcl, false)?;
                        }
                        WithConstraint::Pwith_module(_, _)
                        | WithConstraint::Pwith_modsubst(_, _) => {}
                    }
                }
                self.module_type(*mod_type)
            }
            ModuleTypeDesc::Pmty_typeof(mod_expr) => self.module_expr(*mod_expr),
            ModuleTypeDesc::Pmty_extension(extension) => self.extension(extension),
        }
    }

    // ------------------------------------------------------------------
    // Core types
    // ------------------------------------------------------------------

    /// `Ast_core_type_class_type.typ_mapper` (ast_core_type_class_type.ml:79-136).
    fn typ(&mut self, idx: CoreTypeIdx) -> PpxResult<()> {
        let typ = self.arena.get_core_type(idx).clone();
        if let CoreTypeDesc::Ptyp_object(inner) = &typ.ptyp_desc {
            // Object fields are mapped from the last one
            // (`Ext_list.fold_right`); the object's own attributes and
            // inherited types are not mapped.
            let (fields, _closed) = &**inner;
            for field in fields.iter().rev() {
                if let ObjectField::Otag(_label, _attrs, field_type) = field {
                    self.typ(*field_type)?;
                }
            }
            return Ok(());
        }
        self.default_typ(&typ)
    }

    /// `T.map` (ast_mapper.ml:79-96).
    fn default_typ(&mut self, typ: &CoreType) -> PpxResult<()> {
        self.attributes(&typ.ptyp_attributes)?;
        match &typ.ptyp_desc {
            CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => Ok(()),
            CoreTypeDesc::Ptyp_arrow(inner) => {
                let (arg, ret, arity) = &**inner;
                self.typ(*ret)?;
                let params = self.arena.nary_arrow_args(arg, *arity).into_owned();
                for param in params {
                    self.typ(param.typ)?;
                }
                Ok(())
            }
            CoreTypeDesc::Ptyp_tuple(types) => {
                for typ in self.arena.type_list(*types).to_vec().iter() {
                    self.typ(*typ)?;
                }
                Ok(())
            }
            CoreTypeDesc::Ptyp_constr(inner) => {
                for typ in self.arena.type_list(inner.1).to_vec().iter() {
                    self.typ(*typ)?;
                }
                Ok(())
            }
            CoreTypeDesc::Ptyp_object(_) => unreachable!("object types are handled by typ"),
            CoreTypeDesc::Ptyp_alias(inner) => self.typ(inner.0),
            CoreTypeDesc::Ptyp_variant(inner) => {
                for row in &inner.0 {
                    match row {
                        RowField::Rtag(_label, attrs, _empty, types) => {
                            for typ in types.iter().flat_map(|group| group.txt.iter()) {
                                self.typ(*typ)?;
                            }
                            self.attributes(attrs)?;
                        }
                        RowField::Rinherit(typ) => self.typ(*typ)?,
                    }
                }
                Ok(())
            }
            CoreTypeDesc::Ptyp_poly(inner) => self.typ(inner.1),
            CoreTypeDesc::Ptyp_package(inner) => {
                for (_lid, typ) in &inner.1 {
                    self.typ(*typ)?;
                }
                Ok(())
            }
            CoreTypeDesc::Ptyp_extension(extension) => self.extension(extension),
        }
    }

    // ------------------------------------------------------------------
    // Patterns
    // ------------------------------------------------------------------

    /// `Bs_builtin_ppx.pat_mapper` (bs_builtin_ppx.ml:93-100).
    fn pat(&mut self, idx: PatIdx) -> PpxResult<()> {
        let pat = self.arena.get_pat(idx).clone();
        if let PatternDesc::Ppat_constant(Constant::Integer(_, Some('l'))) = &pat.ppat_desc {
            return Ok(());
        }
        self.default_pat(&pat)
    }

    /// `P.map` (ast_mapper.ml:394-438).
    fn default_pat(&mut self, pat: &Pattern) -> PpxResult<()> {
        self.attributes(&pat.ppat_attributes)?;
        match &pat.ppat_desc {
            PatternDesc::Ppat_any
            | PatternDesc::Ppat_var(_)
            | PatternDesc::Ppat_constant(_)
            | PatternDesc::Ppat_interval(_)
            | PatternDesc::Ppat_type(_)
            | PatternDesc::Ppat_variant_spread(_)
            | PatternDesc::Ppat_unpack(_) => Ok(()),
            PatternDesc::Ppat_alias(inner, _) | PatternDesc::Ppat_exception(inner) => {
                self.pat(*inner)
            }
            PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
                for item in self.arena.pat_list(*items).to_vec().iter() {
                    self.pat(*item)?;
                }
                Ok(())
            }
            PatternDesc::Ppat_dict(entries) => {
                for entry in entries.iter() {
                    self.pat(entry.pdp_pattern)?;
                }
                Ok(())
            }
            PatternDesc::Ppat_construct(_, args) => {
                for arg in self.arena.pat_list(args.txt).to_vec().iter() {
                    self.pat(*arg)?;
                }
                Ok(())
            }
            PatternDesc::Ppat_variant(inner) => {
                for arg in self.arena.pat_list(inner.1.txt).to_vec().iter() {
                    self.pat(*arg)?;
                }
                Ok(())
            }
            PatternDesc::Ppat_record(inner) => {
                let (fields, _closed, rest) = &**inner;
                for field in self.arena.pat_field_list(*fields).to_vec() {
                    self.pat(field.pat)?;
                }
                if let Some(rest_type) = rest.as_ref().and_then(|rest| rest.rest_type) {
                    self.typ(rest_type)?;
                }
                Ok(())
            }
            PatternDesc::Ppat_or(left, right) => {
                self.pat(*right)?;
                self.pat(*left)
            }
            PatternDesc::Ppat_constraint(inner) => {
                let (inner_pat, typ) = &**inner;
                self.typ(*typ)?;
                self.pat(*inner_pat)
            }
            PatternDesc::Ppat_extension(extension) => self.extension(extension),
        }
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    /// `Bs_builtin_ppx.expr_mapper` (bs_builtin_ppx.ml:394-430): map the
    /// expression, restore the async context, then check `await`.
    fn expr(&mut self, idx: ExprIdx) -> PpxResult<()> {
        if self.arena.expr_needs_no_rewrite(idx) {
            return Ok(());
        }
        let expr = self.arena.get_expr(idx).clone();
        let async_saved = self.async_context;
        let result = self.expr_inner(&expr);
        self.async_context = async_saved;
        result?;
        let awaits = match &expr.pexp_desc {
            ExpressionDesc::Pexp_letmodule(inner) => {
                let mod_expr = self.arena.get_mod_expr(inner.1);
                letmodule_expr_has_await_payload(mod_expr, self.arena)
            }
            ExpressionDesc::Pexp_await(_) | ExpressionDesc::Pexp_for_await_of(_) => true,
            _ => false,
        };
        if awaits && !self.async_context {
            return Err(PpxError::at_loc(
                expr.pexp_loc,
                AWAIT_NOT_ASYNC_CONTEXT_ERROR,
            ));
        }
        Ok(())
    }

    /// The inner `expr_mapper` (bs_builtin_ppx.ml:108-392).
    fn expr_inner(&mut self, expr: &Expression) -> PpxResult<()> {
        match &expr.pexp_desc {
            // `Pexp_regexp`: `Ast_payload.validate_raw_source ~kind:Raw_re`
            // on `/pattern/flags`, then the attributes are mapped.
            ExpressionDesc::Pexp_regexp(regexp) => {
                let source = format!("/{}/{}", regexp.pattern, regexp.flags);
                validate_regexp_source(&source, expr.pexp_loc, self.arena, &mut self.warnings)?;
                self.attributes(&expr.pexp_attributes)
            }
            // `Pexp_braces`: forward `@this` to a braced function.
            ExpressionDesc::Pexp_braces(braces) => {
                let has_this = expr
                    .pexp_attributes
                    .iter()
                    .any(|(name, _)| self.arena.get_string(name.txt) == "this");
                if !has_this {
                    return self.default_expr(expr);
                }
                let (this_attrs, other_attrs): (Vec<Attribute>, Vec<Attribute>) = expr
                    .pexp_attributes
                    .iter()
                    .cloned()
                    .partition(|(name, _)| self.arena.get_string(name.txt) == "this");
                match add_this_to_braced_function(&this_attrs, braces.expr, self.arena) {
                    Some(inner) => {
                        let rewritten = Expression {
                            pexp_desc: ExpressionDesc::Pexp_braces(
                                crate::parser::ast::PexpBraces {
                                    expr: inner,
                                    braces_loc: braces.braces_loc,
                                },
                            ),
                            pexp_loc: expr.pexp_loc,
                            pexp_attributes: Attributes::from_vec(other_attrs),
                        };
                        self.default_expr(&rewritten)
                    }
                    None => self.default_expr(expr),
                }
            }
            // `Ast_exp_extension.handle_extension` (ast_exp_extension.ml:26-83).
            ExpressionDesc::Pexp_extension(extension) => {
                self.expression_extension(expr.pexp_loc, extension)
            }
            // bs_builtin_ppx.ml `Pexp_raw`: `handle_raw_node`.
            ExpressionDesc::Pexp_raw(raw) => check_raw_node(raw, self.arena, &mut self.warnings),
            // bs_builtin_ppx.ml `Pexp_todo`: `Ast_exp_extension.todo` warns at
            // the expression after reading the message, which raises on an
            // invalid template escape.
            ExpressionDesc::Pexp_todo(todo) => {
                let message = match todo.message {
                    Some(message) => {
                        expr_semantic_string(self.arena.get_expr(message), self.arena)?
                    }
                    None => None,
                };
                self.warnings.push(PpxWarning {
                    loc: expr.pexp_loc,
                    warning: Warning::BsTodo { message },
                });
                Ok(())
            }
            ExpressionDesc::Pexp_constant(constant) => match constant {
                Constant::Integer(_, Some('l')) => Ok(()),
                _ => self.attributes(&expr.pexp_attributes),
            },
            ExpressionDesc::Pexp_fun(fun) => self.function(expr, fun),
            ExpressionDesc::Pexp_apply(apply) => self.apply(expr, apply),
            ExpressionDesc::Pexp_match(inner)
                if self.is_bool_match(self.arena.case_list(inner.1)) =>
            {
                // Rewritten to `Pexp_ifthenelse (b, t, Some f)` and mapped by
                // `default_expr_mapper`.
                let (scrutinee, cases) = inner;
                let cases = self.arena.case_list(*cases).to_vec();
                self.attributes(&expr.pexp_attributes)?;
                let (true_case, false_case) = if self.case_is_constructor(&cases[0], "true") {
                    (&cases[0], &cases[1])
                } else {
                    (&cases[1], &cases[0])
                };
                self.expr(false_case.pc_rhs)?;
                self.expr(true_case.pc_rhs)?;
                self.expr(*scrutinee)
            }
            ExpressionDesc::Pexp_let(inner) => self.let_expr(expr, inner),
            ExpressionDesc::Pexp_letmodule(inner) => {
                let (_name, mod_expr_idx, body) = &**inner;
                let mod_expr = self.arena.get_mod_expr(*mod_expr_idx);
                if letmodule_expr_has_await_payload(mod_expr, self.arena) {
                    // bs_builtin_ppx.ml:344-383: the module becomes
                    // `Ast_await.create_await_module_expression`; only the body
                    // is mapped.
                    return self.expr(*body);
                }
                self.attributes(&expr.pexp_attributes)?;
                self.expr(*body)?;
                self.module_expr(*mod_expr_idx)
            }
            _ => self.default_expr(expr),
        }
    }

    /// `Pexp_fun` in `expr_mapper` (bs_builtin_ppx.ml:120-158).
    fn function(&mut self, expr: &Expression, fun: &PexpFun) -> PpxResult<()> {
        let params = self.arena.nary_fun_params(fun).into_owned();
        let newtypes = self.arena.nary_fun_newtypes(fun).to_vec();
        let body = self.arena.nary_fun_body(fun);
        if has_this_attr(&expr.pexp_attributes, self.arena) {
            // `Ast_uncurry_gen.to_method_callback` (ast_uncurry_gen.ml:28-80).
            self.async_context = false;
            let Some((self_param, rest)) = params.split_first() else {
                return Ok(());
            };
            self.pat(self_param.p_pat)?;
            let self_pat = self.arena.get_pat(self_param.p_pat);
            if single_var_pattern_name_conservative(self_pat, self.arena).is_none() {
                return Err(PpxError::at_loc(
                    self_pat.ppat_loc,
                    "@this expects its first parameter to be a simple variable (or `_`).",
                ));
            }
            // `Bs_syntaxerr.optional_err`.
            let optional_err = |label: &ArgLabel| {
                if matches!(label, ArgLabel::Optional(_)) {
                    Err(PpxError::at_loc(
                        expr.pexp_loc,
                        "Uncurried function doesn't support optional arguments yet",
                    ))
                } else {
                    Ok(())
                }
            };
            optional_err(&self_param.p_lbl)?;
            for param in rest {
                optional_err(&param.p_lbl)?;
                self.pat(param.p_pat)?;
            }
            return self.expr(body);
        }
        // bs_builtin_ppx.ml:168-171: a `Pexp_fun` holds all parameters of
        // one function, so a `Pexp_fun` in its body is another function and
        // is in an async context exactly when it is async itself.
        self.async_context = fun.is_async;
        self.attributes(&expr.pexp_attributes)?;
        for param in &params {
            // `{p with p_default = ...; p_pat = ...}` maps the pattern first.
            self.pat(param.p_pat)?;
            if let Some(default) = param.p_default {
                self.expr(default)?;
            }
        }
        self.expr(body)?;
        for (_name, attrs) in &newtypes {
            self.attributes(attrs)?;
        }
        Ok(())
    }

    /// `Ast_exp_apply.app_exp_mapper` (ast_exp_apply.ml:75-208).
    fn apply(&mut self, expr: &Expression, apply: &PexpApply) -> PpxResult<()> {
        if let Some(error) = app_exp_mapper_error(expr, self.arena) {
            return Err(error);
        }
        if expression_is_lident(apply.funct, "->", self.arena) {
            // `a |. f`: `let a = self.expr self a_ in let f = self.expr self f_`.
            let args = self.arena.apply_args(apply.args);
            let (lhs, rhs) = (args[0].1, args[1].1);
            self.expr(lhs)?;
            self.expr(rhs)
        } else {
            // `default_expr_mapper`: attributes, arguments, function.
            self.attributes(&expr.pexp_attributes)?;
            for (_, arg) in self.arena.apply_args(apply.args).to_vec() {
                self.expr(arg)?;
            }
            self.expr(apply.funct)
        }
    }

    /// `Pexp_let` in `expr_mapper` and `default_expr_mapper`
    /// (bs_builtin_ppx.ml:75-90, 309-341).
    fn let_expr(
        &mut self,
        expr: &Expression,
        inner: &(RecFlag, crate::parse_arena::VbList, ExprIdx),
    ) -> PpxResult<()> {
        let (rec_flag, bindings, body) = inner;
        let bindings = &self.arena.vb_list(*bindings).to_vec();
        if let [vb] = bindings.as_slice()
            && has_unwrap_attr(&vb.pvb_attributes, self.arena)
        {
            let pat = self.arena.get_pat(vb.pvb_pat);
            let loc = pat.ppat_loc;
            // bs_builtin_ppx.ml:250-276: a supported `let?`, then the
            // catch-all at 363-372.
            let supported = *rec_flag == RecFlag::Nonrecursive
                && self.arena.value_constraint(vb.pvb_pat).is_none()
                && classify_let_unwrap_pattern(pat, self.arena).is_some();
            if !self.let_unwrap {
                return Err(PpxError::at_loc(loc, LET_UNWRAP_NOT_ENABLED_ERROR));
            }
            if !supported {
                return Err(PpxError::at_loc(loc, LET_UNWRAP_UNSUPPORTED_TYPE_ERROR));
            }
            if !matches!(
                &crate::ast_payload::unwrap_braces(self.arena, self.arena.get_expr(vb.pvb_expr))
                    .pexp_desc,
                ExpressionDesc::Pexp_pack(_)
            ) {
                // `default_expr_mapper` on `Pexp_match (pvb_expr, [early;
                // cont])` with the binding's attributes appended: the
                // attributes, the cases (the early-return case holds only
                // generated nodes; the continuation is `pvb_pat => body`),
                // then the scrutinee.
                self.attributes(&expr.pexp_attributes)?;
                self.attributes(&vb.pvb_attributes)?;
                self.expr(*body)?;
                self.pat(vb.pvb_pat)?;
                return self.expr(vb.pvb_expr);
            }
            // A packed module falls back to `default_expr_mapper` below.
        }
        if *rec_flag == RecFlag::Nonrecursive
            && let [vb] = bindings.as_slice()
            && self.arena.value_constraint(vb.pvb_pat).is_none()
            && self.is_record_pattern(vb.pvb_pat)
            && !matches!(
                &crate::parser::parsetree_viewer::unwrap_braces(
                    self.arena,
                    self.arena.get_expr(vb.pvb_expr)
                )
                .pexp_desc,
                ExpressionDesc::Pexp_pack(_)
            )
        {
            // `let {a, b} = e` becomes `switch e { | {a, b} => body }`, with
            // the binding's attributes appended to the expression's.
            self.attributes(&expr.pexp_attributes)?;
            self.attributes(&vb.pvb_attributes)?;
            self.expr(*body)?;
            self.pat(vb.pvb_pat)?;
            return self.expr(vb.pvb_expr);
        }
        self.attributes(&expr.pexp_attributes)?;
        self.expr(*body)?;
        match rec_flag {
            RecFlag::Nonrecursive => self.value_bindings_flattened(bindings),
            RecFlag::Recursive => {
                for vb in bindings {
                    self.value_binding(vb)?;
                }
                Ok(())
            }
        }
    }

    /// `Ast_exp_extension.handle_extension` (ast_exp_extension.ml:26-67): the
    /// payload is not mapped.
    fn expression_extension(&mut self, loc: LocIdx, extension: &Extension) -> PpxResult<()> {
        let (ext_name, payload) = extension;
        match self.arena.get_string(ext_name.txt) {
            "todo" => {
                self.warnings.push(PpxWarning {
                    loc,
                    warning: Warning::BsTodo {
                        // ast_exp_extension.ml:31.
                        message: payload_semantic_string(payload, self.arena)?,
                    },
                });
                Ok(())
            }
            // `Ast_payload.raw_as_string_exp_exn` warns about the Flow parse
            // errors of a string payload before `handle_ffi` rejects one that
            // is not a function.
            "ffi" => {
                push_raw_js_expression_warning(payload, self.arena, &mut self.warnings);
                validate_expression_extension_payload_error(extension, self.arena)
            }
            "raw" => {
                validate_expression_extension_payload_error(extension, self.arena)?;
                push_raw_js_expression_warning(payload, self.arena, &mut self.warnings);
                Ok(())
            }
            _ => validate_expression_extension_payload_error(extension, self.arena),
        }
    }

    /// `E.map` (ast_mapper.ml:282-390).
    fn default_expr(&mut self, expr: &Expression) -> PpxResult<()> {
        self.attributes(&expr.pexp_attributes)?;
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_ident(_)
            | ExpressionDesc::Pexp_constant(_)
            | ExpressionDesc::Pexp_break
            | ExpressionDesc::Pexp_continue => Ok(()),
            ExpressionDesc::Pexp_match((scrutinee, cases)) => {
                let cases = self.arena.case_list(*cases).to_vec();
                self.cases(&cases)?;
                self.expr(*scrutinee)
            }
            // ast_mapper.ml `try_ ~loc ~attrs ?finally:(map_opt (sub.expr sub) finally)
            // (sub.expr sub e) (sub.cases sub pel)`, arguments evaluated right to left.
            ExpressionDesc::Pexp_try((body, cases, finally)) => {
                let cases = self.arena.case_list(*cases).to_vec();
                self.cases(&cases)?;
                self.expr(*body)?;
                match finally {
                    Some(finally) => self.expr(*finally),
                    None => Ok(()),
                }
            }
            ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
                for item in self.arena.expr_list(*items).to_vec().iter() {
                    self.expr(*item)?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_dict(entries) => {
                for entry in entries.iter() {
                    match entry {
                        crate::parser::ast::DictEntry::Pdict_entry(_, e)
                        | crate::parser::ast::DictEntry::Pdict_spread(e) => self.expr(*e)?,
                    }
                }
                Ok(())
            }
            ExpressionDesc::Pexp_spread(_, elements) => {
                for element in self.arena.spread_element_list(*elements).to_vec() {
                    self.expr(element.expr())?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_template(template) => {
                for value in &template.values {
                    self.expr(*value)?;
                }
                Ok(())
            }
            // The tag is the first constructor argument, so it is mapped after
            // the values.
            ExpressionDesc::Pexp_tagged_template(template) => {
                for value in &template.values {
                    self.expr(*value)?;
                }
                self.expr(template.tag)
            }
            ExpressionDesc::Pexp_construct(_, args) => {
                for arg in self.arena.expr_list(args.txt).to_vec().iter() {
                    self.expr(*arg)?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_variant(inner) => {
                for arg in self.arena.expr_list(inner.1.txt).to_vec().iter() {
                    self.expr(*arg)?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_record(inner) => {
                let (fields, spread) = inner;
                if let Some(spread) = spread {
                    self.expr(*spread)?;
                }
                for field in self.arena.expr_field_list(*fields).to_vec() {
                    self.expr(field.expr)?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_field(target, _) => self.expr(*target),
            ExpressionDesc::Pexp_setfield(inner) => {
                let (target, _field, value) = &**inner;
                self.expr(*value)?;
                self.expr(*target)
            }
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (cond, then_expr, else_expr) = &**inner;
                if let Some(else_expr) = else_expr {
                    self.expr(*else_expr)?;
                }
                self.expr(*then_expr)?;
                self.expr(*cond)
            }
            ExpressionDesc::Pexp_ternary(inner) => {
                let (cond, consequent, alternate) = **inner;
                self.expr(alternate)?;
                self.expr(consequent)?;
                self.expr(cond)
            }
            ExpressionDesc::Pexp_braces(braces) => self.expr(braces.expr),
            ExpressionDesc::Pexp_regexp(_) => Ok(()),
            ExpressionDesc::Pexp_sequence(first, second)
            | ExpressionDesc::Pexp_while(first, second) => {
                self.expr(*second)?;
                self.expr(*first)
            }
            ExpressionDesc::Pexp_for(inner) => {
                let (pat, start, finish, _dir, body) = &**inner;
                self.expr(*body)?;
                self.expr(*finish)?;
                self.expr(*start)?;
                self.pat(*pat)
            }
            ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
                let (pat, collection, body) = &**inner;
                self.expr(*body)?;
                self.expr(*collection)?;
                self.pat(*pat)
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                let (inner_expr, typ) = &**inner;
                self.typ(*typ)?;
                self.expr(*inner_expr)
            }
            ExpressionDesc::Pexp_coerce(inner) => {
                let (inner_expr, from_type, to_type) = &**inner;
                self.typ(*to_type)?;
                if let Some(from_type) = from_type {
                    self.typ(*from_type)?;
                }
                self.expr(*inner_expr)
            }
            ExpressionDesc::Pexp_object_get(inner) => self.expr(inner.0),
            // `object_set ~loc ~attrs (sub.expr sub e) (map_loc sub s) (sub.expr sub v)`:
            // arguments right to left.
            ExpressionDesc::Pexp_object_set(inner) => {
                self.expr(inner.2)?;
                self.expr(inner.0)
            }
            ExpressionDesc::Pexp_object_literal(fields) => {
                for (_, e) in fields.iter() {
                    self.expr(*e)?;
                }
                Ok(())
            }
            ExpressionDesc::Pexp_letmodule(inner) => {
                let (_name, mod_expr, body) = &**inner;
                self.expr(*body)?;
                self.module_expr(*mod_expr)
            }
            ExpressionDesc::Pexp_letexception(inner) => {
                let (constructor, body) = &**inner;
                self.expr(*body)?;
                self.extension_constructor(constructor)
            }
            ExpressionDesc::Pexp_assert(inner) | ExpressionDesc::Pexp_await(inner) => {
                self.expr(*inner)
            }
            ExpressionDesc::Pexp_newtype(inner) => self.expr(inner.1),
            ExpressionDesc::Pexp_pack(mod_expr) => self.module_expr(*mod_expr),
            ExpressionDesc::Pexp_open(inner) => self.expr(inner.2),
            ExpressionDesc::Pexp_jsx_element(jsx) => match &**jsx {
                JsxElement::Fragment(fragment) => {
                    for child in &fragment.children {
                        self.expr(*child)?;
                    }
                    Ok(())
                }
                JsxElement::Unary(element) => self.jsx_props(&element.props),
                JsxElement::Container(element) => {
                    for child in &element.children {
                        self.expr(*child)?;
                    }
                    self.jsx_props(&element.props)
                }
            },
            // Handled by `expr_inner`.
            ExpressionDesc::Pexp_let(_)
            | ExpressionDesc::Pexp_fun(_)
            | ExpressionDesc::Pexp_apply(_)
            | ExpressionDesc::Pexp_extension(_)
            | ExpressionDesc::Pexp_raw(_)
            | ExpressionDesc::Pexp_todo(_) => Ok(()),
        }
    }

    fn jsx_props(&mut self, props: &[JsxProp]) -> PpxResult<()> {
        for prop in props {
            match prop {
                JsxProp::Value { value, .. } => self.expr(*value)?,
                JsxProp::Spreading { expr, .. } => self.expr(*expr)?,
                JsxProp::Punning { .. } => {}
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Shape predicates
    // ------------------------------------------------------------------

    fn case_is_constructor(&self, case: &Case, name: &str) -> bool {
        case.pc_guard.is_none()
            && matches!(
                &self.arena.get_pat(case.pc_lhs).ppat_desc,
                PatternDesc::Ppat_construct(lid, args)
                    if args.txt.is_empty() && matches!(
                        self.arena.get_longident(lid.txt),
                        Longident::Lident(n) if self.arena.get_string(*n) == name
                    )
            )
    }

    /// `switch b { | true => t | false => f }` in either case order
    /// (bs_builtin_ppx.ml:161-194).
    fn is_bool_match(&self, cases: &[Case]) -> bool {
        matches!(cases, [first, second]
            if (self.case_is_constructor(first, "true") && self.case_is_constructor(second, "false"))
                || (self.case_is_constructor(first, "false") && self.case_is_constructor(second, "true")))
    }

    fn is_record_pattern(&self, pat: PatIdx) -> bool {
        match &self.arena.get_pat(pat).ppat_desc {
            PatternDesc::Ppat_record(_) => true,
            PatternDesc::Ppat_alias(inner, _) => matches!(
                &self.arena.get_pat(*inner).ppat_desc,
                PatternDesc::Ppat_record(_)
            ),
            _ => false,
        }
    }
}
