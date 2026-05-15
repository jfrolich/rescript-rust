//! Typedtree -> Lambda conversion.
//!
//! This module provides a minimal but functional translation from the
//! typed AST into Lambda IR. The goal is to preserve semantics while
//! keeping the translation straightforward and easy to extend.

use std::path::Path as StdPath;

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::context::IdGenerator;
use crate::ident::{Ident, IdentFlags};
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
use crate::lambda::lam_constant::{Constant, StringDelim};
use crate::lambda::lam_primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName, ExternalObjLabel,
    ExternalObjSpec, ExternalReturnWrapper, ExternalSpec, ImportAttributes, Mutable, Primitive,
};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, DirectionFlag as LamDirection, FunctionAttribute, InlineAttribute,
    Lambda,
};
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::{Attributes, DirectionFlag, MutableFlag as ParserMutableFlag, RecFlag};
use crate::raw_lambda::typeopt::constructor_has_optional_shape;
use crate::types::asttypes::MutableFlag as TypeMutableFlag;
use crate::types::decl::{
    ConstructorDescription, ConstructorTag, LabelDescription, RecordRepresentation, ValueKind,
};
use crate::types::typedtree::{
    Case, Constant as TConstant, Expression, ExpressionDesc, FunctionParam, FunctionParamPattern,
    Pattern, PatternDesc, RecordField, RecordLabelDefinition, Structure, StructureItem,
    StructureItemDesc, ValueBinding,
};

const PREDEF_MATCH_FAILURE_STAMP: i32 = 17;
const PREDEF_ASSERT_FAILURE_STAMP: i32 = 27;

fn predef_exception_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::PREDEF_EXN.with_global())
}

fn record_field_is_static_optional_none(
    lbl: &LabelDescription,
    def: &RecordLabelDefinition,
) -> bool {
    if !lbl.lbl_optional {
        return false;
    }

    match def {
        RecordLabelDefinition::OmittedOptionalNone(_, _) => true,
        RecordLabelDefinition::Overridden(_, expr) => matches!(
            &expr.exp_desc,
            ExpressionDesc::Texp_construct(_, cstr, args)
                if args.is_empty() && cstr.cstr_name == "None" && constructor_has_optional_shape(cstr)
        ),
        RecordLabelDefinition::Kept(_) => false,
    }
}

/// Lambda conversion state.
pub struct LambdaConverter<'a> {
    id_gen: IdGenerator,
    arena: &'a ParseArena,
    preserve_expanded_sparse_records: bool,
}

impl<'a> LambdaConverter<'a> {
    /// Create a new converter with its own id generator.
    pub fn new(arena: &'a ParseArena) -> Self {
        Self {
            id_gen: IdGenerator::new(),
            arena,
            preserve_expanded_sparse_records: false,
        }
    }

    /// Create a new converter with stamps continuing from an existing phase.
    pub fn with_start_stamp(arena: &'a ParseArena, start_stamp: i32) -> Self {
        Self {
            id_gen: IdGenerator::with_start_stamp(start_stamp),
            arena,
            preserve_expanded_sparse_records: false,
        }
    }

    pub(crate) fn current_stamp(&self) -> i32 {
        self.id_gen.current_stamp()
    }

    pub(crate) fn set_current_stamp(&self, stamp: i32) {
        self.id_gen.set_current_stamp(stamp);
    }

    pub(crate) fn set_preserve_expanded_sparse_records(&mut self, preserve: bool) {
        self.preserve_expanded_sparse_records = preserve;
    }

    /// Helper to convert a LocIdx to a Location.
    #[inline]
    fn loc(&self, idx: LocIdx) -> Location {
        self.arena.to_location(idx)
    }

    fn basename_for_loc(&self, loc: Location) -> String {
        if loc.file_name_idx().0 == 0 {
            return String::new();
        }
        let file = self.arena.get_string(loc.file_name_idx());
        StdPath::new(file)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(file)
            .to_string()
    }

    fn failure_payload(&self, loc: Location) -> Constant {
        Constant::Block {
            tag: 0,
            tag_info: TagInfo::Tuple,
            elements: vec![
                Constant::string(self.basename_for_loc(loc)),
                Constant::int(loc.loc_start.line),
                Constant::int(loc.loc_start.column()),
            ],
        }
    }

    fn raise_predef_exception(&self, name: &str, stamp: i32, loc: Location) -> Lambda {
        let exn = Lambda::global_module(predef_exception_ident(name, stamp), false);
        let payload = Lambda::const_(self.failure_payload(loc));
        let block = Lambda::prim(
            Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
            vec![exn, payload],
            loc,
        );
        Lambda::prim(Primitive::Praise, vec![block], loc)
    }

    /// Convert a structure into a Lambda expression.
    pub fn convert_structure(&mut self, structure: &Structure) -> Lambda {
        let items: Vec<Lambda> = structure
            .str_items
            .iter()
            .map(|item| self.convert_structure_item(item))
            .filter(|lam| !lam.is_unit())
            .collect();

        if items.is_empty() {
            return Lambda::unit();
        }

        let mut iter = items.into_iter();
        let mut result = iter.next().unwrap();
        for item_lam in iter {
            result = Lambda::seq(result, item_lam);
        }
        result
    }

    fn convert_structure_item(&mut self, item: &StructureItem) -> Lambda {
        match &item.str_desc {
            StructureItemDesc::Tstr_eval(expr, _) => self.convert_expr(expr),
            StructureItemDesc::Tstr_value(rec_flag, bindings) => {
                self.convert_let_with_body(*rec_flag, bindings, Lambda::unit())
            }
            StructureItemDesc::Tstr_primitive(_) => Lambda::unit(),
            StructureItemDesc::Tstr_type(_, _) => Lambda::unit(),
            StructureItemDesc::Tstr_typext(_) => Lambda::unit(),
            StructureItemDesc::Tstr_exception(_) => Lambda::unit(),
            StructureItemDesc::Tstr_module(_) => Lambda::unit(),
            StructureItemDesc::Tstr_recmodule(_) => Lambda::unit(),
            StructureItemDesc::Tstr_modtype(_) => Lambda::unit(),
            StructureItemDesc::Tstr_open(_) => Lambda::unit(),
            StructureItemDesc::Tstr_include(_) => Lambda::unit(),
            StructureItemDesc::Tstr_attribute(_) => Lambda::unit(),
        }
    }

    /// Convert a typed expression to Lambda.
    pub fn convert_expr(&mut self, expr: &Expression) -> Lambda {
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => self.translate_primitive(self.loc(expr.exp_loc), prim),
                ValueKind::ValReg => self.translate_value_path(expr.exp_loc, path),
            },
            ExpressionDesc::Texp_constant(cst) => Lambda::const_(self.convert_constant(cst)),
            // OCaml `Translcore.transl_exp0` after #8348:
            // `Texp_break -> Lbreak | Texp_continue -> Lcontinue`.
            ExpressionDesc::Texp_break => Lambda::break_(),
            ExpressionDesc::Texp_continue => Lambda::continue_(),
            ExpressionDesc::Texp_let(rec_flag, bindings, body) => {
                let body_lam = self.convert_expr(body);
                self.convert_let_with_body(*rec_flag, bindings, body_lam)
            }
            ExpressionDesc::Texp_function {
                params,
                body,
                partial,
                arity,
                async_: _,
            } => self.convert_function(params, body, *partial, *arity),
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial: _,
                transformed_jsx: _,
            } => self.convert_apply(self.loc(expr.exp_loc), funct, args),
            ExpressionDesc::Texp_match(scrut, cases, _exn_cases, partial) => {
                let scrut_lam = self.convert_expr(scrut);
                self.compile_match(self.loc(expr.exp_loc), scrut_lam, cases, *partial)
            }
            ExpressionDesc::Texp_try(body, cases) => {
                let body_lam = self.convert_expr(body);
                let exn_id = self.id_gen.create("exn");
                let handler_scrut = Lambda::var(exn_id.clone());
                let handler = self.compile_match(
                    self.loc(expr.exp_loc),
                    handler_scrut,
                    cases,
                    crate::types::typedtree::Partial::Partial,
                );
                Lambda::try_(body_lam, exn_id, handler)
            }
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items.iter().map(|e| self.convert_expr(e)).collect();
                Lambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                    elems,
                    self.loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => {
                self.convert_construct(self.loc(expr.exp_loc), cstr, args)
            }
            ExpressionDesc::Texp_variant(tag, arg) => self.convert_poly_variant(tag, arg),
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
            } => self.convert_record(
                self.loc(expr.exp_loc),
                fields,
                extended_expression.as_deref(),
                None,
            ),
            ExpressionDesc::Texp_record_sparse {
                fields,
                all_labels,
                omitted_loc,
                ..
            } => {
                // Debug/captured lambda keeps OCaml's full `lbl_all` stream;
                // normal JS lowering can compact static omitted optional None.
                let (record_fields, logical_field_count) =
                    self.sparse_record_fields_for_lambda(all_labels, fields, *omitted_loc);
                self.convert_record(
                    self.loc(expr.exp_loc),
                    &record_fields,
                    None,
                    logical_field_count,
                )
            }
            ExpressionDesc::Texp_field(record, _, lbl) => {
                let rec_lam = self.convert_expr(record);
                let primitive = Primitive::Pfield(
                    lbl.lbl_pos,
                    FieldDbgInfo::Record {
                        name: lbl.lbl_name.clone(),
                        mutable_flag: to_parser_mutable(lbl.lbl_mut),
                    },
                );
                Lambda::prim(primitive, vec![rec_lam], self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_setfield(record, _, lbl, value) => {
                let rec_lam = self.convert_expr(record);
                let val_lam = self.convert_expr(value);
                let primitive = Primitive::Psetfield(
                    lbl.lbl_pos,
                    SetFieldDbgInfo::RecordSet(lbl.lbl_name.clone()),
                );
                Lambda::prim(primitive, vec![rec_lam, val_lam], self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_array(items) => {
                let elems = items.iter().map(|e| self.convert_expr(e)).collect();
                Lambda::prim(Primitive::Pmakearray, elems, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_ifthenelse(cond, then_, else_) => {
                let cond_lam = self.convert_expr(cond);
                let then_lam = self.convert_expr(then_);
                let else_lam = else_
                    .as_ref()
                    .map(|e| self.convert_expr(e))
                    .unwrap_or_else(Lambda::unit);
                Lambda::if_(cond_lam, then_lam, else_lam)
            }
            ExpressionDesc::Texp_sequence(a, b) => {
                let a_lam = self.convert_expr(a);
                let b_lam = self.convert_expr(b);
                Lambda::seq(a_lam, b_lam)
            }
            ExpressionDesc::Texp_while(cond, body) => {
                let cond_lam = self.convert_expr(cond);
                let body_lam = self.convert_expr(body);
                Lambda::while_(cond_lam, body_lam)
            }
            ExpressionDesc::Texp_for(var, _pat, start, end, dir, body) => {
                let start_lam = self.convert_expr(start);
                let end_lam = self.convert_expr(end);
                let body_lam = self.convert_expr(body);
                let dir = match dir {
                    DirectionFlag::Upto => LamDirection::Upto,
                    DirectionFlag::Downto => LamDirection::Downto,
                };
                Lambda::for_(var.clone(), start_lam, end_lam, dir, body_lam)
            }
            // Upstream #7887: for-of / for-await-of typed-tree variants.
            // Mirrors `compiler/ml/translcore.ml`: lower to the matching
            // Lambda variant.
            ExpressionDesc::Texp_for_of(var, _pat, iterable, body) => {
                let iterable_lam = self.convert_expr(iterable);
                let body_lam = self.convert_expr(body);
                Lambda::for_of(var.clone(), iterable_lam, body_lam)
            }
            ExpressionDesc::Texp_for_await_of(var, _pat, iterable, body) => {
                let iterable_lam = self.convert_expr(iterable);
                let body_lam = self.convert_expr(body);
                Lambda::for_await_of(var.clone(), iterable_lam, body_lam)
            }
            ExpressionDesc::Texp_send(_, _, _) => Lambda::unit(),
            ExpressionDesc::Texp_letmodule(_, _, _, body) => self.convert_expr(body),
            ExpressionDesc::Texp_letexception(_, body) => self.convert_expr(body),
            ExpressionDesc::Texp_assert(inner_expr) => {
                if matches!(
                    inner_expr.exp_desc,
                    ExpressionDesc::Texp_construct(_, ref cstr, ref args)
                        if cstr.cstr_name == "false" && args.is_empty()
                ) {
                    self.raise_predef_exception(
                        "Assert_failure",
                        PREDEF_ASSERT_FAILURE_STAMP,
                        self.loc(expr.exp_loc),
                    )
                } else {
                    let cond = self.convert_expr(inner_expr);
                    let failure = self.raise_predef_exception(
                        "Assert_failure",
                        PREDEF_ASSERT_FAILURE_STAMP,
                        self.loc(expr.exp_loc),
                    );
                    Lambda::if_(cond, Lambda::unit(), failure)
                }
            }
            ExpressionDesc::Texp_pack(_) => Lambda::unit(),
            ExpressionDesc::Texp_extension_constructor(_, path) => {
                self.translate_extension_path(path, self.loc(expr.exp_loc))
            }
        }
    }

    fn convert_constant(&self, cst: &TConstant) -> Constant {
        match cst {
            TConstant::Int(i) => Constant::Int {
                i: *i as i32,
                comment: None,
            },
            TConstant::Char(c) => Constant::Char(*c),
            TConstant::String(s, delim) => Constant::String {
                s: s.clone(),
                delim: delim
                    .as_ref()
                    .and_then(|d| match d.as_str() {
                        "" => Some(StringDelim::Plain),
                        "*j" | "js" | "j" => Some(StringDelim::StarJ),
                        "json" => Some(StringDelim::NoQuotes),
                        "bq" => Some(StringDelim::Backtick),
                        "`" => Some(StringDelim::Backtick),
                        _ => None,
                    })
                    .or_else(|| delim.is_none().then_some(StringDelim::Plain)),
            },
            TConstant::Float(f) => Constant::Float(f.clone()),
            TConstant::BigInt(neg, v) => Constant::BigInt {
                negative: *neg,
                value: v.clone(),
            },
        }
    }

    pub(crate) fn convert_let_with_body(
        &mut self,
        rec_flag: RecFlag,
        bindings: &[ValueBinding],
        body: Lambda,
    ) -> Lambda {
        match rec_flag {
            RecFlag::Nonrecursive => bindings.iter().rev().fold(body, |acc, binding| {
                let value = self.convert_expr(&binding.vb_expr);
                let failure = self.match_failure(self.loc(binding.vb_loc));
                self.bind_pattern(&binding.vb_pat, value, acc, failure)
            }),
            RecFlag::Recursive => {
                let mut ids = Vec::new();
                let mut lam_bindings = Vec::new();
                for binding in bindings {
                    if let PatternDesc::Tpat_var(id, _) = &binding.vb_pat.pat_desc {
                        ids.push(id.clone());
                        lam_bindings.push((id.clone(), self.convert_expr(&binding.vb_expr)));
                    } else {
                        // Fallback to non-recursive handling for complex patterns.
                        return bindings.iter().rev().fold(body, |acc, b| {
                            let value = self.convert_expr(&b.vb_expr);
                            let failure = self.match_failure(self.loc(b.vb_loc));
                            self.bind_pattern(&b.vb_pat, value, acc, failure)
                        });
                    }
                }
                Lambda::letrec(lam_bindings, body)
            }
        }
    }

    fn convert_apply(
        &mut self,
        loc: Location,
        funct: &Expression,
        args: &[crate::types::typedtree::ApplyArg],
    ) -> Lambda {
        fn lapply(loc: Location, func: Lambda, args: Vec<Lambda>) -> Lambda {
            let ap_info = ApInfo {
                loc,
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            };
            Lambda::Lapply(Apply {
                ap_func: Box::new(func),
                ap_args: args,
                ap_info,
                ap_transformed_jsx: false,
            })
        }

        fn protect(
            converter: &mut LambdaConverter<'_>,
            name: &str,
            lam: Lambda,
            defs: &mut Vec<(Ident, Lambda)>,
        ) -> Lambda {
            match lam {
                Lambda::Lvar(_) | Lambda::Lconst(_) => lam,
                _ => {
                    let id = converter.id_gen.create(name);
                    defs.push((id.clone(), lam));
                    Lambda::var(id)
                }
            }
        }

        fn build_apply(
            converter: &mut LambdaConverter<'_>,
            loc: Location,
            lam: Lambda,
            args_rev: Vec<(Lambda, bool)>,
            pending: &[(Option<Lambda>, bool)],
        ) -> Lambda {
            match pending.split_first() {
                Some(((None, optional), tail)) => {
                    let mut defs: Vec<(Ident, Lambda)> = Vec::new();
                    let all_optional = args_rev.iter().all(|(_, is_optional)| *is_optional);
                    let (applied_args, remaining_args) = if all_optional {
                        (Vec::new(), args_rev)
                    } else {
                        (args_rev, Vec::new())
                    };

                    let applied = if applied_args.is_empty() {
                        lam
                    } else {
                        lapply(
                            loc.clone(),
                            lam,
                            applied_args.into_iter().rev().map(|(arg, _)| arg).collect(),
                        )
                    };

                    let handle = protect(converter, "func", applied, &mut defs);
                    let mut protected_tail: Vec<(Option<Lambda>, bool)> =
                        Vec::with_capacity(tail.len());
                    for (arg, is_opt) in tail {
                        let protected_arg = arg
                            .as_ref()
                            .map(|lam| protect(converter, "arg", lam.clone(), &mut defs));
                        protected_tail.push((protected_arg, *is_opt));
                    }

                    let id_arg = converter.id_gen.create("param");
                    let mut next_args_rev = Vec::with_capacity(1 + remaining_args.len());
                    next_args_rev.push((Lambda::var(id_arg.clone()), *optional));
                    next_args_rev.extend(remaining_args.into_iter());

                    let body = build_apply(
                        converter,
                        loc.clone(),
                        handle,
                        next_args_rev,
                        &protected_tail,
                    );

                    let mut wrapped = match body {
                        Lambda::Lfunction(func) => {
                            let mut params = Vec::with_capacity(1 + func.params.len());
                            params.push(id_arg.clone());
                            params.extend(func.params);
                            Lambda::function_(params.len() as i32, params, *func.body, func.attr)
                        }
                        other => Lambda::function_(
                            1,
                            vec![id_arg.clone()],
                            other,
                            FunctionAttribute::default(),
                        ),
                    };

                    for (id, def_lam) in defs {
                        wrapped = Lambda::let_(LetKind::Strict, id, def_lam, wrapped);
                    }
                    wrapped
                }
                Some(((Some(arg), optional), tail)) => {
                    let mut next_args_rev = args_rev;
                    next_args_rev.push((arg.clone(), *optional));
                    build_apply(converter, loc, lam, next_args_rev, tail)
                }
                None => lapply(
                    loc,
                    lam,
                    args_rev.into_iter().rev().map(|(arg, _)| arg).collect(),
                ),
            }
        }

        if let ExpressionDesc::Texp_ident(_, _, desc) = &funct.exp_desc {
            if let ValueKind::ValPrim(prim) = &desc.val_kind {
                if args.iter().all(|arg| arg.expression.is_some()) {
                    let mut actual_args = Vec::new();
                    for arg in args {
                        if let Some(expr) = &arg.expression {
                            actual_args.push(self.convert_expr(expr));
                        }
                    }
                    if let Some(prim) = self.primitive_from_name(&prim.prim_name) {
                        return Lambda::prim(prim, actual_args, loc);
                    }
                }
            }
        }

        let func_lam = self.convert_expr(funct);
        let pending_args: Vec<(Option<Lambda>, bool)> = args
            .iter()
            .map(|arg| {
                (
                    arg.expression.as_ref().map(|expr| self.convert_expr(expr)),
                    arg.label.is_optional(),
                )
            })
            .collect();
        build_apply(self, loc, func_lam, Vec::new(), &pending_args)
    }

    fn convert_function(
        &mut self,
        params: &[FunctionParam],
        cases: &[Case],
        partial: crate::types::typedtree::Partial,
        arity: crate::parser::ast::Arity,
    ) -> Lambda {
        // Use arity to flatten nested functions into a single multi-param function
        // e.g., `(x, y) => x + y` has arity 2 but is represented as nested functions
        let (all_params, final_body, _final_partial) =
            self.flatten_function_by_arity(params, cases, partial, arity);

        let mut param_ids = Vec::new();
        for param in all_params.iter() {
            param_ids.push(param.param_id.clone());
        }

        // Convert the body - if it's simple variable patterns, skip pattern matching
        let body = if let Some(expr) = final_body {
            // We have the final body expression directly
            self.convert_expr(expr)
        } else {
            // Fall back to pattern matching on cases
            Lambda::unit()
        };

        let attr = FunctionAttribute {
            inline: InlineAttribute::Default,
            ..Default::default()
        };

        Lambda::function_(param_ids.len() as i32, param_ids, body, attr)
    }

    /// Create a scrutinee for pattern matching from param_ids
    fn make_scrutinee(&self, param_ids: &[Ident], loc: &Location) -> Lambda {
        if param_ids.len() == 1 {
            Lambda::var(param_ids[0].clone())
        } else {
            let args = param_ids.iter().cloned().map(Lambda::var).collect();
            Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                args,
                loc.clone(),
            )
        }
    }

    /// Check if a pattern is a simple variable pattern (or tuple of variable patterns)
    /// that matches the given param_ids exactly
    fn is_simple_param_pattern(&self, pat: &Pattern, param_ids: &[Ident]) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) => {
                // Single variable pattern
                param_ids.len() == 1 && id.name() == param_ids[0].name()
            }
            PatternDesc::Tpat_tuple(pats) => {
                // Tuple of patterns - check each matches the corresponding param_id
                if pats.len() != param_ids.len() {
                    return false;
                }
                pats.iter().zip(param_ids.iter()).all(|(p, id)| {
                    matches!(&p.pat_desc, PatternDesc::Tpat_var(pat_id, _) if pat_id.name() == id.name())
                })
            }
            PatternDesc::Tpat_any => {
                // Wildcard pattern - also simple
                param_ids.len() == 1
            }
            _ => false,
        }
    }

    /// Flatten nested functions based on arity.
    ///
    /// In OCaml/ReScript, `(x, y) => x + y` is represented in the typed tree as:
    /// ```
    /// Texp_function (arity=2)
    ///   params: [x]
    ///   body: Texp_function
    ///     params: [y]
    ///     body: x + y
    /// ```
    ///
    /// We use the arity to know how many nested functions to flatten into
    /// a single multi-parameter function.
    fn flatten_function_by_arity<'b>(
        &self,
        params: &'b [FunctionParam],
        cases: &'b [Case],
        partial: crate::types::typedtree::Partial,
        arity: crate::parser::ast::Arity,
    ) -> (
        Vec<&'b FunctionParam>,
        Option<&'b Expression>,
        crate::types::typedtree::Partial,
    ) {
        // Look up arity from arena (Arity is now ArityIdx)
        let target_arity = match self.arena.get_arity(arity) {
            Some(n) => n as usize,
            None => params.len(),
        };

        let mut all_params: Vec<&'b FunctionParam> = params.iter().collect();
        let mut current_partial = partial;

        // We need exactly one case with no guard to flatten
        if cases.len() != 1 || cases[0].c_guard.is_some() {
            // Can't flatten - return what we have
            return (all_params, cases.first().map(|c| &c.c_rhs), current_partial);
        }

        let mut current_body: &'b Expression = &cases[0].c_rhs;

        // Keep flattening while we haven't reached the target arity
        while all_params.len() < target_arity {
            match &current_body.exp_desc {
                ExpressionDesc::Texp_function {
                    params: inner_params,
                    body: inner_cases,
                    partial: inner_partial,
                    ..
                } => {
                    // Only flatten if there's exactly one case with no guard
                    if inner_cases.len() != 1 || inner_cases[0].c_guard.is_some() {
                        break;
                    }
                    all_params.extend(inner_params.iter());
                    current_partial = *inner_partial;
                    current_body = &inner_cases[0].c_rhs;
                }
                _ => break,
            }
        }

        (all_params, Some(current_body), current_partial)
    }

    fn param_pattern(param: &FunctionParam) -> Pattern {
        match &param.pat {
            FunctionParamPattern::Simple(pat) => pat.clone(),
            FunctionParamPattern::Nested(nested) => {
                let patterns = nested.iter().map(Self::param_pattern).collect::<Vec<_>>();
                if patterns.is_empty() {
                    Pattern::new(
                        PatternDesc::Tpat_any,
                        LocIdx::none(),
                        crate::types::TypeExprRef(0),
                        crate::types::typedtree::EnvRef(0),
                        Attributes::new(),
                    )
                } else if patterns.len() == 1 {
                    patterns.into_iter().next().unwrap()
                } else {
                    Pattern::new(
                        PatternDesc::Tpat_tuple(patterns),
                        LocIdx::none(),
                        crate::types::TypeExprRef(0),
                        crate::types::typedtree::EnvRef(0),
                        Attributes::new(),
                    )
                }
            }
        }
    }

    fn compile_match(
        &mut self,
        loc: Location,
        scrut: Lambda,
        cases: &[Case],
        partial: crate::types::typedtree::Partial,
    ) -> Lambda {
        let failure = match partial {
            crate::types::typedtree::Partial::Total => Lambda::unit(),
            crate::types::typedtree::Partial::Partial => self.match_failure(loc.clone()),
        };

        // Optimization: if scrutinee is already a variable, use it directly
        // to avoid creating unnecessary intermediate bindings
        let (scrut_var, wrap_let) = match &scrut {
            Lambda::Lvar(id) => (Lambda::var(id.clone()), None),
            _ => {
                let scrut_id = self.id_gen.create("match");
                let scrut_var = Lambda::var(scrut_id.clone());
                (scrut_var, Some(scrut_id))
            }
        };

        let mut result = failure;
        for case in cases.iter().rev() {
            let mut body = self.convert_expr(&case.c_rhs);
            if let Some(guard) = &case.c_guard {
                let guard_lam = self.convert_expr(guard);
                body = Lambda::if_(guard_lam, body, result.clone());
            }
            result = self.bind_pattern(&case.c_lhs, scrut_var.clone(), body, result);
        }

        // Only wrap in let if we created a new binding
        match wrap_let {
            Some(scrut_id) => Lambda::let_(LetKind::Strict, scrut_id, scrut, result),
            None => result,
        }
    }

    fn bind_pattern(
        &mut self,
        pat: &Pattern,
        scrut: Lambda,
        body: Lambda,
        failure: Lambda,
    ) -> Lambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_var(id, _) => {
                // Optimization: if binding to the same variable, skip the let
                if let Lambda::Lvar(scrut_id) = &scrut {
                    if scrut_id.name() == id.name() {
                        return body;
                    }
                }
                Lambda::let_(LetKind::Alias, id.clone(), scrut, body)
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner_bind = self.bind_pattern(inner, scrut.clone(), body, failure);
                Lambda::let_(LetKind::Alias, id.clone(), scrut, inner_bind)
            }
            PatternDesc::Tpat_constant(cst) => {
                let cst_lam = Lambda::const_(self.convert_constant(cst));
                let cond = Lambda::prim(
                    Primitive::Pjscomp(Comparison::Eq),
                    vec![scrut, cst_lam],
                    self.loc(pat.pat_loc),
                );
                Lambda::if_(cond, body, failure)
            }
            PatternDesc::Tpat_tuple(items) => {
                let tmp = self.id_gen.create("tuple");
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate().rev() {
                    let field = Lambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![Lambda::var(tmp.clone())],
                        pat_loc.clone(),
                    );
                    result = self.bind_pattern(item, field, result, failure.clone());
                }
                Lambda::let_(LetKind::Strict, tmp, scrut, result)
            }
            PatternDesc::Tpat_construct(_, cstr, args) => {
                self.bind_construct_pattern(pat, scrut, body, failure, cstr, args)
            }
            PatternDesc::Tpat_variant(tag, arg, _) => {
                let tmp = self.id_gen.create("poly");
                let pat_loc = self.loc(pat.pat_loc);
                let tag_check = Lambda::prim(
                    Primitive::Pjscomp(Comparison::Eq),
                    vec![
                        Lambda::prim(
                            Primitive::Pfield(0, FieldDbgInfo::PolyVarTag),
                            vec![Lambda::var(tmp.clone())],
                            pat_loc.clone(),
                        ),
                        Lambda::const_(Constant::Pointer(tag.clone())),
                    ],
                    pat_loc.clone(),
                );
                let mut body_with_arg = body;
                if let Some(arg_pat) = arg {
                    let payload = Lambda::prim(
                        Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                        vec![Lambda::var(tmp.clone())],
                        pat_loc.clone(),
                    );
                    body_with_arg =
                        self.bind_pattern(arg_pat, payload, body_with_arg, failure.clone());
                }
                let guarded = Lambda::if_(tag_check, body_with_arg, failure);
                Lambda::let_(LetKind::Strict, tmp, scrut, guarded)
            }
            PatternDesc::Tpat_record(fields, _closed) => {
                let tmp = self.id_gen.create("record");
                let mut result = body;
                for (lid, lbl, inner_pat, _optional) in fields.iter().rev() {
                    let field = Lambda::prim(
                        Primitive::Pfield(
                            lbl.lbl_pos,
                            FieldDbgInfo::Record {
                                name: lbl.lbl_name.clone(),
                                mutable_flag: to_parser_mutable(lbl.lbl_mut),
                            },
                        ),
                        vec![Lambda::var(tmp.clone())],
                        self.loc(lid.loc),
                    );
                    result = self.bind_pattern(inner_pat, field, result, failure.clone());
                }
                Lambda::let_(LetKind::Strict, tmp, scrut, result)
            }
            PatternDesc::Tpat_array(items) => {
                let tmp = self.id_gen.create("array");
                let pat_loc = self.loc(pat.pat_loc);
                let len_expr = Lambda::prim(
                    Primitive::Parraylength,
                    vec![Lambda::var(tmp.clone())],
                    pat_loc.clone(),
                );
                let len_cst = Lambda::const_(Constant::int(items.len() as i32));
                let len_cond = Lambda::prim(
                    Primitive::Pjscomp(Comparison::Eq),
                    vec![len_expr, len_cst],
                    pat_loc.clone(),
                );
                let mut result = body;
                for (idx, item) in items.iter().enumerate().rev() {
                    let field = Lambda::prim(
                        Primitive::Parrayrefs,
                        vec![
                            Lambda::var(tmp.clone()),
                            Lambda::const_(Constant::int(idx as i32)),
                        ],
                        pat_loc.clone(),
                    );
                    result = self.bind_pattern(item, field, result, failure.clone());
                }
                let guarded = Lambda::if_(len_cond, result, failure);
                Lambda::let_(LetKind::Strict, tmp, scrut, guarded)
            }
            PatternDesc::Tpat_or(p1, p2, _) => {
                let right = self.bind_pattern(p2, scrut.clone(), body.clone(), failure);
                self.bind_pattern(p1, scrut, body, right)
            }
        }
    }

    fn bind_construct_pattern(
        &mut self,
        pat: &Pattern,
        scrut: Lambda,
        body: Lambda,
        failure: Lambda,
        cstr: &ConstructorDescription,
        args: &[Pattern],
    ) -> Lambda {
        let pat_loc = self.loc(pat.pat_loc);
        match &cstr.cstr_tag {
            ConstructorTag::CstrConstant(_tag) => {
                // Compare against the same value we'd generate: string for variants, bool for true/false
                let tag_const = match cstr.cstr_name.as_str() {
                    "true" => Constant::JsTrue,
                    "false" => Constant::JsFalse,
                    _ => Constant::Pointer(cstr.cstr_name.clone()),
                };
                let cond = Lambda::prim(
                    Primitive::Pjscomp(Comparison::Eq),
                    vec![scrut, Lambda::const_(tag_const)],
                    pat_loc,
                );
                Lambda::if_(cond, body, failure)
            }
            ConstructorTag::CstrBlock(_tag) => {
                let tmp = self.id_gen.create("ctor");
                // Access the TAG field and compare against the constructor name string
                let tag_expr = Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::VariantTag),
                    vec![Lambda::var(tmp.clone())],
                    pat_loc.clone(),
                );
                let tag_cond = Lambda::prim(
                    Primitive::Pjscomp(Comparison::Eq),
                    vec![
                        tag_expr,
                        Lambda::const_(Constant::Pointer(cstr.cstr_name.clone())),
                    ],
                    pat_loc.clone(),
                );
                let mut result = body;
                for (idx, arg_pat) in args.iter().enumerate().rev() {
                    let field = Lambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Variant),
                        vec![Lambda::var(tmp.clone())],
                        pat_loc.clone(),
                    );
                    result = self.bind_pattern(arg_pat, field, result, failure.clone());
                }
                let guarded = Lambda::if_(tag_cond, result, failure);
                Lambda::let_(LetKind::Strict, tmp, scrut, guarded)
            }
            ConstructorTag::CstrUnboxed => {
                if let [single] = args {
                    self.bind_pattern(single, scrut, body, failure)
                } else {
                    body
                }
            }
            ConstructorTag::CstrExtension(_) => body,
        }
    }

    fn convert_construct(
        &mut self,
        loc: Location,
        cstr: &ConstructorDescription,
        args: &[Expression],
    ) -> Lambda {
        match &cstr.cstr_tag {
            ConstructorTag::CstrConstant(_tag) => {
                // Special handling for booleans - they compile to JS true/false
                match cstr.cstr_name.as_str() {
                    "true" => Lambda::const_(Constant::JsTrue),
                    "false" => Lambda::const_(Constant::JsFalse),
                    // ReScript compiles other constant constructors to strings
                    _ => Lambda::const_(Constant::Pointer(cstr.cstr_name.clone())),
                }
            }
            ConstructorTag::CstrUnboxed => {
                if let Some(arg) = args.first() {
                    self.convert_expr(arg)
                } else {
                    Lambda::unit()
                }
            }
            ConstructorTag::CstrBlock(tag) => {
                let args_lam = args.iter().map(|e| self.convert_expr(e)).collect();
                let tag_info =
                    TagInfo::constructor(cstr.cstr_name.clone(), cstr.cstr_nonconsts, *tag);
                Lambda::prim(
                    Primitive::Pmakeblock(*tag, tag_info, Mutable::Immutable),
                    args_lam,
                    loc,
                )
            }
            ConstructorTag::CstrExtension(path) => {
                let mut all_args = Vec::with_capacity(args.len() + 1);
                all_args.push(self.translate_extension_path(path, loc.clone()));
                all_args.extend(args.iter().map(|e| self.convert_expr(e)));
                Lambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
                    all_args,
                    loc,
                )
            }
        }
    }

    fn convert_poly_variant(&mut self, tag: &str, arg: &Option<Box<Expression>>) -> Lambda {
        match arg {
            None => Lambda::const_(Constant::Pointer(tag.to_string())),
            Some(expr) => {
                let arg_lam = self.convert_expr(expr);
                Lambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::PolyVar(tag.to_string()), Mutable::Immutable),
                    vec![Lambda::const_(Constant::Pointer(tag.to_string())), arg_lam],
                    self.loc(expr.exp_loc),
                )
            }
        }
    }

    fn convert_record(
        &mut self,
        loc: Location,
        fields: &[(
            Located<LidentIdx>,
            LabelDescription,
            RecordLabelDefinition,
            bool,
        )],
        base: Option<&Expression>,
        logical_field_count: Option<usize>,
    ) -> Lambda {
        let mut values = vec![None; fields.len()];
        let base_lam = base.map(|e| self.convert_expr(e));

        for (idx, (lid, lbl, def, _opt)) in fields.iter().enumerate() {
            let value = match def {
                RecordLabelDefinition::Overridden(_, expr) => self.convert_expr(expr),
                RecordLabelDefinition::OmittedOptionalNone(_, _) => {
                    Lambda::const_(Constant::Pointer("0a".to_string()))
                }
                RecordLabelDefinition::Kept(_) => {
                    if let Some(base_expr) = &base_lam {
                        let field_pos = match lbl.lbl_repres {
                            RecordRepresentation::RecordExtension => idx as i32 + 1,
                            _ => idx as i32,
                        };
                        Lambda::prim(
                            Primitive::Pfield(
                                field_pos,
                                FieldDbgInfo::Record {
                                    name: lbl.lbl_name.clone(),
                                    mutable_flag: to_parser_mutable(lbl.lbl_mut),
                                },
                            ),
                            vec![base_expr.clone()],
                            self.loc(lid.loc),
                        )
                    } else {
                        Lambda::unit()
                    }
                }
            };
            values[idx] = Some(value);
        }

        let elements = values
            .into_iter()
            .map(|v| v.unwrap_or_else(Lambda::unit))
            .collect();

        let fields_info = fields
            .iter()
            .map(|(_, lbl, _, _)| (lbl.lbl_name.clone(), lbl.lbl_optional))
            .collect();

        let tag_info = TagInfo::Record {
            fields: fields_info,
            logical_field_count,
            mutable_flag: fields
                .iter()
                .find(|(_, lbl, _, _)| lbl.lbl_mut == TypeMutableFlag::Mutable)
                .map(|_| ParserMutableFlag::Mutable)
                .unwrap_or(ParserMutableFlag::Immutable),
        };

        Lambda::prim(
            Primitive::Pmakeblock(0, tag_info, Mutable::Immutable),
            elements,
            loc,
        )
    }

    fn expand_sparse_record_fields(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &[RecordField],
        omitted_loc: LocIdx,
    ) -> Vec<RecordField> {
        // OCaml compiler/ml/typecore.ml:2833-2842 stores omitted optionals in
        // the full `lbl_all` array, and compiler/ml/translcore.ml:1145-1191
        // lowers every slot. Sparse Rust typedtree nodes carry the shared
        // label array so this legacy converter keeps the same Lambda shape.
        let placeholder_lid = fields
            .first()
            .map(|(lid, _, _, _)| lid.clone())
            .unwrap_or_else(|| self.arena.placeholder_located(omitted_loc));
        let mut explicit_by_pos: std::collections::HashMap<usize, &RecordField> =
            std::collections::HashMap::with_capacity(fields.len());
        for field in fields {
            let pos = field.1.lbl_pos;
            if pos >= 0 {
                explicit_by_pos.insert(pos as usize, field);
            }
        }

        let mut expanded = Vec::with_capacity(all_labels.len());
        for (idx, label) in all_labels.iter().enumerate() {
            let pos = if label.lbl_pos >= 0 {
                label.lbl_pos as usize
            } else {
                idx
            };
            if let Some(field) = explicit_by_pos.get(&pos) {
                expanded.push((*field).clone());
            } else if label.lbl_optional {
                // Intentional Rust performance representation: reconstruct
                // the omitted optional `None` node that OCaml
                // compiler/ml/typecore.ml:2833-2842 stores eagerly in the
                // typedtree field list.
                let label_lid = Located {
                    txt: placeholder_lid.txt,
                    loc: omitted_loc,
                };
                expanded.push((
                    label_lid.clone(),
                    label.clone(),
                    RecordLabelDefinition::OmittedOptionalNone(label_lid, label.lbl_arg),
                    false,
                ));
            } else {
                let label_lid = Located {
                    txt: placeholder_lid.txt,
                    loc: omitted_loc,
                };
                expanded.push((
                    label_lid,
                    label.clone(),
                    RecordLabelDefinition::Kept(label.lbl_arg),
                    false,
                ));
            }
        }
        expanded
    }

    fn compact_sparse_record_fields_for_output(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &[RecordField],
    ) -> Vec<RecordField> {
        // If every selected label has a materialized slot, sorting by `lbl_pos`
        // preserves OCaml `lbl_all` field order without walking omitted fields.
        if fields.iter().all(|field| field.1.lbl_pos >= 0) {
            let mut compact = fields
                .iter()
                .filter(|field| !record_field_is_static_optional_none(&field.1, &field.2))
                .cloned()
                .collect::<Vec<_>>();
            compact.sort_by_key(|field| field.1.lbl_pos);
            return compact;
        }

        let mut compact = Vec::with_capacity(fields.len());
        for (idx, label) in all_labels.iter().enumerate() {
            let label_pos = if label.lbl_pos >= 0 {
                label.lbl_pos as usize
            } else {
                idx
            };
            let Some(field) = fields.iter().find(|field| {
                usize::try_from(field.1.lbl_pos).ok() == Some(label_pos)
                    || field.1.lbl_name == label.lbl_name
            }) else {
                continue;
            };
            if record_field_is_static_optional_none(&field.1, &field.2) {
                continue;
            }
            compact.push((*field).clone());
        }
        compact
    }

    fn sparse_record_fields_for_lambda(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &[RecordField],
        omitted_loc: LocIdx,
    ) -> (Vec<RecordField>, Option<usize>) {
        if self.preserve_expanded_sparse_records {
            (
                self.expand_sparse_record_fields(all_labels, fields, omitted_loc),
                None,
            )
        } else {
            (
                self.compact_sparse_record_fields_for_output(all_labels, fields),
                Some(all_labels.len()),
            )
        }
    }

    fn translate_extension_path(&self, path: &crate::types::Path, loc: Location) -> Lambda {
        match path {
            crate::types::Path::Pident(id) => {
                if id.is_global() {
                    Lambda::global_module(id.clone(), false)
                } else {
                    Lambda::var(id.clone())
                }
            }
            crate::types::Path::Pdot(prefix, name, pos) => {
                let prefix_lam = self.translate_extension_path(prefix, loc.clone());
                Lambda::prim(
                    Primitive::Pfield(*pos, FieldDbgInfo::Module { name: name.clone() }),
                    vec![prefix_lam],
                    loc,
                )
            }
            crate::types::Path::Papply(_, _) => Lambda::unit(),
        }
    }

    fn translate_value_path(&self, loc_idx: LocIdx, path: &crate::types::Path) -> Lambda {
        if let Some(lam) = self.value_path_loc_constant(path, loc_idx) {
            return lam;
        }
        match path {
            crate::types::Path::Pident(id) => {
                if id.is_global() {
                    Lambda::global_module(id.clone(), false)
                } else {
                    Lambda::var(id.clone())
                }
            }
            crate::types::Path::Pdot(prefix, name, _) => {
                let prefix_lam = self.translate_value_path(loc_idx, prefix);
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Module { name: name.clone() }),
                    vec![prefix_lam],
                    self.loc(loc_idx),
                )
            }
            crate::types::Path::Papply(_, _) => Lambda::unit(),
        }
    }

    fn translate_primitive(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
    ) -> Lambda {
        if prim.prim_name == "%null" && prim.prim_arity == 0 {
            return Lambda::const_(Constant::JsNull);
        }
        if prim.prim_name == "%undefined" && prim.prim_arity == 0 {
            return Lambda::const_(Constant::JsUndefined { is_unit: false });
        }
        if let Some(primitive) = self.primitive_from_name(&prim.prim_name) {
            if prim.prim_arity == 0 {
                return Lambda::prim(primitive, vec![], loc);
            }
            let params = (0..prim.prim_arity)
                .map(|i| self.id_gen.create(&format!("prim{}", i)))
                .collect::<Vec<_>>();
            let args = params.iter().cloned().map(Lambda::var).collect::<Vec<_>>();
            let body = Lambda::prim(primitive, args, loc);
            return Lambda::function_(prim.prim_arity, params, body, FunctionAttribute::default());
        }

        // Fallback to an external call placeholder.
        let prim = Primitive::PjsCall {
            prim_name: prim.prim_name.clone(),
            arg_types: decoded_external_arg_types(&prim.prim_native_name, prim.prim_arity as usize),
            ffi: decoded_external_ffi_spec(&prim.prim_native_name),
            dynamic_import: false,
            transformed_jsx: false,
        };
        Lambda::prim(prim, vec![], loc)
    }

    pub(crate) fn primitive_from_name(&self, name: &str) -> Option<Primitive> {
        use Primitive::*;
        Some(match name {
            "%sequand" => Psequand,
            "%sequor" => Psequor,
            "%identity" => Pidentity,
            "%ignore" => Pignore,
            "%boolnot" => Pnot,
            "%obj_is_int" => Pisint,
            "%negint" => Pnegint,
            "%succint" => Poffsetint(1),
            "%predint" => Poffsetint(-1),
            "%addint" => Paddint,
            "%subint" => Psubint,
            "%mulint" => Pmulint,
            "%divint" => Pdivint,
            "%modint" => Pmodint,
            "%andint" => Pandint,
            "%orint" => Porint,
            "%xorint" => Pxorint,
            "%lslint" => Plslint,
            "%lsrint" => Plsrint,
            "%asrint" => Pasrint,
            "%eq" => Pintcomp(Comparison::Eq),
            "%noteq" => Pintcomp(Comparison::Neq),
            "%ltint" => Pintcomp(Comparison::Lt),
            "%leint" => Pintcomp(Comparison::Le),
            "%gtint" => Pintcomp(Comparison::Gt),
            "%geint" => Pintcomp(Comparison::Ge),
            "%intorder" => Pintorder,
            "%intmin" => Pintmin,
            "%intmax" => Pintmax,
            "%negfloat" => Pnegfloat,
            "%addfloat" => Paddfloat,
            "%subfloat" => Psubfloat,
            "%mulfloat" => Pmulfloat,
            "%divfloat" => Pdivfloat,
            "%modfloat" => Pmodfloat,
            "%powfloat" => Ppowfloat,
            "%eqfloat" => Pfloatcomp(Comparison::Eq),
            "%noteqfloat" => Pfloatcomp(Comparison::Neq),
            "%ltfloat" => Pfloatcomp(Comparison::Lt),
            "%lefloat" => Pfloatcomp(Comparison::Le),
            "%gtfloat" => Pfloatcomp(Comparison::Gt),
            "%gefloat" => Pfloatcomp(Comparison::Ge),
            "%string_length" => Pstringlength,
            "%string_safe_get" => Pstringrefs,
            "%string_unsafe_get" => Pstringrefu,
            "%string_concat" => Pstringadd,
            "%stringorder" => Pstringorder,
            "%stringmin" => Pstringmin,
            "%stringmax" => Pstringmax,
            "%array_length" => Parraylength,
            "%array_safe_get" => Parrayrefs,
            "%array_safe_set" => Parraysets,
            "%array_unsafe_get" => Parrayrefu,
            "%array_unsafe_set" => Parraysetu,
            "%makedict" => Pmakedict,
            "%dict_has" => PdictHas,
            "%await" => Pawait,
            "%import" => Pimport,
            "%hash" => Phash,
            "%hash_mix_int" => PhashMixint,
            "%hash_mix_string" => PhashMixstring,
            "%hash_final_mix" => PhashFinalmix,
            "%typeof" => Ptypeof,
            "%debugger" => Pdebugger,
            "%intoffloat" => Pintoffloat,
            "%floatofint" => Pfloatofint,
            "%unsafe_eq" => Pjscomp(Comparison::Eq),
            "%unsafe_neq" => Pjscomp(Comparison::Neq),
            "%unsafe_lt" => Pjscomp(Comparison::Lt),
            "%unsafe_le" => Pjscomp(Comparison::Le),
            "%unsafe_gt" => Pjscomp(Comparison::Gt),
            "%unsafe_ge" => Pjscomp(Comparison::Ge),
            "%is_nullable" => PisNullUndefined,
            "%null_to_opt" => PnullToOpt,
            "%nullable_to_opt" => PnullUndefinedToOpt,
            "%function_arity" => PfnArity,
            "%wrap_exn" => PwrapExn,
            "%curry_apply1" => PjsApply,
            "%curry_apply2" => PjsApply,
            "%curry_apply3" => PjsApply,
            "%curry_apply4" => PjsApply,
            "%curry_apply5" => PjsApply,
            "%curry_apply6" => PjsApply,
            "%curry_apply7" => PjsApply,
            "%curry_apply8" => PjsApply,
            "%makemutablelist" => Pmakelist,
            "%unsafe_to_method" => PjsFnMethod,
            "#raw_expr" => PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                code: String::new(),
                is_stmt: false,
            }),
            "#raw_stmt" => PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                code: String::new(),
                is_stmt: true,
            }),
            "#null" => PnullToOpt,
            "#undefined" => PisUndefined,
            "#typeof" => Ptypeof,
            "#is_nullable" => PisNullUndefined,
            "#null_to_opt" => PnullToOpt,
            "#nullable_to_opt" => PnullUndefinedToOpt,
            "#makemutablelist" => Pmakelist,
            "#import" => Pimport,
            "%obj_tag" => Pobjtag,
            "%obj_size" => Pobjsize,
            "%obj_dup" => Pduprecord,
            "%obj_get_field" => Parrayrefu,
            "%obj_set_field" => Parraysetu,
            "%raise" => Praise,
            _ => return None,
        })
    }

    pub(crate) fn value_path_loc_constant(
        &self,
        path: &crate::types::Path,
        loc_idx: LocIdx,
    ) -> Option<Lambda> {
        let crate::types::Path::Pdot(prefix, name, _) = path else {
            return None;
        };
        let crate::types::Path::Pident(id) = &**prefix else {
            return None;
        };
        if id.name() != "Pervasives" {
            return None;
        }
        let loc = self.loc(loc_idx);
        let file = self.basename_for_loc(loc.clone());
        let line = loc.loc_start.line;
        let start_col = loc.loc_start.column();
        let end_col = loc.loc_end.cnum - loc.loc_start.cnum + start_col;
        match name.as_str() {
            "__FILE__" => Some(Lambda::const_(Constant::ImmString(file))),
            "__LINE__" => Some(Lambda::const_(Constant::int(line))),
            "__MODULE__" => Some(Lambda::const_(Constant::ImmString(
                if file.ends_with(".rei") {
                    file.trim_end_matches(".rei").to_string()
                } else {
                    file.trim_end_matches(".res").to_string()
                },
            ))),
            "__LOC__" => Some(Lambda::const_(Constant::ImmString(format!(
                "File {file:?}, line {line}, characters {start_col}-{end_col}"
            )))),
            "__POS__" => Some(Lambda::const_(Constant::Block {
                tag: 0,
                tag_info: TagInfo::Tuple,
                elements: vec![
                    Constant::ImmString(file),
                    Constant::int(line),
                    Constant::int(start_col),
                    Constant::int(end_col),
                ],
            })),
            _ => None,
        }
    }

    fn match_failure(&mut self, loc: Location) -> Lambda {
        self.raise_predef_exception("Match_failure", PREDEF_MATCH_FAILURE_STAMP, loc)
    }
}

fn to_parser_mutable(flag: TypeMutableFlag) -> ParserMutableFlag {
    match flag {
        TypeMutableFlag::Mutable => ParserMutableFlag::Mutable,
        TypeMutableFlag::Immutable => ParserMutableFlag::Immutable,
    }
}

fn decoded_external_ffi_spec(encoded: &str) -> ExternalFfiSpec {
    let ffi_marshaled = decode_marshaled_ffi_type(encoded);
    ExternalFfiSpec {
        kind: if !is_bs_primitive(encoded) {
            ExternalFfiKind::Normal
        } else if ffi_marshaled
            .as_ref()
            .is_some_and(ffi_marshaled_is_obj_create)
        {
            ExternalFfiKind::ObjCreate
        } else {
            ExternalFfiKind::Default
        },
        spec: ffi_marshaled.as_ref().and_then(ffi_marshaled_external_spec),
        obj_params: ffi_marshaled.as_ref().and_then(ffi_marshaled_obj_params),
        return_wrapper: ffi_marshaled
            .as_ref()
            .and_then(ffi_marshaled_return_wrapper)
            .unwrap_or(ExternalReturnWrapper::Identity),
        inline_constant: None,
    }
}

fn decoded_external_arg_types(encoded: &str, arity: usize) -> Vec<ExternalArgSpec> {
    decode_marshaled_ffi_type(encoded)
        .as_ref()
        .and_then(ffi_marshaled_arg_types)
        .unwrap_or_else(|| vec![ExternalArgSpec::dummy(); arity])
}

fn decode_marshaled_ffi_type(encoded: &str) -> Option<OcamlValue> {
    if encoded.is_empty() {
        return None;
    }
    let bytes = encoded.chars().map(|c| c as u32 as u8).collect::<Vec<_>>();
    let mut reader = MarshalReader::new();
    reader.read_from_bytes(&bytes).ok()
}

fn is_bs_primitive(encoded: &str) -> bool {
    let mut chars = encoded.chars();
    let first = chars.next().map(|c| c as u32 as u8);
    let second = chars.next().map(|c| c as u32 as u8);
    first == Some(0x84) && second == Some(0x95) && 2 + chars.count() >= 20
}

fn ffi_marshaled_is_obj_create(value: &OcamlValue) -> bool {
    matches!(value.as_block_opt(), Some((1, _)))
}

fn ffi_marshaled_arg_types(value: &OcamlValue) -> Option<Vec<ExternalArgSpec>> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 3 {
        return None;
    }
    decode_params(&fields[0])
}

fn ffi_marshaled_return_wrapper(value: &OcamlValue) -> Option<ExternalReturnWrapper> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 3 {
        return None;
    }
    match fields[1].as_int() {
        0 | 1 => Some(ExternalReturnWrapper::Identity),
        2 => Some(ExternalReturnWrapper::NullToOpt),
        3 => Some(ExternalReturnWrapper::NullUndefinedToOpt),
        4 => Some(ExternalReturnWrapper::ReplacedWithUnit),
        _ => None,
    }
}

fn ffi_marshaled_external_spec(value: &OcamlValue) -> Option<ExternalSpec> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 3 {
        return None;
    }
    decode_external_spec(&fields[2])
}

fn ffi_marshaled_obj_params(value: &OcamlValue) -> Option<Vec<ExternalObjSpec>> {
    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (1, [params]) => Some(
            params
                .as_list()
                .into_iter()
                .filter_map(decode_obj_param)
                .collect(),
        ),
        _ => None,
    }
}

fn decode_params(value: &OcamlValue) -> Option<Vec<ExternalArgSpec>> {
    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (0, [params]) => Some(
            params
                .as_list()
                .into_iter()
                .filter_map(decode_param)
                .collect(),
        ),
        (1, [arity]) => Some(vec![
            ExternalArgSpec::dummy();
            arity.as_int().max(0) as usize
        ]),
        _ => None,
    }
}

fn decode_param(value: &OcamlValue) -> Option<ExternalArgSpec> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 2 {
        return None;
    }
    Some(ExternalArgSpec {
        arg_type: decode_arg_attr(&fields[0])?,
        arg_label: decode_arg_label(&fields[1])?,
    })
}

fn decode_obj_param(value: &OcamlValue) -> Option<ExternalObjSpec> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 2 {
        return None;
    }
    Some(ExternalObjSpec {
        obj_arg_type: decode_arg_attr(&fields[0])?,
        obj_arg_label: decode_obj_label(&fields[1])?,
    })
}

fn decode_arg_attr(value: &OcamlValue) -> Option<ExternalArgAttr> {
    if let OcamlValue::Int(tag) = value {
        return match *tag {
            0 => Some(ExternalArgAttr::ExternUnit),
            1 => Some(ExternalArgAttr::Nothing),
            2 => Some(ExternalArgAttr::Ignore),
            3 => Some(ExternalArgAttr::Unwrap),
            _ => None,
        };
    }

    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (0, [descr]) => Some(ExternalArgAttr::PolyVarString {
            descr: decode_string_pair_list(descr),
        }),
        (1, [descr]) => Some(ExternalArgAttr::PolyVar {
            descr: descr.as_option().map(decode_string_pair_list),
        }),
        (2, [descr]) => Some(ExternalArgAttr::Int(
            descr
                .as_list()
                .into_iter()
                .filter_map(|entry| {
                    let (entry_tag, entry_fields) = entry.as_block_opt()?;
                    if entry_tag != 0 || entry_fields.len() != 2 {
                        return None;
                    }
                    Some((
                        entry_fields[0].as_string().to_string(),
                        entry_fields[1].as_int(),
                    ))
                })
                .collect(),
        )),
        (3, [cst]) => Some(ExternalArgAttr::ArgCst(decode_arg_const(cst)?)),
        _ => None,
    }
}

fn decode_arg_const(value: &OcamlValue) -> Option<ExternalArgConst> {
    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (0, [i]) => Some(ExternalArgConst::IntLit(i.as_int())),
        (1, [s, delim]) => Some(ExternalArgConst::StringLit(
            s.as_string().to_string(),
            decode_arg_delim(delim)?,
        )),
        _ => None,
    }
}

fn decode_arg_delim(value: &OcamlValue) -> Option<ExternalArgDelim> {
    match value.as_int() {
        0 => Some(ExternalArgDelim::None),
        1 => Some(ExternalArgDelim::StarJ),
        2 => Some(ExternalArgDelim::NoQuotes),
        3 => Some(ExternalArgDelim::BackQuotes),
        _ => None,
    }
}

fn decode_arg_label(value: &OcamlValue) -> Option<ExternalArgLabel> {
    match value.as_int() {
        0 => Some(ExternalArgLabel::Label),
        1 => Some(ExternalArgLabel::Empty),
        2 => Some(ExternalArgLabel::Optional),
        _ => None,
    }
}

fn decode_obj_label(value: &OcamlValue) -> Option<ExternalObjLabel> {
    if let OcamlValue::Int(0) = value {
        return Some(ExternalObjLabel::Empty);
    }

    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (0, [name]) => Some(ExternalObjLabel::Label {
            name: name.as_string().to_string(),
        }),
        (1, [name, for_sure_no_nested_option]) => Some(ExternalObjLabel::Optional {
            name: name.as_string().to_string(),
            for_sure_no_nested_option: for_sure_no_nested_option.as_bool(),
        }),
        _ => None,
    }
}

fn decode_external_spec(value: &OcamlValue) -> Option<ExternalSpec> {
    let (tag, fields) = value.as_block_opt()?;
    match (tag, fields) {
        (0, [name, external_module_name, scopes]) => Some(ExternalSpec::JsVar {
            name: name.as_string().to_string(),
            external_module_name: external_module_name
                .as_option()
                .and_then(decode_external_module_name),
            scopes: decode_string_list(scopes),
        }),
        (1, [external_module_name]) => Some(ExternalSpec::JsModuleAsVar(
            decode_external_module_name(external_module_name)?,
        )),
        (2, [external_module_name, splice]) => Some(ExternalSpec::JsModuleAsFn {
            external_module_name: decode_external_module_name(external_module_name)?,
            splice: splice.as_bool(),
        }),
        (3, [external_module_name]) => Some(ExternalSpec::JsModuleAsClass(
            decode_external_module_name(external_module_name)?,
        )),
        (4, [name, external_module_name, splice, scopes, tagged_template]) => {
            Some(ExternalSpec::JsCall {
                name: name.as_string().to_string(),
                external_module_name: external_module_name
                    .as_option()
                    .and_then(decode_external_module_name),
                splice: splice.as_bool(),
                scopes: decode_string_list(scopes),
                tagged_template: tagged_template.as_bool(),
            })
        }
        (5, [name, splice, scopes]) => Some(ExternalSpec::JsSend {
            name: name.as_string().to_string(),
            splice: splice.as_bool(),
            js_send_scopes: decode_string_list(scopes),
        }),
        (6, [name, external_module_name, splice, scopes]) => Some(ExternalSpec::JsNew {
            name: name.as_string().to_string(),
            external_module_name: external_module_name
                .as_option()
                .and_then(decode_external_module_name),
            splice: splice.as_bool(),
            scopes: decode_string_list(scopes),
        }),
        (7, [name, scopes]) => Some(ExternalSpec::JsSet {
            js_set_name: name.as_string().to_string(),
            js_set_scopes: decode_string_list(scopes),
        }),
        (8, [name, scopes]) => Some(ExternalSpec::JsGet {
            js_get_name: name.as_string().to_string(),
            js_get_scopes: decode_string_list(scopes),
        }),
        (9, [scopes]) => Some(ExternalSpec::JsGetIndex {
            js_get_index_scopes: decode_string_list(scopes),
        }),
        (10, [scopes]) => Some(ExternalSpec::JsSetIndex {
            js_set_index_scopes: decode_string_list(scopes),
        }),
        _ => None,
    }
}

fn decode_external_module_name(value: &OcamlValue) -> Option<ExternalModuleName> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 || fields.len() != 3 {
        return None;
    }
    Some(ExternalModuleName {
        bundle: fields[0].as_string().to_string(),
        module_bind_name: decode_module_bind_name(&fields[1])?,
        import_attributes: fields[2].as_option().and_then(decode_import_attributes),
    })
}

fn decode_module_bind_name(value: &OcamlValue) -> Option<ExternalModuleBindName> {
    match value {
        OcamlValue::Int(0) => Some(ExternalModuleBindName::Nothing),
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(
            ExternalModuleBindName::HintName(fields[0].as_string().to_string()),
        ),
        _ => None,
    }
}

fn decode_import_attributes(value: &OcamlValue) -> Option<ImportAttributes> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 0 {
        return None;
    }
    let bucket_array = match fields {
        [_, bucket_array, _] | [_, bucket_array, _, _] => bucket_array,
        _ => return None,
    };
    let (_, buckets) = bucket_array.as_block_opt()?;
    let mut attrs = Vec::new();
    for bucket in buckets {
        decode_bucket_list(bucket, &mut attrs)?;
    }
    Some(attrs)
}

fn decode_bucket_list(value: &OcamlValue, out: &mut ImportAttributes) -> Option<()> {
    match value {
        OcamlValue::Int(0) => Some(()),
        OcamlValue::Block(0, fields) if fields.len() == 3 => {
            out.push((
                fields[0].as_string().to_string(),
                fields[1].as_string().to_string(),
            ));
            decode_bucket_list(&fields[2], out)
        }
        _ => None,
    }
}

fn decode_string_list(value: &OcamlValue) -> Vec<String> {
    value
        .as_list()
        .into_iter()
        .map(|item| item.as_string().to_string())
        .collect()
}

fn decode_string_pair_list(value: &OcamlValue) -> Vec<(String, String)> {
    value
        .as_list()
        .into_iter()
        .filter_map(|entry| {
            let (tag, fields) = entry.as_block_opt()?;
            if tag != 0 || fields.len() != 2 {
                return None;
            }
            Some((
                fields[0].as_string().to_string(),
                fields[1].as_string().to_string(),
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_ast::ffi_types::{ExternalSpec, FfiType, ReturnWrapper, encode_ffi_type};
    use crate::ident::Ident;
    use crate::parse_arena::{Located, ParseArena};
    use crate::parser::longident::Longident;
    use crate::types::typedtree::{Expression, ExpressionDesc};

    #[test]
    fn test_convert_constant_int() {
        let arena = ParseArena::new();
        let mut conv = LambdaConverter::new(&arena);
        let expr = Expression::new(
            ExpressionDesc::Texp_constant(TConstant::Int(42)),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            crate::types::typedtree::EnvRef(0),
            Attributes::new(),
        );
        let lam = conv.convert_expr(&expr);
        match lam {
            Lambda::Lconst(Constant::Int { i, .. }) => assert_eq!(i, 42),
            _ => panic!("expected int constant"),
        }
    }

    #[test]
    fn test_convert_let_var() {
        use crate::parser::longident::Longident;
        let mut arena = ParseArena::new();
        let x_idx = arena.intern("x");
        let lid_idx = arena.push_longident(Longident::Lident(x_idx));
        let mut conv = LambdaConverter::new(&arena);
        let id = Ident::create_local("x");
        let pat = Pattern::new(
            PatternDesc::Tpat_var(id.clone(), Located::mknoloc("x".to_string())),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            crate::types::typedtree::EnvRef(0),
            Attributes::new(),
        );
        let vb = ValueBinding {
            vb_pat: pat,
            vb_expr: Expression::new(
                ExpressionDesc::Texp_constant(TConstant::Int(1)),
                LocIdx::none(),
                crate::types::TypeExprRef(0),
                crate::types::typedtree::EnvRef(0),
                Attributes::new(),
            ),
            vb_attributes: Attributes::new(),
            vb_loc: LocIdx::none(),
        };
        let body = Expression::new(
            ExpressionDesc::Texp_ident(
                crate::types::Path::pident(id.clone()),
                Located::mknoloc(lid_idx),
                crate::types::ValueDescription {
                    val_type: crate::types::TypeExprRef(0),
                    val_kind: ValueKind::ValReg,
                    val_loc: Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                },
            ),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            crate::types::typedtree::EnvRef(0),
            Attributes::new(),
        );
        let expr = Expression::new(
            ExpressionDesc::Texp_let(RecFlag::Nonrecursive, vec![vb], Box::new(body)),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            crate::types::typedtree::EnvRef(0),
            Attributes::new(),
        );
        let lam = conv.convert_expr(&expr);
        match lam {
            Lambda::Llet(_, _, _, _) => {}
            _ => panic!("expected let binding"),
        }
    }

    #[test]
    fn decoded_external_ffi_spec_reads_null_to_opt_wrapper() {
        let spec = decoded_external_ffi_spec(&encode_ffi_type(&FfiType::FfiBs {
            params: crate::binary_ast::ffi_types::Params::ParamNumber(1),
            return_wrapper: ReturnWrapper::ReturnNullToOpt,
            external_spec: ExternalSpec::JsGet {
                js_get_name: "x".to_string(),
                js_get_scopes: Vec::new(),
            },
        }));

        assert_eq!(spec.return_wrapper, ExternalReturnWrapper::NullToOpt);
    }
}
