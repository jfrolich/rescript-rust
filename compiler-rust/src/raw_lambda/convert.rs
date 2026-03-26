//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::Constant;
use crate::lambda::compat::LetKind;
use crate::lambda::convert::LambdaConverter;
use crate::lambda::primitive::{ExternalArgSpec, ExternalFfiSpec, Mutable};
use crate::lambda::tag_info::TagInfo;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, Lambda, Primitive,
};
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Arity;
use crate::raw_lambda::RawLambda;
use crate::types::ConstructorTag;
use crate::types::decl::ValueKind;
use crate::types::typedtree::{
    ApplyArg, Case, Expression, ExpressionDesc, FunctionParam, FunctionParamPattern, Partial,
    Pattern, PatternDesc, Structure, StructureItem, StructureItemDesc, ValueBinding,
};

fn iter_bound_pattern_idents<'a, F>(pat: &'a Pattern, f: &mut F)
where
    F: FnMut(&'a Ident),
{
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => f(id),
        PatternDesc::Tpat_alias(inner, id, _) => {
            iter_bound_pattern_idents(inner, f);
            f(id);
        }
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => {
            for pat in pats {
                iter_bound_pattern_idents(pat, f);
            }
        }
        PatternDesc::Tpat_record(fields, _) => {
            for (_, _, pat, _) in fields {
                iter_bound_pattern_idents(pat, f);
            }
        }
        PatternDesc::Tpat_variant(_, Some(inner), _) => iter_bound_pattern_idents(inner, f),
        PatternDesc::Tpat_or(left, _, _) => iter_bound_pattern_idents(left, f),
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_variant(_, None, _) => {}
    }
}

fn rev_let_bound_idents(bindings: &[ValueBinding]) -> Vec<Ident> {
    let mut ids = Vec::new();
    for binding in bindings {
        iter_bound_pattern_idents(&binding.vb_pat, &mut |id| ids.push(id.clone()));
    }
    ids.reverse();
    ids
}

fn simple_let_binding_id(binding: &ValueBinding) -> Option<Ident> {
    match &binding.vb_pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id.clone()),
        PatternDesc::Tpat_alias(inner, id, _) if matches!(inner.pat_desc, PatternDesc::Tpat_any) => {
            Some(id.clone())
        }
        _ => None,
    }
}

/// Converter from typedtree to raw lambda.
pub struct RawLambdaConverter<'a> {
    arena: &'a ParseArena,
    id_gen: IdGenerator,
    lowered: LambdaConverter<'a>,
}

impl<'a> RawLambdaConverter<'a> {
    /// Create a new raw-lambda converter.
    pub fn new(arena: &'a ParseArena) -> Self {
        Self {
            arena,
            id_gen: IdGenerator::new(),
            lowered: LambdaConverter::new(arena),
        }
    }

    /// Create a new raw-lambda converter with stamps continuing from an existing phase.
    pub fn with_start_stamp(arena: &'a ParseArena, start_stamp: i32) -> Self {
        Self {
            arena,
            id_gen: IdGenerator::with_start_stamp(start_stamp),
            lowered: LambdaConverter::with_start_stamp(arena, start_stamp),
        }
    }

    #[inline]
    fn loc(&self, idx: LocIdx) -> Location {
        self.arena.to_location(idx)
    }

    /// Convert a structure into raw lambda.
    pub fn convert_structure(&mut self, structure: &Structure) -> RawLambda {
        RawLambda::from_lowered(self.convert_structure_items(Vec::new(), &structure.str_items))
    }

    fn convert_structure_items(&mut self, fields: Vec<Ident>, items: &[StructureItem]) -> Lambda {
        let Some((item, rem)) = items.split_first() else {
            let export_ids: Vec<Ident> = fields.iter().rev().cloned().collect();
            let block_fields = export_ids.iter().cloned().map(Lambda::var).collect();
            return Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::ModuleExport(export_ids), Mutable::Immutable),
                block_fields,
                Location::none(),
            );
        };

        match &item.str_desc {
            StructureItemDesc::Tstr_eval(expr, _) => {
                let body = self.convert_structure_items(fields, rem);
                Lambda::seq(self.convert_expr(expr), body)
            }
            StructureItemDesc::Tstr_value(rec_flag, bindings) => {
                let mut ext_fields = rev_let_bound_idents(bindings);
                ext_fields.extend(fields);
                let body = self.convert_structure_items(ext_fields, rem);
                self.convert_let_with_body(*rec_flag, bindings, body)
            }
            StructureItemDesc::Tstr_primitive(_)
            | StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_typext(_)
            | StructureItemDesc::Tstr_exception(_)
            | StructureItemDesc::Tstr_module(_)
            | StructureItemDesc::Tstr_recmodule(_)
            | StructureItemDesc::Tstr_modtype(_)
            | StructureItemDesc::Tstr_open(_)
            | StructureItemDesc::Tstr_include(_)
            | StructureItemDesc::Tstr_attribute(_) => self.convert_structure_items(fields, rem),
        }
    }

    fn convert_expr(&mut self, expr: &Expression) -> Lambda {
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(_, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => self.translate_primitive(self.loc(expr.exp_loc), prim),
                ValueKind::ValReg => self.lowered.convert_expr(expr),
            },
            ExpressionDesc::Texp_let(rec_flag, bindings, body) => {
                let body_lam = self.convert_expr(body);
                self.convert_let_with_body(*rec_flag, bindings, body_lam)
            }
            ExpressionDesc::Texp_function {
                params,
                body,
                partial,
                arity,
                ..
            } if body.len() == 1 && body[0].c_guard.is_none() => {
                self.convert_function(params, body, *partial, *arity, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => self.convert_apply(
                self.loc(expr.exp_loc),
                funct,
                args,
                *partial,
                *transformed_jsx,
            ),
            ExpressionDesc::Texp_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(_) | ConstructorTag::CstrUnboxed => {
                    self.convert_construct(self.loc(expr.exp_loc), cstr, args)
                }
                _ => self.lowered.convert_expr(expr),
            },
            _ => self.lowered.convert_expr(expr),
        }
    }

    fn convert_let_with_body(
        &mut self,
        rec_flag: crate::parser::ast::RecFlag,
        bindings: &[ValueBinding],
        body: Lambda,
    ) -> Lambda {
        match rec_flag {
            crate::parser::ast::RecFlag::Nonrecursive => {
                if bindings.iter().all(|binding| simple_let_binding_id(binding).is_some()) {
                    bindings.iter().rev().fold(body, |acc, binding| {
                        let id = simple_let_binding_id(binding).expect("checked above");
                        let value = self.convert_expr(&binding.vb_expr);
                        Lambda::let_(LetKind::Strict, id, value, acc)
                    })
                } else {
                    self.lowered.convert_let_with_body(rec_flag, bindings, body)
                }
            }
            crate::parser::ast::RecFlag::Recursive => {
                if bindings.iter().all(|binding| simple_let_binding_id(binding).is_some()) {
                    let lam_bindings = bindings
                        .iter()
                        .map(|binding| {
                            (
                                simple_let_binding_id(binding).expect("checked above"),
                                self.convert_expr(&binding.vb_expr),
                            )
                        })
                        .collect();
                    Lambda::letrec(lam_bindings, body)
                } else {
                    self.lowered.convert_let_with_body(rec_flag, bindings, body)
                }
            }
        }
    }

    fn convert_function(
        &mut self,
        params: &[FunctionParam],
        cases: &[Case],
        partial: Partial,
        arity: Arity,
        loc: Location,
    ) -> Lambda {
        let (all_params, final_body, _partial) =
            self.flatten_function_by_arity(params, cases, partial, arity);

        let mut param_ids = Vec::new();
        for (idx, param) in all_params.iter().enumerate() {
            let pat = Self::param_pattern(param);
            let id = match &pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => id.clone(),
                _ => self.id_gen.create(&format!("param{idx}")),
            };
            param_ids.push(id);
        }

        let body = final_body.map(|expr| self.convert_expr(expr)).unwrap_or_else(Lambda::unit);
        let lambda = Lambda::function_(
            param_ids.len() as i32,
            param_ids,
            body,
            FunctionAttribute::default(),
        );

        match self.arena.get_arity(arity) {
            Some(n) => Lambda::prim(Primitive::PjsFnMake(n as i32), vec![lambda], loc),
            None => lambda,
        }
    }

    fn flatten_function_by_arity<'b>(
        &self,
        params: &'b [FunctionParam],
        cases: &'b [Case],
        partial: Partial,
        arity: Arity,
    ) -> (Vec<&'b FunctionParam>, Option<&'b Expression>, Partial) {
        let target_arity = match self.arena.get_arity(arity) {
            Some(n) => n as usize,
            None => params.len(),
        };

        if cases.len() != 1 || cases[0].c_guard.is_some() {
            return (params.iter().collect(), cases.first().map(|case| &case.c_rhs), partial);
        }

        let mut all_params: Vec<&'b FunctionParam> = params.iter().collect();
        let mut current_partial = partial;
        let mut current_body = &cases[0].c_rhs;

        while all_params.len() < target_arity {
            match &current_body.exp_desc {
                ExpressionDesc::Texp_function {
                    params: inner_params,
                    body: inner_cases,
                    partial: inner_partial,
                    ..
                } if inner_cases.len() == 1 && inner_cases[0].c_guard.is_none() => {
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
                if patterns.len() == 1 {
                    patterns.into_iter().next().unwrap()
                } else {
                    Pattern::new(
                        PatternDesc::Tpat_tuple(patterns),
                        LocIdx::none(),
                        crate::types::TypeExprRef(0),
                        crate::types::typedtree::EnvRef(0),
                        crate::parser::ast::Attributes::new(),
                    )
                }
            }
        }
    }

    fn convert_apply(
        &mut self,
        loc: Location,
        funct: &Expression,
        args: &[ApplyArg],
        _partial: bool,
        transformed_jsx: bool,
    ) -> Lambda {
        if let ExpressionDesc::Texp_ident(_, _, desc) = &funct.exp_desc {
            if let ValueKind::ValPrim(prim) = &desc.val_kind {
                let prim_arity = prim.prim_arity.max(0) as usize;
                if args.len() >= prim_arity
                    && args.iter().take(prim_arity).all(|arg| arg.expression.is_some())
                {
                    let (applied, rest) = args.split_at(prim_arity);
                    let applied_exprs = applied
                        .iter()
                        .map(|arg| arg.expression.as_ref().expect("checked above"))
                        .collect::<Vec<_>>();
                    let prim_args = applied_exprs
                        .iter()
                        .map(|expr| self.convert_expr(expr))
                        .collect::<Vec<_>>();
                    let prim = self.translate_primitive_application(prim, transformed_jsx);
                    let base = Lambda::prim(prim, prim_args, loc.clone());
                    return if rest.is_empty() {
                        base
                    } else {
                        self.transl_apply(base, rest, loc, transformed_jsx)
                    };
                }
            }
        }

        let funct_lam = self.convert_expr(funct);
        self.transl_apply(funct_lam, args, loc, transformed_jsx)
    }

    fn convert_construct(
        &mut self,
        _loc: Location,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
    ) -> Lambda {
        match &cstr.cstr_tag {
            ConstructorTag::CstrConstant(tag) => match cstr.cstr_name.as_str() {
                "true" => Lambda::const_(Constant::JsTrue),
                "false" => Lambda::const_(Constant::JsFalse),
                _ => {
                    // OCaml raw lambda prints constant constructors via their numeric
                    // pointer tag (`0a`, `1a`, ...). The lowered Lambda constant type
                    // does not preserve that pointer metadata, so the raw stage stores
                    // the printed pointer form directly.
                    let printed_tag = format!("{tag}a");
                    Lambda::const_(Constant::Pointer(printed_tag))
                }
            },
            ConstructorTag::CstrUnboxed => {
                if let Some(arg) = args.first() {
                    self.convert_expr(arg)
                } else {
                    Lambda::unit()
                }
            }
            ConstructorTag::CstrBlock(_) | ConstructorTag::CstrExtension(_) => {
                unreachable!("convert_construct is only used for raw constant/unboxed constructors")
            }
        }
    }

    fn transl_apply(
        &mut self,
        lam: Lambda,
        sargs: &[ApplyArg],
        loc: Location,
        transformed_jsx: bool,
    ) -> Lambda {
        fn lapply(loc: Location, func: Lambda, args: Vec<Lambda>, transformed_jsx: bool) -> Lambda {
            Lambda::Lapply(Apply {
                ap_func: Box::new(func),
                ap_args: args,
                ap_info: ApInfo {
                    loc,
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: transformed_jsx,
            })
        }

        fn is_simple(lam: &Lambda) -> bool {
            matches!(lam, Lambda::Lvar(_) | Lambda::Lconst(_))
        }

        fn may_map<T, U, F>(value: Option<T>, f: F) -> Option<U>
        where
            F: FnOnce(T) -> U,
        {
            value.map(f)
        }

        fn build_apply(
            conv: &mut RawLambdaConverter<'_>,
            lam: Lambda,
            mut args_rev: Vec<(Lambda, bool)>,
            pending: &[(Option<Lambda>, bool)],
            loc: Location,
            transformed_jsx: bool,
        ) -> Lambda {
            match pending.split_first() {
                Some(((None, optional), tail)) => {
                    let mut defs: Vec<(Ident, Lambda)> = Vec::new();
                    let protect = |conv: &mut RawLambdaConverter<'_>,
                                   name: &str,
                                   lam: Lambda,
                                   defs: &mut Vec<(Ident, Lambda)>| {
                        if is_simple(&lam) {
                            lam
                        } else {
                            let id = conv.id_gen.create(name);
                            defs.push((id.clone(), lam));
                            Lambda::var(id)
                        }
                    };

                    let all_optional = args_rev.iter().all(|(_, is_optional)| *is_optional);
                    let remaining_args = if all_optional {
                        std::mem::take(&mut args_rev)
                    } else {
                        Vec::new()
                    };
                    let applied = if args_rev.is_empty() {
                        lam
                    } else {
                        lapply(
                            loc.clone(),
                            lam,
                            args_rev.into_iter().rev().map(|(arg, _)| arg).collect(),
                            transformed_jsx,
                        )
                    };
                    let handle = protect(conv, "func", applied, &mut defs);
                    let protected_tail = tail
                        .iter()
                        .map(|(arg, is_optional)| {
                            (
                                arg.as_ref().map(|lam| {
                                    protect(conv, "arg", lam.clone(), &mut defs)
                                }),
                                *is_optional,
                            )
                        })
                        .collect::<Vec<_>>();
                    let id_arg = conv.id_gen.create("param");
                    let mut next_args_rev = Vec::with_capacity(1 + remaining_args.len());
                    next_args_rev.push((Lambda::var(id_arg.clone()), *optional));
                    next_args_rev.extend(remaining_args);
                    let body = match build_apply(
                        conv,
                        handle,
                        next_args_rev,
                        &protected_tail,
                        loc.clone(),
                        transformed_jsx,
                    ) {
                        Lambda::Lfunction(func) => Lambda::Lfunction(crate::lambda::LFunction {
                            arity: func.arity + 1,
                            params: std::iter::once(id_arg).chain(func.params).collect(),
                            body: func.body,
                            attr: func.attr,
                        }),
                        lam => Lambda::function_(
                            1,
                            vec![id_arg],
                            lam,
                            FunctionAttribute::default(),
                        ),
                    };
                    defs.into_iter().fold(body, |body, (id, lam)| {
                        Lambda::let_(LetKind::Strict, id, lam, body)
                    })
                }
                Some(((Some(arg), optional), tail)) => {
                    args_rev.insert(0, (arg.clone(), *optional));
                    build_apply(conv, lam, args_rev, tail, loc, transformed_jsx)
                }
                None => lapply(
                    loc,
                    lam,
                    args_rev.into_iter().rev().map(|(arg, _)| arg).collect(),
                    transformed_jsx,
                ),
            }
        }

        let pending = sargs
            .iter()
            .map(|arg| {
                (
                    may_map(arg.expression.clone(), |expr| self.convert_expr(&expr)),
                    arg.label.is_optional(),
                )
            })
            .collect::<Vec<_>>();
        build_apply(self, lam, Vec::new(), &pending, loc, transformed_jsx)
    }

    fn translate_primitive(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
    ) -> Lambda {
        let primitive = self.translate_primitive_application(prim, false);
        if prim.prim_arity == 0 {
            Lambda::prim(primitive, vec![], loc)
        } else {
            let params = if prim.prim_arity == 1 {
                vec![self.id_gen.create("prim")]
            } else {
                (0..prim.prim_arity)
                    .map(|i| self.id_gen.create(&format!("prim{i}")))
                    .collect::<Vec<_>>()
            };
            let args = params.iter().cloned().map(Lambda::var).collect();
            Lambda::function_(
                prim.prim_arity,
                params,
                Lambda::prim(primitive, args, loc),
                FunctionAttribute::default(),
            )
        }
    }

    fn translate_primitive_application(
        &self,
        prim: &crate::types::PrimitiveDescription,
        transformed_jsx: bool,
    ) -> Primitive {
        if let Some(primitive) = self.lowered.primitive_from_name(&prim.prim_name) {
            primitive
        } else {
            Primitive::PjsCall {
                prim_name: prim.prim_name.clone(),
                arg_types: vec![ExternalArgSpec { label: None }; prim.prim_arity.max(0) as usize],
                ffi: ExternalFfiSpec { module_name: None },
                dynamic_import: false,
                transformed_jsx,
            }
        }
    }
}
