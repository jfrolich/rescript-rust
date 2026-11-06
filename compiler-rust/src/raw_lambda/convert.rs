//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use crate::types::path::PathView;
use std::borrow::Cow;
use std::path::Path as StdPath;

use crate::context::IdGenerator;
use crate::diagnostics::{Warning, WarningConfig};
use crate::ident::{Ident, IdentFlags};
use crate::js_ir::{Kind, ModuleId};
use crate::lambda::Constant;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::{
    ConstructorRuntimeTag, ConstructorTag as PointerConstructorTag, PointerInfo,
};
use crate::lambda::lam_primitive::{ExternalModuleName, ImportSource, Mutable};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{
    ApInfo, ApplyStatus, FieldDbgInfo, FunctionAttribute, InlineAttribute, Lambda, Primitive,
    SetFieldDbgInfo,
};
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::MutableFlag as ParserMutableFlag;
use crate::raw_lambda::matching as full_matching;
use crate::raw_lambda::typeopt::{
    constructor_case, constructor_has_optional_shape, constructor_payload_is_unboxed,
    is_base_type as typeopt_is_base_type, type_cannot_contain_undefined,
    type_cannot_contain_undefined_no_env,
};
use crate::raw_lambda::{RawLambda, RawPrimInfo};
use crate::types::SignatureItem;
use crate::types::asttypes::MutableFlag as TypeMutableFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{LabelDescription, RecordRepresentation, ValueKind};
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typecore::TypeCoreWarning;
use crate::types::typedtree::{
    ApplyArg, Case, Constant as TConstant, Expression, ExpressionDesc, FunctionParam,
    ModuleCoercion, ModuleExpr, ModuleExprDesc, Partial, Pattern, PatternDesc, RecordField,
    RecordLabelDefinition, Structure, StructureItem, StructureItemDesc, ValueBinding,
};

// Keep these aligned with compiler/ml/predef.ml's allocation order. The
// iterable, asyncIterable, and taggedTemplate predefs precede exceptions.
const PREDEF_MATCH_FAILURE_STAMP: i32 = 20;
const PREDEF_ASSERT_FAILURE_STAMP: i32 = 30;

#[derive(Clone)]
struct RecModuleBinding {
    id: Ident,
    loc: Location,
    init: Option<(RawLambda, RawLambda)>,
    rhs: RawLambda,
}

fn predef_exception_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::PREDEF_EXN.with_global())
}

fn recmodule_function_shape_constant() -> Constant {
    Constant::Constructor(crate::types::VariantTag {
        name: "Function".to_string(),
        literal: None,
    })
}

fn raw_constructor_constant(
    ctx: &crate::types::TypeContext,
    cstr: &crate::types::ConstructorDescription,
    tag: i32,
) -> Constant {
    // OCaml compiler/ml/translcore.ml:800-816 emits Pt_shape_none
    // only when Datarepr.constructor_has_optional_shape marks the
    // constructor; an ordinary constructor named `None` stays Pt_constructor.
    if !constructor_has_optional_shape(cstr)
        && let crate::types::ConstructorKind::Ordinary(reference) = cstr.cstr_kind
        && let crate::types::VariantConstructorCase::Constant(tag) = reference.representation(ctx)
    {
        return Constant::Constructor(tag);
    }
    let comment = if constructor_has_optional_shape(cstr) {
        PointerInfo::ShapeNone
    } else {
        let (num_constants, num_blocks) = match cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(reference) => ctx
                .with_variant_layout(reference.variant, |layout| {
                    (layout.num_constants(), layout.num_blocks())
                }),
            crate::types::ConstructorKind::Extension(_) => unreachable!(),
        };
        let runtime_tag = match cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(reference) => {
                match reference.representation(ctx) {
                    crate::types::VariantConstructorCase::Constant(tag) => {
                        constructor_runtime_tag(&tag.literal)
                    }
                    crate::types::VariantConstructorCase::Block(block) => {
                        constructor_runtime_tag(&block.tag().literal)
                    }
                }
            }
            crate::types::ConstructorKind::Extension(_) => unreachable!(),
        };
        PointerInfo::Constructor(PointerConstructorTag {
            name: cstr.cstr_name.clone(),
            const_: num_constants as i32,
            non_const: num_blocks as i32,
            runtime_tag,
        })
    };
    Constant::Int {
        i: tag,
        comment: Some(Box::new(comment)),
    }
}

fn raw_optional_none_constant() -> Constant {
    Constant::Int {
        i: 0,
        comment: Some(Box::new(PointerInfo::ShapeNone)),
    }
}

fn raw_optional_none() -> RawLambda {
    RawLambda::const_(raw_optional_none_constant())
}

fn raw_free_variables(lam: &RawLambda) -> HashSet<Ident> {
    let mut fv = HashSet::new();
    crate::raw_lambda::collect_free_variables(lam, &mut fv);
    fv
}

fn raw_subst_idents_owned(subst: &HashMap<Ident, Ident>, lam: RawLambda) -> RawLambda {
    if subst.is_empty() {
        return lam;
    }

    match lam {
        RawLambda::Lshared(inner) => {
            raw_subst_idents_owned(subst, std::sync::Arc::unwrap_or_clone(inner))
        }
        RawLambda::Lvar(id) => subst
            .get(&id)
            .cloned()
            .map(RawLambda::Lvar)
            .unwrap_or(RawLambda::Lvar(id)),
        RawLambda::LglobalModule(_) | RawLambda::Lconst(_) => lam,
        RawLambda::Lapply(apply) => RawLambda::Lapply(Box::new(crate::raw_lambda::RawApply {
            ap_func: Box::new(raw_subst_idents_owned(subst, *apply.ap_func)),
            ap_args: apply
                .ap_args
                .into_iter()
                .map(|arg| raw_subst_idents_owned(subst, arg))
                .collect(),
            ap_info: apply.ap_info,
            ap_transformed_jsx: apply.ap_transformed_jsx,
        })),
        RawLambda::Lfunction(func) => {
            RawLambda::Lfunction(Box::new(crate::raw_lambda::RawLFunction {
                arity: func.arity,
                params: func.params,
                body: Box::new(raw_subst_idents_owned(subst, *func.body)),
                attr: func.attr,
                loc: func.loc,
            }))
        }
        RawLambda::Llet(kind, id, arg, body) => RawLambda::Llet(
            kind,
            id,
            Box::new(raw_subst_idents_owned(subst, *arg)),
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lletrec(bindings, body) => RawLambda::Lletrec(
            bindings
                .into_iter()
                .map(|(id, expr)| (id, raw_subst_idents_owned(subst, expr)))
                .collect(),
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lprim(info) => RawLambda::Lprim(Box::new(crate::raw_lambda::RawPrimInfo {
            primitive: info.primitive,
            args: info
                .args
                .into_iter()
                .map(|arg| raw_subst_idents_owned(subst, arg))
                .collect(),
            loc: info.loc,
        })),
        RawLambda::Lswitch(arg, sw) => RawLambda::Lswitch(
            Box::new(raw_subst_idents_owned(subst, *arg)),
            Box::new(crate::raw_lambda::RawLambdaSwitch {
                sw_consts_full: sw.sw_consts_full,
                sw_consts: sw
                    .sw_consts
                    .into_iter()
                    .map(|(tag, lam)| (tag, raw_subst_idents_owned(subst, lam)))
                    .collect(),
                sw_blocks_full: sw.sw_blocks_full,
                sw_blocks: sw
                    .sw_blocks
                    .into_iter()
                    .map(|(tag, lam)| (tag, raw_subst_idents_owned(subst, lam)))
                    .collect(),
                sw_failaction: sw
                    .sw_failaction
                    .map(|lam| Box::new(raw_subst_idents_owned(subst, *lam))),
                sw_dispatch: sw.sw_dispatch,
            }),
        ),
        RawLambda::LstringSwitch(arg, cases, default) => RawLambda::LstringSwitch(
            Box::new(raw_subst_idents_owned(subst, *arg)),
            cases
                .into_iter()
                .map(|(name, lam)| (name, raw_subst_idents_owned(subst, lam)))
                .collect(),
            default.map(|lam| Box::new(raw_subst_idents_owned(subst, *lam))),
        ),
        RawLambda::LstaticRaise(i, args) => RawLambda::LstaticRaise(
            i,
            args.into_iter()
                .map(|arg| raw_subst_idents_owned(subst, arg))
                .collect(),
        ),
        RawLambda::LstaticCatch(body, handler, on_raise) => RawLambda::LstaticCatch(
            Box::new(raw_subst_idents_owned(subst, *body)),
            handler,
            Box::new(raw_subst_idents_owned(subst, *on_raise)),
        ),
        RawLambda::LtryWith(body, exn, handler) => RawLambda::LtryWith(
            Box::new(raw_subst_idents_owned(subst, *body)),
            exn,
            Box::new(raw_subst_idents_owned(subst, *handler)),
        ),
        RawLambda::LifThenElse(cond, ifso, ifnot) => RawLambda::LifThenElse(
            Box::new(raw_subst_idents_owned(subst, *cond)),
            Box::new(raw_subst_idents_owned(subst, *ifso)),
            Box::new(raw_subst_idents_owned(subst, *ifnot)),
        ),
        RawLambda::Lsequence(first, second) => RawLambda::Lsequence(
            Box::new(raw_subst_idents_owned(subst, *first)),
            Box::new(raw_subst_idents_owned(subst, *second)),
        ),
        RawLambda::Lwhile(cond, body) => RawLambda::Lwhile(
            Box::new(raw_subst_idents_owned(subst, *cond)),
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lfor(var, lo, hi, dir, body) => RawLambda::Lfor(
            var,
            Box::new(raw_subst_idents_owned(subst, *lo)),
            Box::new(raw_subst_idents_owned(subst, *hi)),
            dir,
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lfor_of(var, iterable, body) => RawLambda::Lfor_of(
            var,
            Box::new(raw_subst_idents_owned(subst, *iterable)),
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lfor_await_of(var, iterable, body) => RawLambda::Lfor_await_of(
            var,
            Box::new(raw_subst_idents_owned(subst, *iterable)),
            Box::new(raw_subst_idents_owned(subst, *body)),
        ),
        RawLambda::Lassign(id, expr) => {
            RawLambda::Lassign(id, Box::new(raw_subst_idents_owned(subst, *expr)))
        }
        RawLambda::Lbreak => RawLambda::Lbreak,
        RawLambda::Lcontinue => RawLambda::Lcontinue,
    }
}

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
        PatternDesc::Tpat_record(fields, _, rest) => {
            if let Some(rest) = rest {
                f(&rest.rest_ident);
            }
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

fn let_bound_idents(bindings: &[ValueBinding]) -> Vec<Ident> {
    let mut ids = Vec::new();
    for binding in bindings {
        iter_bound_pattern_idents(&binding.vb_pat, &mut |id| ids.push(*id));
    }
    ids
}

fn simple_let_binding_id(binding: &ValueBinding) -> Option<Ident> {
    match &binding.vb_pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(*id),
        PatternDesc::Tpat_alias(inner, id, _)
            if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
        {
            Some(*id)
        }
        _ => None,
    }
}

fn nonrecursive_alias_any_binding(binding: &ValueBinding) -> bool {
    matches!(
        &binding.vb_pat.pat_desc,
        PatternDesc::Tpat_alias(inner, _, _) if matches!(inner.pat_desc, PatternDesc::Tpat_any)
    )
}

/// The label's runtime name, decided when its declaration was typed
/// (OCaml `lbl.lbl_runtime_name`).
fn label_runtime_name(lbl: &LabelDescription) -> String {
    lbl.lbl_runtime_name.clone()
}

fn constructor_runtime_tag(
    tag: &Option<crate::types::VariantLiteralTag>,
) -> Option<ConstructorRuntimeTag> {
    tag.as_ref().map(|tag| match tag {
        crate::types::VariantLiteralTag::Int(value) => {
            ConstructorRuntimeTag::Int(i64::from(*value as i32))
        }
        crate::types::VariantLiteralTag::String(value) => {
            ConstructorRuntimeTag::String(value.clone())
        }
        crate::types::VariantLiteralTag::Float(value) => {
            ConstructorRuntimeTag::Float(value.clone())
        }
        crate::types::VariantLiteralTag::BigInt(value) => {
            ConstructorRuntimeTag::BigInt(value.clone())
        }
        crate::types::VariantLiteralTag::Bool(value) => ConstructorRuntimeTag::Bool(*value),
        crate::types::VariantLiteralTag::Null => ConstructorRuntimeTag::Null,
        crate::types::VariantLiteralTag::Undefined => ConstructorRuntimeTag::Undefined,
    })
}

fn config_payload_flags_contains(
    payload: &crate::parser::ast::Payload,
    value: &str,
    arena: &ParseArena,
) -> bool {
    use crate::parser::ast::{Constant as PConstant, ExpressionDesc as PExpressionDesc};
    use crate::parser::longident::Longident;

    let crate::parser::ast::Payload::PStr(items) = payload else {
        return false;
    };

    items.iter().any(|item| {
        let crate::parser::ast::StructureItemDesc::Pstr_eval(inner) = &item.pstr_desc else {
            return false;
        };
        let (expr_idx, _) = &**inner;
        let expr = arena.get_expr(*expr_idx);
        let PExpressionDesc::Pexp_record(record) = &expr.pexp_desc else {
            return false;
        };
        let (fields, _) = &*record;
        arena.expr_field_list(*fields).iter().any(|field| {
            let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                return false;
            };
            if arena.get_string(*name_idx) != "flags" {
                return false;
            }
            let field_expr = arena.get_expr(field.expr);
            let PExpressionDesc::Pexp_array(elements) = &field_expr.pexp_desc else {
                return false;
            };
            arena.expr_list(*elements).iter().any(|elem_idx| {
                let elem = arena.get_expr(*elem_idx);
                matches!(
                    &elem.pexp_desc,
                    PExpressionDesc::Pexp_constant(c)
                        if matches!(&*c, PConstant::String(s) if s.semantic(arena) == value)
                )
            })
        })
    })
}

fn structure_has_config_string(structure: &Structure, value: &str, arena: &ParseArena) -> bool {
    structure.str_items.iter().any(|item| {
        let StructureItemDesc::Tstr_attribute(attr) = &item.str_desc else {
            return false;
        };
        arena.get_string(attr.0.txt) == "config"
            && config_payload_flags_contains(&attr.1, value, arena)
    })
}

fn raw_polyvariant_const(tag: &str) -> RawLambda {
    RawLambda::const_(Constant::Int {
        i: crate::types::btype::hash_variant(tag),
        comment: Some(Box::new(PointerInfo::PolyVariant(tag.to_string()))),
    })
}

fn raw_record_field_access(lbl: &LabelDescription) -> Option<(i32, FieldDbgInfo)> {
    let name = label_runtime_name(lbl);
    let info = match &lbl.lbl_repres {
        RecordRepresentation::RecordRegular => FieldDbgInfo::Record { name },
        RecordRepresentation::RecordFloatUnused => return None,
        RecordRepresentation::RecordUnboxed(_) => FieldDbgInfo::Record { name },
        RecordRepresentation::RecordInlined { .. } => FieldDbgInfo::RecordInline { name },
        RecordRepresentation::RecordExtension => FieldDbgInfo::RecordExtension { name },
    };
    let pos = match lbl.lbl_repres {
        RecordRepresentation::RecordExtension => lbl.lbl_pos + 1,
        _ => lbl.lbl_pos,
    };
    Some((pos, info))
}

fn raw_record_setfield_access(lbl: &LabelDescription) -> Option<(i32, SetFieldDbgInfo)> {
    let name = label_runtime_name(lbl);
    let info = match &lbl.lbl_repres {
        RecordRepresentation::RecordRegular => SetFieldDbgInfo::RecordSet(name),
        RecordRepresentation::RecordFloatUnused | RecordRepresentation::RecordUnboxed(_) => {
            return None;
        }
        RecordRepresentation::RecordInlined { .. } => SetFieldDbgInfo::RecordInlineSet(name),
        RecordRepresentation::RecordExtension => SetFieldDbgInfo::RecordExtensionSet(name),
    };
    let pos = match lbl.lbl_repres {
        RecordRepresentation::RecordExtension => lbl.lbl_pos + 1,
        _ => lbl.lbl_pos,
    };
    Some((pos, info))
}

fn raw_record_mutable_flag(
    fields: &[(
        Located<LidentIdx>,
        LabelDescription,
        RecordLabelDefinition,
        bool,
    )],
) -> ParserMutableFlag {
    fields
        .iter()
        .find(|(_, lbl, _, _)| lbl.lbl_mut == TypeMutableFlag::Mutable)
        .map(|_| ParserMutableFlag::Mutable)
        .unwrap_or(ParserMutableFlag::Immutable)
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

fn inlined_record_representation(
    cstr: &crate::types::ConstructorDescription,
) -> Option<RecordRepresentation> {
    let inlined = cstr.cstr_inlined.as_ref()?;
    match &inlined.type_kind {
        crate::types::decl::TypeKind::TypeRecord(_, repr) => Some(repr.clone()),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum RawLocKind {
    File,
    Line,
    Module,
    Loc,
    Pos,
}

#[derive(Clone)]
struct ComparisonSpecialization {
    objcomp: Primitive,
    intcomp: Primitive,
    boolcomp: Primitive,
    floatcomp: Primitive,
    stringcomp: Primitive,
    bigintcomp: Primitive,
    simplify_constant_constructor: bool,
}

/// A source position the converter reads: an arena location index, or a
/// declaration `Location` carried by the type system
/// (`PrimitiveCoercion.pc_loc`). Node handles and coordinate reads both go
/// through the converter so the two stay separate.
#[derive(Debug, Clone, Copy)]
enum SrcLoc {
    Arena(LocIdx),
    Decl(Location),
}

impl From<LocIdx> for SrcLoc {
    fn from(idx: LocIdx) -> Self {
        SrcLoc::Arena(idx)
    }
}

impl From<Location> for SrcLoc {
    fn from(loc: Location) -> Self {
        SrcLoc::Decl(loc)
    }
}

#[derive(Debug, Clone)]
pub struct RawLambdaDiagnostic {
    pub loc: Location,
    pub message: String,
}

pub(crate) struct IndexedRawLambda {
    raw: RawLambda,
    id_gen: std::sync::Arc<IdGenerator>,
}

impl IndexedRawLambda {
    pub(crate) fn into_parts(self) -> (RawLambda, std::sync::Arc<IdGenerator>) {
        (self.raw, self.id_gen)
    }
}

enum RawLambdaIdGenerator {
    Owned(IdGenerator),
    Shared(std::sync::Arc<IdGenerator>),
}

impl std::ops::Deref for RawLambdaIdGenerator {
    type Target = IdGenerator;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(generator) => generator,
            Self::Shared(generator) => generator,
        }
    }
}

/// Converter from typedtree to raw lambda.
pub struct RawLambdaConverter<'a> {
    arena: &'a ParseArena,
    type_ctx: &'a TypeContext,
    env: &'a crate::types::env::Env,
    persistent_env: Option<crate::cmi::persistent_env::PersistentEnv>,
    possible_required_modules: ahash::AHashSet<ModuleId>,
    id_gen: RawLambdaIdGenerator,
    next_static_raise: i32,
    next_negative_raise: i32,
    unit_name: String,
    no_assert_false: bool,
    noassert: bool,
    diagnostic: Option<RawLambdaDiagnostic>,
    warnings: Vec<TypeCoreWarning>,
    warning_config: WarningConfig,
    suppress_inlined_attribute_check: usize,
    preserve_expanded_sparse_records: bool,
    hoisted_functions: Vec<crate::lambda::HoistedFunction>,
    hoisted_exports: Vec<crate::lambda::HoistedExport>,
    /// Location handles attached to the nodes this conversion builds.
    lam_locs: crate::raw_lambda::loc::LamLocBuilder,
}

impl<'a> RawLambdaConverter<'a> {
    /// Create a new raw-lambda converter.
    pub fn new(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext,
        env: &'a crate::types::env::Env,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            possible_required_modules: ahash::AHashSet::new(),
            id_gen: RawLambdaIdGenerator::Owned(IdGenerator::new()),
            next_static_raise: 0,
            next_negative_raise: 0,
            unit_name: String::new(),
            no_assert_false: false,
            noassert: false,
            diagnostic: None,
            warnings: Vec::new(),
            warning_config: WarningConfig::new(),
            suppress_inlined_attribute_check: 0,
            preserve_expanded_sparse_records: false,
            hoisted_functions: Vec::new(),
            hoisted_exports: Vec::new(),
            lam_locs: crate::raw_lambda::loc::LamLocBuilder::new(arena),
        }
    }

    /// Create a new raw-lambda converter with stamps continuing from an existing phase.
    pub fn with_start_stamp(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext,
        env: &'a crate::types::env::Env,
        start_stamp: i32,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            possible_required_modules: ahash::AHashSet::new(),
            id_gen: RawLambdaIdGenerator::Owned(IdGenerator::with_start_stamp(start_stamp)),
            next_static_raise: 0,
            next_negative_raise: 0,
            unit_name: String::new(),
            no_assert_false: false,
            noassert: false,
            diagnostic: None,
            warnings: Vec::new(),
            warning_config: WarningConfig::new(),
            suppress_inlined_attribute_check: 0,
            preserve_expanded_sparse_records: false,
            hoisted_functions: Vec::new(),
            hoisted_exports: Vec::new(),
            lam_locs: crate::raw_lambda::loc::LamLocBuilder::new(arena),
        }
    }

    /// Create a new raw-lambda converter with the current compilation unit name.
    pub fn with_start_stamp_and_unit_name(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext,
        env: &'a crate::types::env::Env,
        start_stamp: i32,
        unit_name: String,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            possible_required_modules: ahash::AHashSet::new(),
            id_gen: RawLambdaIdGenerator::Owned(IdGenerator::with_start_stamp(start_stamp)),
            next_static_raise: 0,
            next_negative_raise: 0,
            unit_name,
            no_assert_false: false,
            noassert: false,
            diagnostic: None,
            warnings: Vec::new(),
            warning_config: WarningConfig::new(),
            suppress_inlined_attribute_check: 0,
            preserve_expanded_sparse_records: false,
            hoisted_functions: Vec::new(),
            hoisted_exports: Vec::new(),
            lam_locs: crate::raw_lambda::loc::LamLocBuilder::new(arena),
        }
    }

    /// Create the inactive indexed producer with the compilation-wide
    /// identifier stream. Legacy constructors above retain stack-owned generators.
    pub(crate) fn with_id_generator_and_unit_name(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext,
        env: &'a crate::types::env::Env,
        id_gen: std::sync::Arc<IdGenerator>,
        unit_name: String,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            possible_required_modules: ahash::AHashSet::new(),
            id_gen: RawLambdaIdGenerator::Shared(id_gen),
            next_static_raise: 0,
            next_negative_raise: 0,
            unit_name,
            no_assert_false: false,
            noassert: false,
            diagnostic: None,
            warnings: Vec::new(),
            warning_config: WarningConfig::new(),
            suppress_inlined_attribute_check: 0,
            preserve_expanded_sparse_records: false,
            hoisted_functions: Vec::new(),
            hoisted_exports: Vec::new(),
            lam_locs: crate::raw_lambda::loc::LamLocBuilder::new(arena),
        }
    }

    pub(crate) fn finish_indexed_raw(self, raw: RawLambda) -> IndexedRawLambda {
        let RawLambdaIdGenerator::Shared(id_gen) = self.id_gen else {
            panic!("indexed Raw Lambda requires the shared-generator converter")
        };
        IndexedRawLambda { raw, id_gen }
    }

    #[cfg(test)]
    fn shares_id_generator(&self, generator: &std::sync::Arc<IdGenerator>) -> bool {
        matches!(&self.id_gen, RawLambdaIdGenerator::Shared(owned) if std::sync::Arc::ptr_eq(owned, generator))
    }

    pub fn set_persistent_env(
        &mut self,
        persistent_env: crate::cmi::persistent_env::PersistentEnv,
    ) {
        self.persistent_env = Some(persistent_env);
    }

    pub fn set_no_assert_false(&mut self, no_assert_false: bool) {
        self.no_assert_false = no_assert_false;
    }

    pub fn set_noassert(&mut self, noassert: bool) {
        self.noassert = noassert;
    }

    pub fn set_preserve_expanded_sparse_records(&mut self, preserve: bool) {
        self.preserve_expanded_sparse_records = preserve;
    }

    pub fn set_warning_config(&mut self, warning_config: WarningConfig) {
        self.warning_config = warning_config;
    }

    pub fn current_stamp(&self) -> i32 {
        self.id_gen.current_stamp()
    }

    pub fn take_possible_required_modules(&mut self) -> ahash::AHashSet<ModuleId> {
        std::mem::take(&mut self.possible_required_modules)
    }

    pub fn take_diagnostic(&mut self) -> Option<RawLambdaDiagnostic> {
        self.diagnostic.take()
    }

    pub fn take_warnings(&mut self) -> Vec<TypeCoreWarning> {
        std::mem::take(&mut self.warnings)
    }

    pub fn take_hoisted_functions(&mut self) -> Vec<crate::lambda::HoistedFunction> {
        std::mem::take(&mut self.hoisted_functions)
    }

    pub fn take_hoisted_exports(&mut self) -> Vec<crate::lambda::HoistedExport> {
        std::mem::take(&mut self.hoisted_exports)
    }

    fn report_unknown_builtin_primitive(&mut self, loc: SrcLoc, prim_name: &str) {
        if prim_name.starts_with('%') {
            self.report_diagnostic(
                self.loc(loc),
                format!("Unknown builtin primitive \"{prim_name}\""),
            );
        }
    }

    fn report_diagnostic(&mut self, loc: Location, message: String) {
        if self.diagnostic.is_none() {
            self.diagnostic = Some(RawLambdaDiagnostic { loc, message });
        }
    }

    fn report_warning(&mut self, loc: LocIdx, warning: Warning) {
        if !self.warning_config.is_active(&warning) {
            return;
        }
        let is_error = self.warning_config.is_error(&warning);
        self.warnings.push(TypeCoreWarning {
            loc,
            warning,
            is_error,
        });
    }

    fn sync_local_stamp_generators(&mut self) {
        let shared_stamp = self.current_stamp().max(self.type_ctx.current_stamp());
        self.type_ctx.set_current_time(shared_stamp);
        self.id_gen.set_current_stamp(shared_stamp);
    }

    /// `Translcore.pack_trywith_exn` (translcore.ml:956-959): when the
    /// handler takes the caught value apart, catch it as `raw_<id>` and bind
    /// `id` to it converted with `Primitive_exceptions.internalToException`.
    /// Called where OCaml calls it, so `raw_<id>` takes the next stamp.
    fn pack_trywith_exn(&mut self, id: Ident, handler: RawLambda) -> (Ident, RawLambda) {
        if !crate::raw_lambda::lower::exception_id_destructed_raw(&handler, &id) {
            return (id, handler);
        }
        let raw_id = self.fresh_ident(&format!("raw_{}", id.name()));
        let wrapped = RawLambda::let_(
            crate::lambda::lam_compat::LetKind::StrictOpt,
            id,
            crate::raw_lambda::lower::wrap_exn_raw(LamLoc::NONE, RawLambda::var(raw_id.clone())),
            handler,
        );
        (raw_id, wrapped)
    }

    fn fresh_ident(&mut self, name: &str) -> Ident {
        // OCaml uses one global `Ident.currentstamp` for both Translcore and
        // Translmod (`compiler/ml/translcore.ml:1250-1271`,
        // `compiler/ml/translmod.ml:422-448`), so synchronize before and after
        // minting a raw identifier to preserve OCaml's physical stamp ordering.
        self.sync_local_stamp_generators();
        let id = self.id_gen.create(name);
        let stamp = id.stamp();
        self.type_ctx.set_current_time(stamp);
        id
    }

    fn rename_ident(&mut self, id: &Ident) -> Ident {
        // `Typecore.id_of_pattern` and functor translation call `Ident.rename`
        // on the same global counter as `Ident.create` (compiler/ml/typecore.ml:
        // 2268-2283, compiler/ml/translmod.ml:250-256). Component forcing can
        // allocate through the type context immediately afterward, so publish
        // the renamed stamp at the same boundary as `fresh_ident`.
        self.sync_local_stamp_generators();
        let renamed = id.rename(&self.id_gen);
        self.type_ctx.set_current_time(renamed.stamp());
        renamed
    }

    fn note_possible_required_module(&mut self, id: &Ident) {
        self.possible_required_modules.insert(ModuleId {
            id: *id,
            kind: Kind::Ml,
            dynamic_import: false,
        });
    }

    fn note_possible_required_modules_in_raw_lambda(&mut self, lam: &RawLambda) {
        match lam {
            RawLambda::Lshared(inner) => self.note_possible_required_modules_in_raw_lambda(inner),
            RawLambda::Lvar(_) | RawLambda::Lconst(_) => {}
            RawLambda::LglobalModule(id) => {
                self.note_possible_required_module(id);
            }
            RawLambda::Lapply(apply) => {
                self.note_possible_required_modules_in_raw_lambda(&apply.ap_func);
                for arg in &apply.ap_args {
                    self.note_possible_required_modules_in_raw_lambda(arg);
                }
            }
            RawLambda::Lfunction(func) => {
                self.note_possible_required_modules_in_raw_lambda(&func.body);
            }
            RawLambda::Llet(_, _, value, body) => {
                self.note_possible_required_modules_in_raw_lambda(value);
                self.note_possible_required_modules_in_raw_lambda(body);
            }
            RawLambda::Lletrec(bindings, body) => {
                for (_, value) in bindings {
                    self.note_possible_required_modules_in_raw_lambda(value);
                }
                self.note_possible_required_modules_in_raw_lambda(body);
            }
            RawLambda::Lprim(info) => {
                for arg in &info.args {
                    self.note_possible_required_modules_in_raw_lambda(arg);
                }
            }
            RawLambda::Lswitch(scrutinee, switch) => {
                self.note_possible_required_modules_in_raw_lambda(scrutinee);
                for (_, branch) in &switch.sw_consts {
                    self.note_possible_required_modules_in_raw_lambda(branch);
                }
                for (_, branch) in &switch.sw_blocks {
                    self.note_possible_required_modules_in_raw_lambda(branch);
                }
                if let Some(failaction) = &switch.sw_failaction {
                    self.note_possible_required_modules_in_raw_lambda(failaction);
                }
            }
            RawLambda::LstringSwitch(scrutinee, cases, default) => {
                self.note_possible_required_modules_in_raw_lambda(scrutinee);
                for (_, branch) in cases {
                    self.note_possible_required_modules_in_raw_lambda(branch);
                }
                if let Some(default) = default {
                    self.note_possible_required_modules_in_raw_lambda(default);
                }
            }
            RawLambda::LstaticRaise(_, args) => {
                for arg in args {
                    self.note_possible_required_modules_in_raw_lambda(arg);
                }
            }
            RawLambda::LstaticCatch(body, _, handler) | RawLambda::LtryWith(body, _, handler) => {
                self.note_possible_required_modules_in_raw_lambda(body);
                self.note_possible_required_modules_in_raw_lambda(handler);
            }
            RawLambda::LifThenElse(cond, then_, else_) => {
                self.note_possible_required_modules_in_raw_lambda(cond);
                self.note_possible_required_modules_in_raw_lambda(then_);
                self.note_possible_required_modules_in_raw_lambda(else_);
            }
            RawLambda::Lsequence(first, second) => {
                self.note_possible_required_modules_in_raw_lambda(first);
                self.note_possible_required_modules_in_raw_lambda(second);
            }
            RawLambda::Lwhile(cond, body) => {
                self.note_possible_required_modules_in_raw_lambda(cond);
                self.note_possible_required_modules_in_raw_lambda(body);
            }
            RawLambda::Lfor(_, start, finish, _, body) => {
                self.note_possible_required_modules_in_raw_lambda(start);
                self.note_possible_required_modules_in_raw_lambda(finish);
                self.note_possible_required_modules_in_raw_lambda(body);
            }
            RawLambda::Lfor_of(_, iterable, body) | RawLambda::Lfor_await_of(_, iterable, body) => {
                self.note_possible_required_modules_in_raw_lambda(iterable);
                self.note_possible_required_modules_in_raw_lambda(body);
            }
            RawLambda::Lassign(_, value) => {
                self.note_possible_required_modules_in_raw_lambda(value);
            }
            RawLambda::Lbreak | RawLambda::Lcontinue => {}
        }
    }

    fn sync_matching_stamps(&mut self) {
        self.sync_local_stamp_generators();
    }

    fn compile_matching_with_synced_stamps(
        &mut self,
        handler_fun: impl FnOnce() -> RawLambda,
        arg: RawLambda,
        pat_act_list: Vec<(&Pattern, full_matching::CaseAction)>,
        partial: Partial,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::compile_matching(
            self.type_ctx,
            &crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs),
            handler_fun,
            arg,
            pat_act_list,
            partial,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    fn for_let_with_synced_stamps(
        &mut self,
        loc: LocIdx,
        param: RawLambda,
        pat: &Pattern,
        body: RawLambda,
    ) -> RawLambda {
        // Native Translcore calls Matching.for_let while both modules allocate
        // from the same Ident.currentstamp (compiler/ml/translcore.ml:1071;
        // compiler/ext/ident.ml:26-58). Publish Matching's TypeContext-backed
        // allocations back to the raw converter at the same boundary as the
        // other Matching entry points below.
        self.sync_matching_stamps();
        let lambda = full_matching::for_let(
            self.type_ctx,
            &crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs),
            self.loc(loc),
            param,
            pat,
            body,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    fn for_function_with_synced_stamps(
        &mut self,
        loc: LocIdx,
        param: RawLambda,
        pat_act_list: Vec<(&Pattern, full_matching::CaseAction)>,
        partial: Partial,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::for_function(
            self.type_ctx,
            &crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs),
            self.loc(loc),
            param,
            pat_act_list,
            partial,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    fn for_trywith_with_synced_stamps(
        &mut self,
        param: RawLambda,
        pat_act_list: Vec<(&Pattern, full_matching::CaseAction)>,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::for_trywith(
            self.type_ctx,
            &crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs),
            param,
            pat_act_list,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    fn for_multiple_match_with_synced_stamps(
        &mut self,
        loc: LocIdx,
        paraml: Vec<RawLambda>,
        pat_act_list: Vec<(&Pattern, full_matching::CaseAction)>,
        partial: Partial,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::for_multiple_match(
            self.type_ctx,
            &crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs),
            self.loc(loc),
            paraml,
            pat_act_list,
            partial,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    /// Semantic read of source coordinates (location-valued constants,
    /// diagnostics). Node metadata uses [`Self::lam_loc`] instead.
    #[inline]
    fn loc(&self, loc: impl Into<SrcLoc>) -> Location {
        match loc.into() {
            SrcLoc::Arena(idx) => self.arena.to_location(idx),
            SrcLoc::Decl(loc) => loc,
        }
    }

    /// The node handle of a source location.
    #[inline]
    fn lam_loc(&self, loc: impl Into<SrcLoc>) -> LamLoc {
        match loc.into() {
            SrcLoc::Arena(idx) => self.lam_locs.from_idx(self.arena, idx),
            SrcLoc::Decl(loc) => self.lam_locs.intern(loc),
        }
    }

    /// Whether a location is compiler-generated.
    fn is_ghost_loc(&self, loc: SrcLoc) -> bool {
        match loc {
            SrcLoc::Arena(idx) => self.arena.get_location(idx).loc_ghost,
            SrcLoc::Decl(loc) => loc.loc_ghost,
        }
    }

    /// The node handle of a hoisted-function location, resolved back to its
    /// arena index for warnings (`LocIdx::none` without coordinates).
    fn loc_idx_for_lam_loc(&self, loc: LamLoc) -> LocIdx {
        match self.lam_locs.get(loc) {
            Some(loc) => self.loc_idx_for_location(&loc),
            None => self.arena.none_loc(),
        }
    }

    fn loc_arena(&self) -> crate::raw_lambda::loc::LocArena<'_> {
        crate::raw_lambda::loc::LocArena::new(self.arena, &self.lam_locs)
    }

    /// The table resolving every location handle in the converted Lambda
    /// (and the hoisted functions). Location-free arenas give an opaque
    /// table without coordinate rows.
    pub fn take_lam_locs(&self) -> crate::lambda::LamLocTable {
        self.lam_locs.take_table(self.arena)
    }

    fn next_raise_count(&mut self) -> i32 {
        self.next_static_raise += 1;
        self.next_static_raise
    }

    /// Get a negative static exception ID for exception-carrying static catches.
    /// Matches OCaml's next_negative_raise_count.
    fn next_negative_raise_count(&mut self) -> i32 {
        self.next_negative_raise -= 1;
        self.next_negative_raise
    }

    /// Convert typed tree cases to `(Pattern, action)` pairs for the full
    /// matching compiler. A guard stays data until matching knows its
    /// fallthrough (`compiler/ml/translcore.ml` `Matching.guarded`).
    fn cases_to_pat_act_list<'c>(
        &mut self,
        cases: &'c [Case],
    ) -> Vec<(&'c Pattern, full_matching::CaseAction)> {
        cases
            .iter()
            .map(|case| {
                let body = self.convert_expr_raw(&case.c_rhs);
                let act = match &case.c_guard {
                    Some(guard) => {
                        full_matching::CaseAction::guarded(self.convert_expr_raw(guard), body)
                    }
                    None => full_matching::CaseAction::unguarded(body),
                };
                (&case.c_lhs, act)
            })
            .collect()
    }

    fn id_of_pattern(&mut self, pat: &Pattern) -> Option<Ident> {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => Some(*id),
            PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => match &args[0].pat_desc {
                PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                    Some(self.rename_ident(id))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn name_pattern_ident(&mut self, default: &str, cases: &[Case]) -> Ident {
        cases
            .iter()
            .find_map(|case| self.id_of_pattern(&case.c_lhs))
            .unwrap_or_else(|| self.fresh_ident(default))
    }

    /// Look up all label declarations for a record type.
    /// OCaml's make_record_matching uses lbl_all to iterate over ALL fields.
    /// Since Rust's lbl_all is a placeholder, we resolve via the type context cache.
    fn resolve_all_record_labels(
        &self,
        record_ty: TypeExprRef,
    ) -> Option<
        Vec<(
            String,
            i32,
            TypeMutableFlag,
            RecordRepresentation,
            Vec<crate::types::decl::Attribute>,
        )>,
    > {
        let ty = self.type_ctx.repr(record_ty);
        let desc = self.type_ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, .. } => {
                if path.same(&crate::types::predef::path_dict()) {
                    let labels = self.type_ctx.get_dict_pattern_labels();
                    if !labels.is_empty() {
                        return Some(labels);
                    }
                }
                // Try the record labels cache (populated during type checking),
                // keyed by the exact type path (including stamps)
                if let Some(labels) = self.type_ctx.get_record_labels(path) {
                    return Some(labels);
                }
                // Try env lookup
                if let Ok(decl) = self.env.lookup_type(path) {
                    if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind
                    {
                        return Some(
                            labels
                                .iter()
                                .enumerate()
                                .map(|(pos, ld)| {
                                    let name = ld.declaration_name();
                                    (
                                        name,
                                        pos as i32,
                                        ld.ld_mutable,
                                        repr.clone(),
                                        ld.ld_attributes.clone(),
                                    )
                                })
                                .collect(),
                        );
                    }
                }
                // Try type_ctx stores
                if let Some(decl) = self.type_ctx.find_type_decl_by_path(&path.name()) {
                    if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind
                    {
                        return Some(
                            labels
                                .iter()
                                .enumerate()
                                .map(|(pos, ld)| {
                                    let name = ld.declaration_name();
                                    (
                                        name,
                                        pos as i32,
                                        ld.ld_mutable,
                                        repr.clone(),
                                        ld.ld_attributes.clone(),
                                    )
                                })
                                .collect(),
                        );
                    }
                }
                if let Some(decl) = self.type_ctx.find_type_decl(path.last()) {
                    if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind
                    {
                        return Some(
                            labels
                                .iter()
                                .enumerate()
                                .map(|(pos, ld)| {
                                    let name = ld.declaration_name();
                                    (
                                        name,
                                        pos as i32,
                                        ld.ld_mutable,
                                        repr.clone(),
                                        ld.ld_attributes.clone(),
                                    )
                                })
                                .collect(),
                        );
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn global_path(&self) -> Option<crate::types::Path> {
        if self.unit_name.is_empty() {
            None
        } else {
            Some(crate::types::Path::pident(Ident::create_persistent(
                self.unit_name.clone(),
            )))
        }
    }

    fn register_module_type_paths(
        &self,
        module_path: &crate::types::Path,
        module_type: &crate::types::decl::ModuleType,
        visited_module_paths: &mut HashSet<String>,
    ) {
        match module_type {
            crate::types::decl::ModuleType::MtySignature(sig) => {
                self.register_signature_type_paths_inner(
                    Some(module_path),
                    sig,
                    visited_module_paths,
                );
            }
            crate::types::decl::ModuleType::MtyFunctor { result, .. } => {
                self.register_module_type_paths(module_path, result, visited_module_paths);
            }
            crate::types::decl::ModuleType::MtyIdent(_)
            | crate::types::decl::ModuleType::MtyAlias(_, _) => {}
        }
    }

    fn register_signature_type_paths(
        &self,
        prefix: Option<&crate::types::Path>,
        sig: &[SignatureItem],
    ) {
        let mut visited_module_paths = HashSet::new();
        self.register_signature_type_paths_inner(prefix, sig, &mut visited_module_paths);
    }

    fn should_register_nested_module_type_paths(&self, module_path: &crate::types::Path) -> bool {
        let Ok((head, _)) = module_path.flatten() else {
            // OCaml `Path.head` asserts on functor applications and callers use
            // `Path.flatten` when they need a safe dotted-path test
            // (compiler/ml/path.ml:58-69). Registration is only a side-table
            // seed for current/local modules, so functor applications stay out.
            return false;
        };
        !head.is_persistent() && !head.is_global() || head.name() == self.unit_name
    }

    fn register_signature_type_paths_inner(
        &self,
        prefix: Option<&crate::types::Path>,
        sig: &[SignatureItem],
        visited_module_paths: &mut HashSet<String>,
    ) {
        for item in sig {
            match item {
                SignatureItem::SigType(id, decl, _) => {
                    if id.stamp() != 0 {
                        self.type_ctx
                            .register_type_decl_by_stamp(id.stamp(), decl.clone());
                    }
                    if let Some(prefix) = prefix {
                        let path = crate::types::Path::pdot(prefix.clone(), id.name());
                        self.type_ctx
                            .register_type_decl_by_path(&path.name(), decl.clone());
                        self.type_ctx
                            .register_type_decl_by_exact_path(path, decl.clone());
                    }
                }
                SignatureItem::SigModule(id, md, _) => {
                    let module_path = md.md_path.clone().unwrap_or_else(|| {
                        prefix.map_or_else(
                            || crate::types::Path::pident(*id),
                            |prefix| crate::types::Path::pdot(prefix.clone(), id.name()),
                        )
                    });
                    // OCaml raw translation walks the current structure and
                    // coercion (compiler/ml/translmod.ml:290-451), not the full
                    // signatures of already-compiled dependency modules. Keep
                    // this Rust side-table seeding to local/current-module
                    // paths so dependency cycles stay in PersistentEnv lookups.
                    if self.should_register_nested_module_type_paths(&module_path)
                        && visited_module_paths.insert(module_path.name())
                    {
                        self.register_module_type_paths(
                            &module_path,
                            &md.md_type,
                            visited_module_paths,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    fn field_path(
        rootpath: &Option<crate::types::Path>,
        field: &Ident,
    ) -> Option<crate::types::Path> {
        rootpath
            .as_ref()
            .map(|path| crate::types::Path::pdot(path.clone(), field.name().to_string()))
    }

    fn loc_idx_for_location(&self, loc: &Location) -> LocIdx {
        (0..self.arena.location_count())
            .map(|index| LocIdx(index as u32))
            .find(|index| self.arena.to_location(*index) == *loc)
            .unwrap_or_else(|| self.arena.none_loc())
    }

    /// Mirrors `Translcore.mark_js_hoisted_pattern` and
    /// `Translmod.js_hoist_handler` from upstream 8bf91cb18.
    fn mark_js_hoisted_pattern(
        &mut self,
        rootpath: &Option<crate::types::Path>,
        attrs: &crate::parser::ast::Attributes,
        pat: &Pattern,
        lam: &RawLambda,
        target_loc: LocIdx,
    ) {
        // `Translattribute.find_attribute` (translattribute.ml:28-38): a
        // repeated attribute reports warning 54 at the second one and counts
        // as absent.
        let mut matching = attrs
            .iter()
            .filter(|(name, _)| self.arena.get_string(name.txt) == "res.hoistedFunction");
        let Some((attr_name, payload)) = matching.next() else {
            return;
        };
        if let Some((second, _)) = matching.next() {
            self.report_warning(
                second.loc,
                Warning::DuplicatedAttribute {
                    name: "res.hoistedFunction".to_string(),
                },
            );
            return;
        }
        let warning_loc = attr_name.loc;
        if !matches!(payload, crate::parser::ast::Payload::PStr(items) if items.is_empty()) {
            self.report_warning(
                warning_loc,
                Warning::AttributePayload {
                    attr: "res.hoistedFunction".to_string(),
                    message: "This attribute does not accept a payload".to_string(),
                },
            );
            return;
        }
        let binding = match (&pat.pat_desc, lam) {
            (PatternDesc::Tpat_var(id, _), RawLambda::Lfunction(_)) => *id,
            (PatternDesc::Tpat_alias(inner, id, _), RawLambda::Lfunction(_))
                if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
            {
                *id
            }
            _ => {
                self.report_warning(
                    warning_loc,
                    Warning::MisplacedAttribute {
                        name: "res.hoistedFunction".to_string(),
                    },
                );
                return;
            }
        };
        let Some(path) = rootpath.as_ref() else {
            self.report_warning(
                warning_loc,
                Warning::MisplacedAttribute {
                    name: "res.hoistedFunction".to_string(),
                },
            );
            return;
        };
        let Ok((_head, segments)) = path.flatten() else {
            self.report_warning(
                warning_loc,
                Warning::MisplacedAttribute {
                    name: "res.hoistedFunction".to_string(),
                },
            );
            return;
        };
        if segments.is_empty() {
            self.report_warning(
                warning_loc,
                Warning::MisplacedAttribute {
                    name: "res.hoistedFunction".to_string(),
                },
            );
            return;
        }
        let mut segments = segments.into_iter().map(str::to_string).collect::<Vec<_>>();
        segments.push(binding.name().to_string());
        // Structure translation visits the continuation first. Prepending keeps
        // the same source order as OCaml's `js_hoisted := item :: !js_hoisted`.
        self.hoisted_functions.insert(
            0,
            crate::lambda::HoistedFunction {
                binding,
                path: segments,
                loc: self.lam_loc(attr_name.loc),
                target_loc: self.lam_loc(target_loc),
            },
        );
    }

    /// Find an inline-style attribute, matching OCaml's
    /// `Translattribute.find_attribute`: duplicates warn at the second
    /// attribute and make the attribute unavailable to the caller.
    fn find_inline_attribute_index(
        &mut self,
        attrs: &crate::parser::ast::Attributes,
        attr_name: &str,
    ) -> Option<usize> {
        let mut first = None;
        for (idx, (located_name, _)) in attrs.iter().enumerate() {
            let name = self.arena.get_string(located_name.txt);
            if name != attr_name {
                continue;
            }
            if first.is_some() {
                self.report_warning(
                    located_name.loc,
                    Warning::DuplicatedAttribute {
                        name: name.to_string(),
                    },
                );
                return None;
            }
            first = Some(idx);
        }
        first
    }

    fn parse_inline_attribute(
        &mut self,
        attr: Option<&crate::parser::ast::Attribute>,
    ) -> InlineAttribute {
        use crate::parser::ast::{ExpressionDesc, Payload, StructureItemDesc};
        use crate::parser::longident::Longident;

        let Some((located_name, payload)) = attr else {
            return InlineAttribute::Default;
        };

        let warn = |this: &mut Self| {
            this.report_warning(
                located_name.loc,
                Warning::AttributePayload {
                    attr: this.arena.get_string(located_name.txt).to_string(),
                    message: "It must be either empty, 'always' or 'never'".to_string(),
                },
            );
        };

        match payload {
            Payload::PStr(items) if items.is_empty() => InlineAttribute::Always,
            Payload::PStr(items) if items.len() == 1 => {
                if let StructureItemDesc::Pstr_eval(eval_inner) = &items[0].pstr_desc {
                    let (expr_idx, attrs) = &**eval_inner;
                    // translattribute.ml: `Ast_payload.unwrap_braces expression`.
                    let expr = crate::ast_payload::unwrap_braces(
                        self.arena,
                        self.arena.get_expr(*expr_idx),
                    );
                    if attrs.is_empty()
                        && let ExpressionDesc::Pexp_ident(ident) = &expr.pexp_desc
                    {
                        let lid = self.arena.get_longident(ident.txt);
                        if let Longident::Lident(str_idx) = lid {
                            let name = self.arena.get_string(*str_idx);
                            if name == "always" {
                                return InlineAttribute::Always;
                            } else if name == "never" {
                                return InlineAttribute::Never;
                            }
                        }
                    }
                }
                warn(self);
                InlineAttribute::Default
            }
            _ => {
                warn(self);
                InlineAttribute::Default
            }
        }
    }

    /// Extract inline attribute from module/value attributes, matching OCaml's
    /// `Translattribute.get_inline_attribute`.
    fn get_inline_attribute_from(
        &mut self,
        attrs: &crate::parser::ast::Attributes,
    ) -> InlineAttribute {
        let idx = self.find_inline_attribute_index(attrs, "inline");
        self.parse_inline_attribute(idx.map(|idx| &attrs.as_slice()[idx]))
    }

    fn get_inlined_attribute_from(
        &mut self,
        attrs: &crate::parser::ast::Attributes,
    ) -> InlineAttribute {
        let idx = self.find_inline_attribute_index(attrs, "inlined");
        self.parse_inline_attribute(idx.map(|idx| &attrs.as_slice()[idx]))
    }

    fn with_inlined_attribute_check_suppressed<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.suppress_inlined_attribute_check += 1;
        let result = f(self);
        self.suppress_inlined_attribute_check -= 1;
        result
    }

    /// Mirrors `Translattribute.check_attribute` for expression attributes.
    fn check_expr_attribute(&mut self, expr: &Expression) {
        for (located_name, _) in expr.exp_attributes.iter() {
            let name = self.arena.get_string(located_name.txt);
            match name {
                "inline" => {
                    if !matches!(expr.exp_desc, ExpressionDesc::Texp_function { .. }) {
                        self.report_warning(
                            located_name.loc,
                            Warning::MisplacedAttribute {
                                name: name.to_string(),
                            },
                        );
                    }
                }
                "inlined" => {
                    if self.suppress_inlined_attribute_check > 0 {
                        continue;
                    }
                    self.report_warning(
                        located_name.loc,
                        Warning::MisplacedAttribute {
                            name: name.to_string(),
                        },
                    );
                }
                _ => {}
            }
        }
    }

    /// Mirrors `Translattribute.check_attribute_on_module` for module attributes.
    fn check_module_attribute(&mut self, module_expr: &ModuleExpr) {
        for (located_name, _) in module_expr.mod_attributes.iter() {
            let name = self.arena.get_string(located_name.txt);
            match name {
                "inline" => {
                    if !matches!(module_expr.mod_desc, ModuleExprDesc::Tmod_functor(..)) {
                        self.report_warning(
                            located_name.loc,
                            Warning::MisplacedAttribute {
                                name: name.to_string(),
                            },
                        );
                    }
                }
                "inlined" => {
                    if self.suppress_inlined_attribute_check > 0 {
                        continue;
                    }
                    self.report_warning(
                        located_name.loc,
                        Warning::MisplacedAttribute {
                            name: name.to_string(),
                        },
                    );
                }
                _ => {}
            }
        }
    }

    /// Extract `@directive("...")` from function expression attributes,
    /// matching OCaml's `extract_directive_for_fn`.
    fn get_directive_attribute_from(
        attrs: &crate::parser::ast::Attributes,
        arena: &ParseArena,
    ) -> Option<String> {
        // translcore.ml `extract_directive_for_fn`: the first `directive`
        // attribute whose payload is a string, read by
        // `Ast_payload.semantic_string_of_payload`.
        for (located_name, payload) in attrs.iter() {
            if arena.get_string(located_name.txt) != "directive" {
                continue;
            }
            if let Some(directive) = crate::ast_payload::semantic_string_of_payload(arena, payload)
                .ok()
                .flatten()
            {
                return Some(directive);
            }
        }
        None
    }

    /// Apply an inline attribute to a raw function, matching OCaml's
    /// `Translattribute.add_inline_attribute`.
    fn apply_inline_attribute_raw(
        &mut self,
        lam: RawLambda,
        loc: LocIdx,
        inline: InlineAttribute,
    ) -> RawLambda {
        if matches!(inline, InlineAttribute::Default) {
            return lam;
        }
        match lam {
            RawLambda::Lfunction(mut func) => {
                if !matches!(func.attr.inline, InlineAttribute::Default) {
                    self.report_warning(
                        loc,
                        Warning::DuplicatedAttribute {
                            name: "inline".to_string(),
                        },
                    );
                }
                func.attr.inline = inline;
                RawLambda::Lfunction(func)
            }
            other => {
                if matches!(inline, InlineAttribute::Default) {
                    return other;
                }
                self.report_warning(
                    loc,
                    Warning::MisplacedAttribute {
                        name: "inline".to_string(),
                    },
                );
                other
            }
        }
    }

    fn functor_path(
        rootpath: &Option<crate::types::Path>,
        param: &Ident,
    ) -> Option<crate::types::Path> {
        rootpath.as_ref().map(|path| {
            crate::types::Path::papply(path.clone(), crate::types::Path::pident(*param))
        })
    }

    fn transl_extension_constructor_raw(
        &mut self,
        path: Option<crate::types::Path>,
        ext: &crate::types::typedtree::ExtensionConstructor,
    ) -> RawLambda {
        let name = path
            .as_ref()
            .map(crate::types::Path::name)
            .unwrap_or_else(|| ext.ext_id.name().to_string());
        let loc = ext.ext_loc;
        match &ext.ext_kind {
            crate::types::typedtree::ExtensionConstructorKind::Text_decl(_, _) => {
                RawLambda::prim(Primitive::PcreateExtension(name), vec![], self.lam_loc(loc))
            }
            crate::types::typedtree::ExtensionConstructorKind::Text_rebind(path, _) => {
                self.translate_extension_path_raw(path, SrcLoc::from(loc))
            }
        }
    }

    fn transl_type_extension_raw(
        &mut self,
        rootpath: &Option<crate::types::Path>,
        tyext: &crate::types::typedtree::TypeExtension,
        body: RawLambda,
    ) -> RawLambda {
        tyext
            .tyext_constructors
            .iter()
            .rev()
            .fold(body, |acc, ext| {
                RawLambda::let_(
                    LetKind::Strict,
                    ext.ext_id,
                    self.transl_extension_constructor_raw(
                        Self::field_path(rootpath, &ext.ext_id),
                        ext,
                    ),
                    acc,
                )
            })
    }

    fn raw_loc_kind(name: &str) -> Option<RawLocKind> {
        match name {
            "%loc_FILE" => Some(RawLocKind::File),
            "%loc_LINE" => Some(RawLocKind::Line),
            "%loc_MODULE" => Some(RawLocKind::Module),
            "%loc_LOC" => Some(RawLocKind::Loc),
            "%loc_POS" => Some(RawLocKind::Pos),
            _ => None,
        }
    }

    fn type_desc(&self, ty: TypeExprRef) -> TypeDesc {
        (*self.type_ctx.get_desc(self.type_ctx.repr(ty))).clone()
    }

    fn is_function_type_with_env(
        &self,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
    ) -> Option<(TypeExprRef, TypeExprRef)> {
        let ty = self.type_ctx.repr(ty);
        if let Some(parts) = crate::types::ctype::split_arrow(self.type_ctx, ty) {
            return Some(parts);
        }
        match &*self.type_ctx.get_desc(ty) {
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                self.is_function_type_with_env(*next, env)
            }
            TypeDesc::Tconstr { .. } => {
                let expanded = crate::types::ctype::expand_head(self.type_ctx, env, ty);
                if expanded == ty {
                    None
                } else {
                    self.is_function_type_with_env(expanded, env)
                }
            }
            _ => None,
        }
    }

    fn get_function_arity_from_type(
        &self,
        env: &crate::types::env::Env,
        ty: TypeExprRef,
    ) -> Option<i32> {
        let repr = self.type_ctx.repr(ty);
        match &*self.type_ctx.get_desc(repr) {
            TypeDesc::Tarrow { args, .. } => Some(args.len() as i32),
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                self.get_function_arity_from_type(env, *next)
            }
            TypeDesc::Tconstr { .. } => {
                let expanded = crate::types::ctype::expand_head(self.type_ctx, env, ty);
                if expanded == ty {
                    None
                } else {
                    self.get_function_arity_from_type(env, expanded)
                }
            }
            _ => None,
        }
    }

    fn is_base_type(&self, ty: TypeExprRef, name: &str) -> bool {
        self.is_base_type_with_env(ty, name, self.env)
    }

    fn is_base_type_with_env(
        &self,
        ty: TypeExprRef,
        name: &str,
        env: &crate::types::env::Env,
    ) -> bool {
        // OCaml primitive specialization goes through `Typeopt.is_base_type`
        // (compiler/ml/translcore.ml:407-415), whose `scrape` uses
        // `Ctype.expand_head_opt` (compiler/ml/typeopt.ml:19-31,99-101).
        typeopt_is_base_type(self.type_ctx, env, ty, name)
    }

    fn is_immediate_type_with_env(&self, ty: TypeExprRef, env: &crate::types::env::Env) -> bool {
        use crate::types::btype;
        use crate::types::type_expr::TypeDesc;

        // Match OCaml `Ctype.maybe_pointer_type`: for `Tconstr`, inspect only
        // `Env.find_type p env` and its `type_immediate` bit; do not chase the
        // manifest here (compiler/ml/ctype.ml:4492-4512). `Translcore`
        // chooses integer comparison when that result is `Immediate`
        // (compiler/ml/translcore.ml:407-415).
        let ty = self.type_ctx.repr(ty);
        match &*self.type_ctx.get_desc(ty) {
            TypeDesc::Tconstr { path, .. } => {
                if let Some(decl) =
                    crate::raw_lambda::typeopt::find_type_decl(self.type_ctx, env, path)
                {
                    return decl.type_immediate;
                }
                false
            }
            TypeDesc::Tvariant(row) => {
                let row = btype::row_repr(self.type_ctx, row);
                row.row_closed
                    && !row.row_fields.iter().any(|(_, f)| {
                        matches!(
                            btype::row_field_repr(self.type_ctx, f),
                            crate::types::type_expr::RowField::Rpresent(Some(_))
                                | crate::types::type_expr::RowField::Reither {
                                    constant: false,
                                    ..
                                }
                        )
                    })
            }
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                self.is_immediate_type_with_env(*next, env)
            }
            _ => false,
        }
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

    fn loc_coords(loc: Location) -> (i32, i32, i32) {
        let line = loc.loc_start.line;
        let start_col = loc.loc_start.column();
        let end_col = loc.loc_end.cnum - loc.loc_start.cnum + start_col;
        (line, start_col, end_col)
    }

    fn raw_loc_constant(&self, kind: RawLocKind, loc: SrcLoc) -> RawLambda {
        // `__FILE__` and `__MODULE__` read only the unit and the source file
        // name, which a location-free arena keeps for source locations; the
        // other kinds (and generated or declaration locations) read real
        // coordinates and need the located retry.
        let needs_coordinates = match kind {
            RawLocKind::Line | RawLocKind::Loc | RawLocKind::Pos => true,
            RawLocKind::Module if !self.unit_name.is_empty() => false,
            RawLocKind::File | RawLocKind::Module => {
                matches!(loc, SrcLoc::Decl(_)) || self.is_ghost_loc(loc)
            }
        };
        if needs_coordinates {
            self.arena.require_locations();
        }
        let loc = self.loc(loc);
        let file = self.basename_for_loc(loc);
        let (line, start_col, end_col) = Self::loc_coords(loc);
        match kind {
            RawLocKind::File => RawLambda::const_(Constant::ImmString(file)),
            RawLocKind::Line => RawLambda::const_(Constant::int(line)),
            RawLocKind::Module => {
                RawLambda::const_(Constant::ImmString(if self.unit_name.is_empty() {
                    format!("//{file}//")
                } else {
                    self.unit_name.clone()
                }))
            }
            RawLocKind::Loc => RawLambda::const_(Constant::ImmString(format!(
                "File {file:?}, line {line}, characters {start_col}-{end_col}"
            ))),
            RawLocKind::Pos => RawLambda::const_(Constant::Block {
                tag_info: Box::new(TagInfo::Tuple),
                elements: vec![
                    Constant::ImmString(file),
                    Constant::int(line),
                    Constant::int(start_col),
                    Constant::int(end_col),
                ],
            }),
        }
    }

    fn value_path_loc_constant(&self, path: &crate::types::Path, loc: SrcLoc) -> Option<RawLambda> {
        let crate::types::path::PathView::Pdot(prefix, name, _) = path.view() else {
            return None;
        };
        let crate::types::path::PathView::Pident(id) = prefix.view() else {
            return None;
        };
        if id.name() != "Pervasives" {
            return None;
        }
        let kind = match name.as_str() {
            "__FILE__" => RawLocKind::File,
            "__LINE__" => RawLocKind::Line,
            "__MODULE__" => RawLocKind::Module,
            "__LOC__" => RawLocKind::Loc,
            "__POS__" => RawLocKind::Pos,
            _ => return None,
        };
        Some(self.raw_loc_constant(kind, loc))
    }

    fn failure_payload(&self, loc: LocIdx) -> Constant {
        self.arena.require_locations();
        let loc = self.loc(loc);
        Constant::Block {
            tag_info: Box::new(TagInfo::Tuple),
            elements: vec![
                Constant::const_string(&self.basename_for_loc(loc)),
                Constant::int(loc.loc_start.line),
                Constant::int(loc.loc_start.column()),
            ],
        }
    }

    fn raise_predef_exception(&self, name: &str, stamp: i32, loc: LocIdx) -> Lambda {
        let exn = Lambda::global_module(predef_exception_ident(name, stamp));
        let payload = Lambda::const_(self.failure_payload(loc));
        let block = Lambda::prim(
            Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
            vec![exn, payload],
            self.lam_loc(loc),
        );
        Lambda::prim(Primitive::Praise, vec![block], self.lam_loc(loc))
    }

    fn raw_assert_failed(&self, loc: LocIdx) -> RawLambda {
        RawLambda::from_lowered(self.raise_predef_exception(
            "Assert_failure",
            PREDEF_ASSERT_FAILURE_STAMP,
            loc,
        ))
    }

    fn raw_assert_false(&self, loc: LocIdx) -> RawLambda {
        // OCaml translcore.ml:926-931 only lowers `assert false` to
        // Lambda.lambda_assert_false when -bs-noassertfalse is active.
        if !self.no_assert_false {
            return self.raw_assert_failed(loc);
        }
        RawLambda::const_(Constant::int_with_comment(
            0,
            crate::lambda::lam_constant::PointerInfo::AssertFalse,
        ))
    }

    fn translate_unified_ops_primitive(
        &self,
        prim_name: &str,
        lhs_type: TypeExprRef,
    ) -> Option<Primitive> {
        self.translate_unified_ops_primitive_with_env(prim_name, lhs_type, self.env)
    }

    fn translate_unified_ops_primitive_with_env(
        &self,
        prim_name: &str,
        lhs_type: TypeExprRef,
        env: &crate::types::env::Env,
    ) -> Option<Primitive> {
        let choose = |int_prim: Primitive,
                      bool_prim: Option<Primitive>,
                      float_prim: Option<Primitive>,
                      bigint_prim: Option<Primitive>,
                      string_prim: Option<Primitive>| {
            if self.is_base_type_with_env(lhs_type, "int", env)
                || self.is_immediate_type_with_env(lhs_type, env)
            {
                int_prim
            } else if self.is_base_type_with_env(lhs_type, "float", env) {
                float_prim.unwrap_or(int_prim)
            } else if self.is_base_type_with_env(lhs_type, "bigint", env) {
                bigint_prim.unwrap_or(int_prim)
            } else if self.is_base_type_with_env(lhs_type, "string", env) {
                string_prim.unwrap_or(int_prim)
            } else if self.is_base_type_with_env(lhs_type, "bool", env) {
                bool_prim.unwrap_or(int_prim)
            } else {
                int_prim
            }
        };

        Some(match prim_name {
            // unified_ops.ml:60-71: unary `+` is the identity on every
            // supported operand type.
            "%plus" => choose(
                Primitive::Pidentity,
                None,
                Some(Primitive::Pidentity),
                Some(Primitive::Pidentity),
                None,
            ),
            "%neg" => choose(
                Primitive::Pnegint,
                None,
                Some(Primitive::Pnegfloat),
                Some(Primitive::Pnegbigint),
                None,
            ),
            "%add" => choose(
                Primitive::Paddint,
                None,
                Some(Primitive::Paddfloat),
                Some(Primitive::Paddbigint),
                Some(Primitive::Pstringadd),
            ),
            "%sub" => choose(
                Primitive::Psubint,
                None,
                Some(Primitive::Psubfloat),
                Some(Primitive::Psubbigint),
                None,
            ),
            "%mul" => choose(
                Primitive::Pmulint,
                None,
                Some(Primitive::Pmulfloat),
                Some(Primitive::Pmulbigint),
                None,
            ),
            "%div" => choose(
                Primitive::Pdivint,
                None,
                Some(Primitive::Pdivfloat),
                Some(Primitive::Pdivbigint),
                None,
            ),
            "%mod" => choose(
                Primitive::Pmodint,
                None,
                Some(Primitive::Pmodfloat),
                Some(Primitive::Pmodbigint),
                None,
            ),
            "%pow" => choose(
                Primitive::Ppowint,
                None,
                Some(Primitive::Ppowfloat),
                Some(Primitive::Ppowbigint),
                None,
            ),
            "%lsl" => choose(
                Primitive::Plslint,
                None,
                None,
                Some(Primitive::Plslbigint),
                None,
            ),
            "%asr" => choose(
                Primitive::Pasrint,
                None,
                None,
                Some(Primitive::Pasrbigint),
                None,
            ),
            "%lsr" => Primitive::Plsrint,
            "%bitnot" => choose(
                Primitive::Pnotint,
                None,
                None,
                Some(Primitive::Pnotbigint),
                None,
            ),
            "%bitor" => choose(
                Primitive::Porint,
                None,
                None,
                Some(Primitive::Porbigint),
                None,
            ),
            "%bitxor" => choose(
                Primitive::Pxorint,
                None,
                None,
                Some(Primitive::Pxorbigint),
                None,
            ),
            "%bitand" => choose(
                Primitive::Pandint,
                None,
                None,
                Some(Primitive::Pandbigint),
                None,
            ),
            _ => return None,
        })
    }

    fn comparison_specialization(prim_name: &str) -> Option<ComparisonSpecialization> {
        let table = |cmp: crate::lambda::Comparison, simplify_constant_constructor| {
            ComparisonSpecialization {
                objcomp: Primitive::Pobjcomp(cmp),
                intcomp: Primitive::Pintcomp(cmp),
                boolcomp: Primitive::Pboolcomp(cmp),
                floatcomp: Primitive::Pfloatcomp(cmp),
                stringcomp: Primitive::Pstringcomp(cmp),
                bigintcomp: Primitive::Pbigintcomp(cmp),
                simplify_constant_constructor,
            }
        };

        Some(match prim_name {
            "%equal" => table(crate::lambda::Comparison::Eq, true),
            "%notequal" => table(crate::lambda::Comparison::Neq, true),
            "%lessthan" => table(crate::lambda::Comparison::Lt, false),
            "%greaterthan" => table(crate::lambda::Comparison::Gt, false),
            "%lessequal" => table(crate::lambda::Comparison::Le, false),
            "%greaterequal" => table(crate::lambda::Comparison::Ge, false),
            "%equal_null" => table(crate::lambda::Comparison::Eq, false),
            "%equal_undefined" => table(crate::lambda::Comparison::Eq, false),
            "%equal_nullable" => table(crate::lambda::Comparison::Eq, false),
            "%compare" => ComparisonSpecialization {
                objcomp: Primitive::Pobjorder,
                intcomp: Primitive::Pintorder,
                boolcomp: Primitive::Pboolorder,
                floatcomp: Primitive::Pfloatorder,
                stringcomp: Primitive::Pstringorder,
                bigintcomp: Primitive::Pbigintorder,
                simplify_constant_constructor: false,
            },
            "%max" | "%bs_max" => ComparisonSpecialization {
                objcomp: Primitive::Pobjmax,
                intcomp: Primitive::Pintmax,
                boolcomp: Primitive::Pboolmax,
                floatcomp: Primitive::Pfloatmax,
                stringcomp: Primitive::Pstringmax,
                bigintcomp: Primitive::Pbigintmax,
                simplify_constant_constructor: false,
            },
            "%min" | "%bs_min" => ComparisonSpecialization {
                objcomp: Primitive::Pobjmin,
                intcomp: Primitive::Pintmin,
                boolcomp: Primitive::Pboolmin,
                floatcomp: Primitive::Pfloatmin,
                stringcomp: Primitive::Pstringmin,
                bigintcomp: Primitive::Pbigintmin,
                simplify_constant_constructor: false,
            },
            _ => return None,
        })
    }

    fn specialize_comparison_in_env(
        &self,
        table: ComparisonSpecialization,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
    ) -> Primitive {
        if self.is_base_type_with_env(ty, "int", env)
            || self.is_base_type_with_env(ty, "char", env)
            || self.is_immediate_type_with_env(ty, env)
        {
            table.intcomp
        } else if self.is_base_type_with_env(ty, "float", env) {
            table.floatcomp
        } else if self.is_base_type_with_env(ty, "string", env) {
            table.stringcomp
        } else if self.is_base_type_with_env(ty, "bigint", env) {
            table.bigintcomp
        } else if self.is_base_type_with_env(ty, "bool", env) {
            table.boolcomp
        } else {
            table.objcomp
        }
    }

    /// Like specialize_comparison but uses the expression's stored env for type checks.
    /// This avoids the issue where self.env (the initial env) doesn't have local type
    /// definitions, causing expand_head to produce incorrect expansions.
    fn specialize_comparison_with_env(
        &self,
        table: ComparisonSpecialization,
        arg: &Expression,
    ) -> Primitive {
        let ty = arg.exp_type;
        let env = self.env_for_expr(arg);
        let env_ref = env.as_deref().unwrap_or(self.env);
        self.specialize_comparison_in_env(table, ty, env_ref)
    }

    fn has_constant_constructor_arg(expr: &Expression) -> bool {
        match &expr.exp_desc {
            ExpressionDesc::Texp_construct(_, cstr, _) => {
                cstr.cstr_args.is_empty()
                    && matches!(cstr.cstr_kind, crate::types::ConstructorKind::Ordinary(_))
            }
            ExpressionDesc::Texp_variant(_, None) => true,
            _ => false,
        }
    }

    fn find_raw_primitive(&self, prim_name: &str) -> Option<Primitive> {
        match prim_name {
            "%makeref" => Some(Primitive::Pmakeblock(TagInfo::ref_tag(), Mutable::Mutable)),
            "%refset" => Some(Primitive::Psetfield(
                0,
                crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet("contents".to_string()),
            )),
            "%identity" | "%component_identity" => Some(Primitive::Pidentity),
            "%ignore" => Some(Primitive::Pignore),
            // Direct bigint primitives (used by Js.BigInt externals)
            "%negbigint" => Some(Primitive::Pnegbigint),
            "%addbigint" => Some(Primitive::Paddbigint),
            "%subbigint" => Some(Primitive::Psubbigint),
            "%mulbigint" => Some(Primitive::Pmulbigint),
            "%divbigint" => Some(Primitive::Pdivbigint),
            "%powbigint" => Some(Primitive::Ppowbigint),
            "%modbigint" => Some(Primitive::Pmodbigint),
            "%andbigint" => Some(Primitive::Pandbigint),
            "%orbigint" => Some(Primitive::Porbigint),
            "%xorbigint" => Some(Primitive::Pxorbigint),
            "%bitnot_bigint" => Some(Primitive::Pnotbigint),
            "%lslbigint" => Some(Primitive::Plslbigint),
            "%asrbigint" => Some(Primitive::Pasrbigint),
            "%bigintorder" => Some(Primitive::Pbigintorder),
            "%bigintmin" => Some(Primitive::Pbigintmin),
            "%bigintmax" => Some(Primitive::Pbigintmax),
            "%eqbigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Eq)),
            "%noteqbigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Neq)),
            "%ltbigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Lt)),
            "%lebigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Le)),
            "%gtbigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Gt)),
            "%gebigint" => Some(Primitive::Pbigintcomp(crate::lambda::Comparison::Ge)),
            // Method wrapping
            "%unsafe_to_method" => Some(Primitive::PjsFnMethod),
            "%obj_tag" => Some(Primitive::Pobjtag),
            "%obj_size" => Some(Primitive::Pobjsize),
            "%obj_dup" => Some(Primitive::Pduprecord),
            "%obj_get_field" => Some(Primitive::Parrayrefu),
            "%obj_set_field" => Some(Primitive::Parraysetu),
            // Type-specialized int primitives (from OCaml's prim_table)
            // These are the resolved forms of unified ops when the type is int
            "%negint" => Some(Primitive::Pnegint),
            "%addint" => Some(Primitive::Paddint),
            "%subint" => Some(Primitive::Psubint),
            "%mulint" => Some(Primitive::Pmulint),
            "%divint" => Some(Primitive::Pdivint),
            "%modint" => Some(Primitive::Pmodint),
            "%bitnot_int" => Some(Primitive::Pnotint),
            "%andint" => Some(Primitive::Pandint),
            "%orint" => Some(Primitive::Porint),
            "%xorint" => Some(Primitive::Pxorint),
            "%lslint" => Some(Primitive::Plslint),
            "%lsrint" => Some(Primitive::Plsrint),
            "%asrint" => Some(Primitive::Pasrint),
            // Type-specialized float primitives
            "%negfloat" => Some(Primitive::Pnegfloat),
            "%addfloat" => Some(Primitive::Paddfloat),
            "%subfloat" => Some(Primitive::Psubfloat),
            "%mulfloat" => Some(Primitive::Pmulfloat),
            "%divfloat" => Some(Primitive::Pdivfloat),
            "%modfloat" => Some(Primitive::Pmodfloat),
            "%powfloat" => Some(Primitive::Ppowfloat),
            // Type-specialized int comparison primitives
            "%eq" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Eq)),
            "%noteq" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Neq)),
            "%ltint" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Lt)),
            "%leint" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Le)),
            "%gtint" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Gt)),
            "%geint" => Some(Primitive::Pintcomp(crate::lambda::Comparison::Ge)),
            // Type-specialized float comparison primitives
            "%eqfloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Eq)),
            "%noteqfloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Neq)),
            "%ltfloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Lt)),
            "%lefloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Le)),
            "%gtfloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Gt)),
            "%gefloat" => Some(Primitive::Pfloatcomp(crate::lambda::Comparison::Ge)),
            // Type-specialized string comparison primitives
            "%eqstring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Eq)),
            "%noteqstring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Neq)),
            "%ltstring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Lt)),
            "%lestring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Le)),
            "%gtstring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Gt)),
            "%gestring" => Some(Primitive::Pstringcomp(crate::lambda::Comparison::Ge)),
            // Type-specialized bool comparison primitives
            "%eqbool" => Some(Primitive::Pboolcomp(crate::lambda::Comparison::Eq)),
            "%noteqbool" => Some(Primitive::Pboolcomp(crate::lambda::Comparison::Neq)),
            // Order/min/max primitives
            "%intorder" => Some(Primitive::Pintorder),
            "%intmin" => Some(Primitive::Pintmin),
            "%intmax" => Some(Primitive::Pintmax),
            "%floatorder" => Some(Primitive::Pfloatorder),
            "%floatmin" => Some(Primitive::Pfloatmin),
            "%floatmax" => Some(Primitive::Pfloatmax),
            "%boolorder" => Some(Primitive::Pboolorder),
            "%boolmin" => Some(Primitive::Pboolmin),
            "%boolmax" => Some(Primitive::Pboolmax),
            "%stringorder" => Some(Primitive::Pstringorder),
            "%stringmin" => Some(Primitive::Pstringmin),
            "%stringmax" => Some(Primitive::Pstringmax),
            // Other specialized primitives
            "%obj_is_int" => Some(Primitive::Pisint),
            "%boolnot" => Some(Primitive::Pnot),
            "%sequand" => Some(Primitive::Psequand),
            "%sequor" => Some(Primitive::Psequor),
            "%raise" => Some(Primitive::Praise),
            "%string_length" => Some(Primitive::Pstringlength),
            "%string_safe_get" => Some(Primitive::Pstringrefs),
            "%string_unsafe_get" => Some(Primitive::Pstringrefu),
            "%string_concat" => Some(Primitive::Pstringadd),
            "%array_length" => Some(Primitive::Parraylength),
            "%array_safe_get" => Some(Primitive::Parrayrefs),
            "%array_safe_set" => Some(Primitive::Parraysets),
            "%array_unsafe_get" => Some(Primitive::Parrayrefu),
            "%array_unsafe_set" => Some(Primitive::Parraysetu),
            "%makedict" => Some(Primitive::Pmakedict),
            "%dict_has" => Some(Primitive::PdictHas),
            "%await" => Some(Primitive::Pawait),
            "%hash" => Some(Primitive::Phash),
            "%hash_mix_int" => Some(Primitive::PhashMixint),
            "%hash_mix_string" => Some(Primitive::PhashMixstring),
            "%hash_final_mix" => Some(Primitive::PhashFinalmix),
            "%typeof" => Some(Primitive::Ptypeof),
            "%debugger" => Some(Primitive::Pdebugger),
            "%intoffloat" => Some(Primitive::Pintoffloat),
            "%floatofint" => Some(Primitive::Pfloatofint),
            "%unsafe_eq" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Eq)),
            "%unsafe_neq" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Neq)),
            "%unsafe_lt" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Lt)),
            "%unsafe_le" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Le)),
            "%unsafe_gt" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Gt)),
            "%unsafe_ge" => Some(Primitive::Pjscomp(crate::lambda::Comparison::Ge)),
            "%is_nullable" => Some(Primitive::PisNullUndefined),
            "%null_to_opt" => Some(Primitive::PnullToOpt),
            "%nullable_to_opt" => Some(Primitive::PnullUndefinedToOpt),
            "%powint" => Some(Primitive::Ppowint),
            // OCaml translcore.ml:377-387 maps these runtime externals to
            // dedicated primitives before lambda conversion.
            "%function_arity" => Some(Primitive::PfnArity),
            "%curry_apply1" => Some(Primitive::PjsApply),
            "%curry_apply2" => Some(Primitive::PjsApply),
            "%curry_apply3" => Some(Primitive::PjsApply),
            "%curry_apply4" => Some(Primitive::PjsApply),
            "%curry_apply5" => Some(Primitive::PjsApply),
            "%curry_apply6" => Some(Primitive::PjsApply),
            "%curry_apply7" => Some(Primitive::PjsApply),
            "%curry_apply8" => Some(Primitive::PjsApply),
            "%makemutablelist" => Some(Primitive::Pmakelist),
            // #-prefixed primitives (from OCaml's translcore.ml prim_table)
            "#typeof" => Some(Primitive::Ptypeof),
            "#is_nullable" => Some(Primitive::PisNullUndefined),
            "#null_to_opt" => Some(Primitive::PnullToOpt),
            "#nullable_to_opt" => Some(Primitive::PnullUndefinedToOpt),
            "#makemutablelist" => Some(Primitive::Pmakelist),
            _ => {
                // %fieldN -> Pfield(N, Fld_tuple)
                if let Some(n_str) = prim_name.strip_prefix("%field") {
                    if let Ok(n) = n_str.parse::<i32>() {
                        return Some(Primitive::Pfield(n, FieldDbgInfo::Tuple));
                    }
                }
                // %setfieldN -> Psetfield(N, ...)
                if let Some(n_str) = prim_name.strip_prefix("%setfield") {
                    if let Ok(n) = n_str.parse::<i32>() {
                        return Some(Primitive::Psetfield(
                            n,
                            crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet(String::new()),
                        ));
                    }
                }
                None
            }
        }
    }

    /// Translcore.transl_primitive for a coercion (`~val_type:pc_type`,
    /// translmod.ml:94-95 and 352-354).
    fn transl_primitive_raw(
        &mut self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        loc: SrcLoc,
    ) -> RawLambda {
        let env = self.env;
        self.translate_primitive_raw_in_env(loc, prim, ty, env, ty, None)
    }

    fn specialize_primitive_raw(
        &self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
    ) -> Option<Primitive> {
        self.specialize_primitive_raw_with_env(prim, ty, self.env)
    }

    fn specialize_primitive_raw_with_env(
        &self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
    ) -> Option<Primitive> {
        let prim_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some((lhs, _)) = self.is_function_type_with_env(ty, env) {
            if let Some(primitive) =
                self.translate_unified_ops_primitive_with_env(prim_name, lhs, env)
            {
                return Some(primitive);
            }
            if let Some(table) = Self::comparison_specialization(prim_name) {
                return Some(self.specialize_comparison_in_env(table, lhs, env));
            }
        } else if let Some(table) = Self::comparison_specialization(prim_name) {
            return Some(table.objcomp);
        }

        self.find_raw_primitive(prim_name)
    }

    /// Translcore.transl_primitive_application: `None` means the primitive
    /// is an external whose application must be expanded from its FFI spec.
    fn translate_primitive_application_raw(
        &mut self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        args: &[&Expression],
        loc: SrcLoc,
    ) -> Option<Primitive> {
        let prim_name = Self::raw_primitive_name(&prim.prim_name).to_string();

        if let [arg1] | [arg1, _] = args {
            if let Some(primitive) = self.translate_unified_ops_primitive(&prim_name, arg1.exp_type)
            {
                return Some(primitive);
            }
        }

        if let [arg1, _] = args {
            if let Some(table) = Self::comparison_specialization(&prim_name) {
                if self.is_base_type(arg1.exp_type, "bool") {
                    return Some(table.boolcomp);
                }
                if args
                    .iter()
                    .any(|arg| Self::has_constant_constructor_arg(arg))
                    && table.simplify_constant_constructor
                {
                    return Some(table.intcomp);
                }
                // Use arg's type directly for specialization, matching OCaml's
                // transl_prim_2 which checks the arg's exp_type via its env.
                // specialize_primitive_raw falls back to funct.exp_type with self.env
                // which may not have local type definitions, causing incorrect expansion.
                return Some(self.specialize_comparison_with_env(table, arg1));
            }
        }

        let primitive = self.specialize_primitive_raw(prim, ty);
        if primitive.is_none() {
            // translcore.ml:852-855.
            self.report_unknown_builtin_primitive(loc, &prim_name);
        }
        primitive
    }

    /// `Translcore.lambda_of_inline_const`.
    fn lambda_of_inline_const(c: &crate::types::external_ffi_types::InlineConst) -> Constant {
        use crate::types::external_ffi_types::InlineConst;
        match c {
            InlineConst::ConstString(s) => Constant::String(s.clone()),
            InlineConst::ConstBool(true) => Constant::JsTrue,
            InlineConst::ConstBool(false) => Constant::JsFalse,
            InlineConst::ConstInt(i) => Constant::Int {
                i: *i,
                comment: None,
            },
            // The `negative` field holds `Bigint_utils.parse_bigint`'s sign
            // flag, true for a positive literal (ast_external_mk.ml).
            InlineConst::ConstBigint { negative, digits } => Constant::BigInt {
                negative: !*negative,
                value: digits.clone(),
            },
            InlineConst::ConstFloat(f) => Constant::Float(f.clone()),
        }
    }

    /// `Translcore.external_returns_unit`: does the external's declared type
    /// return unit? Computed from the declared scheme so it is stable across
    /// use sites; aliases of unit count as unit.
    fn external_returns_unit(
        &self,
        env: &crate::types::env::Env,
        prim: &crate::types::PrimitiveDescription,
        val_type: TypeExprRef,
    ) -> bool {
        let result_type = if prim.prim_arity == 0 {
            val_type
        } else {
            let expanded = crate::types::ctype::expand_head(self.type_ctx, env, val_type);
            let repr = self.type_ctx.repr(expanded);
            match &*self.type_ctx.get_desc(repr) {
                TypeDesc::Tarrow { ret, .. } => *ret,
                _ => val_type,
            }
        };
        self.is_base_type_with_env(result_type, "unit", env)
    }

    /// `Translcore.external_result_wrap`.
    fn external_result_wrap(
        loc: LamLoc,
        result_type: crate::types::external_ffi_types::ReturnWrapper,
        returns_unit: bool,
        result: RawLambda,
    ) -> RawLambda {
        use crate::types::external_ffi_types::ReturnWrapper;
        match result_type {
            ReturnWrapper::ReturnUnset if returns_unit => RawLambda::seq(result, RawLambda::unit()),
            ReturnWrapper::ReturnNullToOpt => {
                RawLambda::prim(Primitive::PnullToOpt, vec![result], loc)
            }
            ReturnWrapper::ReturnNullUndefinedToOpt => {
                RawLambda::prim(Primitive::PnullUndefinedToOpt, vec![result], loc)
            }
            ReturnWrapper::ReturnUnset | ReturnWrapper::ReturnIdentity => result,
        }
    }

    /// `Translcore.transl_external_application`.
    fn transl_external_application(
        &mut self,
        loc: SrcLoc,
        env: &crate::types::env::Env,
        prim: &crate::types::PrimitiveDescription,
        val_type: TypeExprRef,
        argl: Vec<RawLambda>,
        transformed_jsx: bool,
    ) -> RawLambda {
        use crate::types::decl::PrimKind;
        use crate::types::external_ffi_types::ExternalFfi;
        match &prim.prim_kind {
            PrimKind::KindInlineConst(c) => RawLambda::const_(Self::lambda_of_inline_const(c)),
            PrimKind::KindExternal(spec) => match spec.as_ref() {
                ExternalFfi::FfiObjCreate(labels) => RawLambda::prim(
                    Primitive::PjsObjectCreate(labels.clone()),
                    argl,
                    self.lam_loc(loc),
                ),
                ExternalFfi::FfiBs(arg_types, result_type, decl) => {
                    let returns_unit = self.external_returns_unit(env, prim, val_type);
                    let call = RawLambda::prim(
                        Primitive::PjsCall {
                            prim_name: prim.prim_name.clone(),
                            arg_types: arg_types.clone(),
                            ffi: Box::new(decl.clone()),
                            transformed_jsx,
                        },
                        argl,
                        self.lam_loc(loc),
                    );
                    Self::external_result_wrap(self.lam_loc(loc), *result_type, returns_unit, call)
                }
            },
            PrimKind::KindIntrinsic => {
                self.report_diagnostic(
                    self.loc(loc),
                    format!(
                        "\x1b[1;31mError:\x1b[0m internal error, using unrecognized primitive {}",
                        prim.prim_name
                    ),
                );
                RawLambda::unit()
            }
        }
    }

    /// `Translcore.import_source_of_arg`: the argument of the dynamic-import
    /// primitive is a module reference, never an expression; resolve it here,
    /// at translation, from the typedtree.
    fn import_source_of_arg(&mut self, arg: &Expression) -> Option<ImportSource> {
        use crate::types::decl::PrimKind;
        use crate::types::external_ffi_types::{
            DeclKind, ExternalFfi, ModuleBindName, ModuleSource,
        };
        let unsupported = |this: &mut Self, loc: LocIdx| {
            let loc = this.loc(loc);
            this.report_diagnostic(
                loc,
                "Invalid argument: unsupported argument to dynamic import. If you believe this should be supported, please open an issue.".to_string(),
            );
            None
        };
        fn module_path(me: &ModuleExpr) -> Option<&crate::types::path::Path> {
            match &me.mod_desc {
                ModuleExprDesc::Tmod_ident(path, _) => Some(path),
                ModuleExprDesc::Tmod_constraint(me, _, _, _) => module_path(me),
                _ => None,
            }
        }
        match &arg.exp_desc {
            ExpressionDesc::Texp_pack(me) => match module_path(me) {
                Some(path) => {
                    let env = self.env_for_module_expr(me);
                    self.import_of_global_path(true, arg.exp_loc, env.as_deref(), path)
                }
                None => unsupported(self, arg.exp_loc),
            },
            ExpressionDesc::Texp_ident(_, _, desc)
                if matches!(desc.val_kind, ValueKind::ValPrim(_)) =>
            {
                let ValueKind::ValPrim(p) = &desc.val_kind else {
                    unreachable!()
                };
                match &p.prim_kind {
                    PrimKind::KindExternal(spec) => match spec.as_ref() {
                        ExternalFfi::FfiBs(_, _, decl) => match (&decl.kind, &decl.module_) {
                            // the external's value lives at `module.<scopes>.<name>`
                            (DeclKind::DeclVal { name }, Some(ModuleSource::ModuleNamed(emn))) => {
                                let mut path = decl.scopes.clone();
                                path.push(name.clone());
                                Some(ImportSource::ImportExternal {
                                    module_: emn.clone(),
                                    path,
                                })
                            }
                            (DeclKind::DeclVal { .. }, Some(ModuleSource::ModuleItself)) => {
                                Some(ImportSource::ImportExternal {
                                    module_: ExternalModuleName {
                                        bundle: p.prim_name.clone(),
                                        module_bind_name: ModuleBindName::PhintNothing,
                                        import_attributes: None,
                                    },
                                    path: vec![],
                                })
                            }
                            _ => unsupported(self, arg.exp_loc),
                        },
                        ExternalFfi::FfiObjCreate(_) => unsupported(self, arg.exp_loc),
                    },
                    _ => unsupported(self, arg.exp_loc),
                }
            }
            ExpressionDesc::Texp_ident(path, _, _) => {
                let env = self.env_for_expr(arg);
                self.import_of_global_path(false, arg.exp_loc, env.as_deref(), path)
            }
            _ => unsupported(self, arg.exp_loc),
        }
    }

    /// `of_global_path` in `Translcore.import_source_of_arg`: a module path is
    /// normalized fully (resolving a final alias hop such as a namespace's
    /// `module List = Stdlib_List`); a value path normalizes its module prefix.
    fn import_of_global_path(
        &mut self,
        is_module: bool,
        loc: LocIdx,
        env: Option<&crate::types::env::Env>,
        path: &crate::types::path::Path,
    ) -> Option<ImportSource> {
        use crate::types::path::Path;
        let env = env.unwrap_or(self.env);
        let path = if is_module {
            self.normalize_module_path_in_env(env, path)
        } else {
            self.normalize_value_path_in_env(env, path)
        };
        fn segments(p: &Path, acc: Vec<String>) -> Option<(Ident, Vec<String>)> {
            match p.view() {
                PathView::Pident(id) => id.is_persistent().then_some((*id, acc)),
                PathView::Pdot(prefix, name, _) => {
                    let mut acc = acc;
                    acc.insert(0, name.to_string());
                    segments(prefix, acc)
                }
                PathView::Papply(..) => None,
            }
        }
        match segments(&path, Vec::new()) {
            Some((module_, path)) => Some(ImportSource::ImportModule { module_, path }),
            None => {
                let loc = loc;
                self.report_diagnostic(
                    self.loc(loc),
                    "Invalid argument: Dynamic import requires a module or module value that is a file as argument. Passing a value or local module is not allowed.".to_string(),
                );
                None
            }
        }
    }

    /// `Translcore.external_import_needs_adaptation`: does importing this
    /// external as a value require the FFI adaptation a direct call would
    /// apply?
    fn external_import_needs_adaptation(
        arg_types: &[crate::types::external_ffi_types::Param],
        decl: &crate::types::external_ffi_types::ExternalDecl,
        return_wrapper: crate::types::external_ffi_types::ReturnWrapper,
    ) -> bool {
        use crate::types::external_ffi_types::{Attr, LabelNoname, ReturnWrapper};
        decl.variadic
            || matches!(
                return_wrapper,
                ReturnWrapper::ReturnNullToOpt | ReturnWrapper::ReturnNullUndefinedToOpt
            )
            || arg_types.iter().any(|p| {
                !matches!(p.arg_type, Attr::Nothing | Attr::ExternUnit)
                    || matches!(p.arg_label, LabelNoname::ArgOptional)
            })
    }

    /// `Translcore.transl_adapted_external_import`: `import(f)` where `f`'s
    /// binding needs adaptation lowers to
    /// `import("module").then(m => (a1 .. an) => <adapted call of m.<f>>)`.
    #[allow(clippy::too_many_arguments)]
    fn transl_adapted_external_import(
        &mut self,
        loc: SrcLoc,
        env: &crate::types::env::Env,
        emn: &ExternalModuleName,
        name: &str,
        scopes: &[String],
        variadic: bool,
        arg_types: &[crate::types::external_ffi_types::Param],
        return_wrapper: crate::types::external_ffi_types::ReturnWrapper,
        prim: &crate::types::PrimitiveDescription,
        val_type: TypeExprRef,
    ) -> RawLambda {
        use crate::types::external_ffi_types::{DeclKind, ExternalDecl, Param};
        let returns_unit = self.external_returns_unit(env, prim, val_type);
        let node_loc = self.lam_loc(loc);
        let send_call = |receiver: RawLambda, args: Vec<RawLambda>, kind: DeclKind| {
            let mut send_arg_types = vec![Param::dummy()];
            send_arg_types.extend(arg_types.iter().cloned());
            let mut send_args = vec![receiver];
            send_args.extend(args);
            RawLambda::prim(
                Primitive::PjsCall {
                    prim_name: name.to_string(),
                    arg_types: send_arg_types,
                    ffi: Box::new(ExternalDecl {
                        kind,
                        module_: None,
                        scopes: scopes.to_vec(),
                        variadic,
                        effective_arity: arg_types.len() as i64 + 1,
                    }),
                    transformed_jsx: false,
                },
                send_args,
                node_loc,
            )
        };
        let m = self.fresh_ident("m");
        let adapted_value = if prim.prim_arity == 0 {
            Self::external_result_wrap(
                self.lam_loc(loc),
                return_wrapper,
                returns_unit,
                send_call(
                    RawLambda::var(m),
                    vec![],
                    DeclKind::DeclGet {
                        name: name.to_string(),
                    },
                ),
            )
        } else {
            let params: Vec<Ident> = (0..prim.prim_arity)
                .map(|i| self.fresh_ident(&format!("prim{i}")))
                .collect();
            let body = Self::external_result_wrap(
                self.lam_loc(loc),
                return_wrapper,
                returns_unit,
                send_call(
                    RawLambda::var(m),
                    params.iter().cloned().map(RawLambda::var).collect(),
                    DeclKind::DeclSend {
                        name: name.to_string(),
                    },
                ),
            );
            RawLambda::function_(
                prim.prim_arity,
                params,
                body,
                FunctionAttribute::default(),
                self.lam_loc(loc),
            )
        };
        let callback = RawLambda::function_(
            1,
            vec![m],
            adapted_value,
            FunctionAttribute::default(),
            self.lam_loc(loc),
        );
        RawLambda::prim(
            Primitive::PjsCall {
                prim_name: "then".to_string(),
                arg_types: vec![Param::dummy(), Param::dummy()],
                ffi: Box::new(ExternalDecl {
                    kind: DeclKind::DeclSend {
                        name: "then".to_string(),
                    },
                    module_: None,
                    scopes: vec![],
                    variadic: false,
                    effective_arity: 2,
                }),
                transformed_jsx: false,
            },
            vec![
                RawLambda::prim(
                    Primitive::Pimport(Box::new(ImportSource::ImportExternal {
                        module_: emn.clone(),
                        path: vec![],
                    })),
                    vec![],
                    self.lam_loc(loc),
                ),
                callback,
            ],
            self.lam_loc(loc),
        )
    }

    /// `Translcore.transl_dynamic_import`.
    fn transl_dynamic_import(&mut self, loc: SrcLoc, arg: &Expression) -> RawLambda {
        use crate::types::decl::PrimKind;
        use crate::types::external_ffi_types::{DeclKind, ExternalFfi, ModuleSource};
        if let ExpressionDesc::Texp_ident(_, _, desc) = &arg.exp_desc
            && let ValueKind::ValPrim(p) = &desc.val_kind
            && let PrimKind::KindExternal(spec) = &p.prim_kind
            && let ExternalFfi::FfiBs(arg_types, return_wrapper, decl) = spec.as_ref()
            && let DeclKind::DeclVal { name } = &decl.kind
            && let Some(ModuleSource::ModuleNamed(emn)) = &decl.module_
            && Self::external_import_needs_adaptation(arg_types, decl, *return_wrapper)
        {
            let env = self.env_for_expr(arg);
            let env = env.as_deref().unwrap_or(self.env);
            return self.transl_adapted_external_import(
                loc,
                env,
                emn,
                name,
                &decl.scopes,
                decl.variadic,
                arg_types,
                *return_wrapper,
                p,
                desc.val_type,
            );
        }
        match self.import_source_of_arg(arg) {
            Some(source) => RawLambda::prim(
                Primitive::Pimport(Box::new(source)),
                vec![],
                self.lam_loc(loc),
            ),
            None => RawLambda::unit(),
        }
    }

    /// translcore.ml `is_null_undefined_constant`: unit shares the
    /// undefined constant but is not a `%null` / `%undefined` literal.
    fn raw_lambda_is_nullish_constant(lam: &RawLambda) -> bool {
        matches!(
            lam,
            RawLambda::Lconst(Constant::JsNull | Constant::JsUndefined { is_unit: false })
        )
    }

    fn report_polymorphic_comparison_warning(
        &mut self,
        loc: LocIdx,
        primitive: &Primitive,
        args: &[RawLambda],
    ) {
        match primitive {
            Primitive::Pobjcomp(crate::lambda::Comparison::Eq)
            | Primitive::Pobjcomp(crate::lambda::Comparison::Neq)
                if matches!(args, [left, right] if Self::raw_lambda_is_nullish_constant(left) || Self::raw_lambda_is_nullish_constant(right)) =>
                {}
            Primitive::Pobjcomp(_)
            | Primitive::Pobjorder
            | Primitive::Pobjmin
            | Primitive::Pobjmax => {
                self.report_warning(loc, Warning::BsPolymorphicComparison);
            }
            _ => {}
        }
    }

    fn extract_constant_raw(lam: &RawLambda) -> Option<Constant> {
        match lam {
            RawLambda::Lconst(c) => Some(c.clone()),
            _ => None,
        }
    }

    fn raw_block_or_prim(
        &self,
        _tag: i32,
        tag_info: TagInfo,
        elems: Vec<RawLambda>,
        loc: impl Into<SrcLoc>,
    ) -> RawLambda {
        let loc: SrcLoc = loc.into();
        if let Some(constants) = elems
            .iter()
            .map(Self::extract_constant_raw)
            .collect::<Option<Vec<_>>>()
        {
            RawLambda::const_(Constant::Block {
                tag_info: Box::new(tag_info),
                elements: constants,
            })
        } else {
            RawLambda::prim(
                Primitive::Pmakeblock(tag_info, Mutable::Immutable),
                elems,
                self.lam_loc(loc),
            )
        }
    }

    fn raw_constructor_tag_info(
        &self,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
    ) -> TagInfo {
        match &cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(_) if constructor_has_optional_shape(cstr) => {
                match args {
                    [arg] => {
                        // translcore.ml:818-824: `type_cannot_contain_undefined
                        // arg.exp_type arg.exp_env`.
                        let can_skip =
                            self.type_ctx.get_typed_env(arg.exp_env).is_some_and(|env| {
                                type_cannot_contain_undefined(
                                    self.type_ctx,
                                    env.as_ref(),
                                    arg.exp_type,
                                )
                            });
                        if can_skip {
                            TagInfo::SomeNotNested
                        } else {
                            TagInfo::Some
                        }
                    }
                    _ => TagInfo::Some,
                }
            }
            _ => {
                let reference = match cstr.cstr_kind {
                    crate::types::ConstructorKind::Ordinary(reference) => reference,
                    crate::types::ConstructorKind::Extension(_) => unreachable!(),
                };
                let (runtime, num_nonconst) =
                    self.type_ctx
                        .with_variant_layout(reference.variant, |layout| {
                            let runtime = match &layout.constructors[reference.position] {
                                crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock::Tagged(runtime),
                                ) => runtime.clone(),
                                crate::types::VariantConstructorCase::Block(
                                    crate::types::VariantBlock::Untagged { .. },
                                ) => unreachable!("untagged constructors are erased"),
                                crate::types::VariantConstructorCase::Constant(_) => {
                                    unreachable!("payload constructor has constant layout")
                                }
                            };
                            (runtime, layout.num_blocks() as i32)
                        });
                TagInfo::Constructor {
                    name: cstr.cstr_name.clone(),
                    num_nonconst,
                    runtime: Box::new(runtime),
                }
            }
        }
    }

    fn convert_construct_raw(
        &mut self,
        loc: SrcLoc,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
    ) -> RawLambda {
        if cstr.cstr_inlined.is_some() {
            return match args {
                [arg] => match &arg.exp_desc {
                    ExpressionDesc::Texp_record {
                        fields,
                        extended_expression,
                        ..
                    } => self.convert_record_raw(
                        SrcLoc::from(arg.exp_loc),
                        fields,
                        extended_expression.as_deref(),
                        inlined_record_representation(cstr),
                        None,
                    ),
                    ExpressionDesc::Texp_record_sparse {
                        fields,
                        all_labels,
                        omitted_loc,
                        ..
                    } => {
                        // Debug/captured lambda keeps OCaml's full `lbl_all`
                        // stream; normal JS lowering can compact static
                        // omitted optional None before raw-lambda conversion.
                        let (record_fields, logical_field_count) =
                            self.sparse_record_fields_for_lambda(all_labels, fields, *omitted_loc);
                        self.convert_record_raw(
                            SrcLoc::from(arg.exp_loc),
                            &record_fields,
                            None,
                            inlined_record_representation(cstr),
                            logical_field_count,
                        )
                    }
                    _ => self.convert_expr_raw(arg),
                },
                [] => RawLambda::const_(raw_constructor_constant(self.type_ctx, cstr, 0)),
                _ => RawLambda::unit(),
            };
        }

        match cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(reference) => match reference
                .representation(self.type_ctx)
            {
                crate::types::VariantConstructorCase::Constant(_) => {
                    match cstr.cstr_name.as_str() {
                        "true" => RawLambda::const_(Constant::JsTrue),
                        "false" => RawLambda::const_(Constant::JsFalse),
                        _ => RawLambda::const_(raw_constructor_constant(
                            self.type_ctx,
                            cstr,
                            reference.position as i32,
                        )),
                    }
                }
                crate::types::VariantConstructorCase::Block(block)
                    if block.is_untagged()
                        && self
                            .type_ctx
                            .with_variant_layout(reference.variant, |layout| {
                                layout.constructors.len() == 1
                            }) =>
                {
                    match args {
                        [arg] => self.convert_expr_raw(arg),
                        [] => RawLambda::const_(raw_constructor_constant(self.type_ctx, cstr, 0)),
                        _ => RawLambda::unit(),
                    }
                }
                // translcore.ml Texp_construct: untagged payload constructors
                // have no Lambda or JS block.
                crate::types::VariantConstructorCase::Block(block)
                    if block.is_untagged() && !constructor_has_optional_shape(cstr) =>
                {
                    match args {
                        [arg] => self.convert_expr_raw(arg),
                        _ => unreachable!(
                            "untagged constructor arity is checked by the type checker"
                        ),
                    }
                }
                crate::types::VariantConstructorCase::Block(_) => {
                    let elems = args.iter().map(|arg| self.convert_expr_raw(arg)).collect();
                    let tag_info = self.raw_constructor_tag_info(cstr, args);
                    self.raw_block_or_prim(
                        reference.block_index(self.type_ctx) as i32,
                        tag_info,
                        elems,
                        loc,
                    )
                }
            },
            crate::types::ConstructorKind::Extension(ref path) => {
                let mut args_lam = Vec::with_capacity(args.len() + 1);
                args_lam.push(self.translate_extension_path_raw(path, loc));
                args_lam.extend(args.iter().map(|arg| self.convert_expr_raw(arg)));
                RawLambda::prim(
                    Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
                    args_lam,
                    self.lam_loc(loc),
                )
            }
        }
    }

    fn convert_record_raw(
        &mut self,
        loc: SrcLoc,
        fields: &[(
            Located<LidentIdx>,
            LabelDescription,
            RecordLabelDefinition,
            bool,
        )],
        base: Option<&Expression>,
        empty_repres: Option<RecordRepresentation>,
        logical_field_count: Option<usize>,
    ) -> RawLambda {
        let first_lbl = fields.first().map(|(_, first_lbl, _, _)| first_lbl);
        let repres = first_lbl
            .map(|lbl| lbl.lbl_repres.clone())
            .or(empty_repres)
            .unwrap_or(RecordRepresentation::RecordRegular);
        let mutable_flag = raw_record_mutable_flag(fields);
        let base_lam = base.map(|expr| self.convert_expr_raw(expr));
        let has_optional = fields.iter().any(|(_, lbl, _, _)| lbl.lbl_optional);
        // OCaml uses field-by-field construction when:
        // - no base expression, OR
        // - all fields are overridden (no Kept), OR
        // - size < 20 AND no optional fields (OCaml's transl_record line 1130)
        let build_direct = base.is_none()
            || fields.iter().all(|(_, _, def, _)| {
                matches!(
                    def,
                    RecordLabelDefinition::Overridden(_, _)
                        | RecordLabelDefinition::OmittedOptionalNone(_, _)
                )
            })
            || (fields.len() < 20 && !has_optional);

        if build_direct {
            // OCaml allocates init_id before inspecting opt_init_expr, even
            // for a record literal with no base (translcore.ml:1087-1114).
            // The binder is emitted only when a base exists, but its allocation
            // still orders later Translcore/Translmod identifiers.
            let init_id = self.fresh_ident("init");
            let init_var = base_lam.as_ref().map(|_| RawLambda::var(init_id));

            let mut elems = Vec::with_capacity(fields.len());
            let mut fields_info = Vec::with_capacity(fields.len());
            for (lid, lbl, def, _) in fields {
                // OCaml compiler/ml/translcore.ml:1139-1191 maps every record
                // field in `fields`, including omitted optional fields that
                // typecore.ml:2833-2842 materialized as `option_none`. Keep the
                // full Lambda block shape here; JS output can still erase
                // optional `undefined` fields during JS lowering.
                let value = match def {
                    RecordLabelDefinition::Overridden(_, expr) => self.convert_expr_raw(expr),
                    RecordLabelDefinition::OmittedOptionalNone(_, _) => raw_optional_none(),
                    RecordLabelDefinition::Kept(_) => {
                        let Some(base_var) = &init_var else {
                            elems.push(RawLambda::unit());
                            fields_info.push((label_runtime_name(lbl), lbl.lbl_optional));
                            continue;
                        };
                        if matches!(lbl.lbl_repres, RecordRepresentation::RecordUnboxed(_)) {
                            base_var.clone()
                        } else if let Some((pos, info)) = raw_record_field_access(lbl) {
                            RawLambda::prim(
                                Primitive::Pfield(pos, info),
                                vec![base_var.clone()],
                                self.lam_loc(lid.loc),
                            )
                        } else {
                            RawLambda::unit()
                        }
                    }
                };
                elems.push(value);
                fields_info.push((label_runtime_name(lbl), lbl.lbl_optional));
            }

            let result = match repres {
                RecordRepresentation::RecordRegular => {
                    // OCaml: if mut = Mutable then raise Not_constant
                    // Mutable records never become constant blocks
                    if matches!(mutable_flag, ParserMutableFlag::Mutable) {
                        RawLambda::prim(
                            Primitive::Pmakeblock(
                                TagInfo::Record {
                                    fields: fields_info,
                                    logical_field_count,
                                    mutable_flag,
                                },
                                Mutable::Mutable,
                            ),
                            elems,
                            self.lam_loc(loc),
                        )
                    } else {
                        self.raw_block_or_prim(
                            0,
                            TagInfo::Record {
                                fields: fields_info,
                                logical_field_count,
                                mutable_flag,
                            },
                            elems,
                            loc,
                        )
                    }
                }
                RecordRepresentation::RecordFloatUnused => RawLambda::unit(),
                RecordRepresentation::RecordUnboxed(_) => match elems.as_slice() {
                    [value] => value.clone(),
                    _ => RawLambda::unit(),
                },
                RecordRepresentation::RecordInlined {
                    name,
                    representation,
                } => {
                    let crate::types::VariantConstructorCase::Block(block) =
                        representation.representation(self.type_ctx)
                    else {
                        unreachable!("inlined record must reference a block constructor")
                    };
                    let tag = representation.block_index(self.type_ctx) as i32;
                    let tag_info = TagInfo::RecordInlined {
                        name,
                        num_nonconst: representation.num_blocks(self.type_ctx) as i32,
                        fields: fields_info,
                        logical_field_count,
                        mutable_flag,
                        runtime: Box::new(block),
                    };
                    // OCaml: if mut = Mutable then raise Not_constant
                    if matches!(mutable_flag, ParserMutableFlag::Mutable) {
                        RawLambda::prim(
                            Primitive::Pmakeblock(tag_info, Mutable::Mutable),
                            elems,
                            self.lam_loc(loc),
                        )
                    } else {
                        self.raw_block_or_prim(tag, tag_info, elems, loc)
                    }
                }
                RecordRepresentation::RecordExtension => {
                    let Some(first_lbl) = first_lbl else {
                        return RawLambda::unit();
                    };
                    let path = match self.type_desc(first_lbl.lbl_res) {
                        TypeDesc::Tconstr { path, .. } => path,
                        _ => return RawLambda::unit(),
                    };
                    let mut args = Vec::with_capacity(elems.len() + 1);
                    args.push(self.translate_extension_path_raw(&path, loc));
                    args.extend(elems);
                    RawLambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::RecordExt {
                                fields: fields
                                    .iter()
                                    .map(|(_, lbl, _, _)| label_runtime_name(lbl))
                                    .collect(),
                                mutable_flag,
                            },
                            if matches!(mutable_flag, ParserMutableFlag::Mutable) {
                                Mutable::Mutable
                            } else {
                                Mutable::Immutable
                            },
                        ),
                        args,
                        self.lam_loc(loc),
                    )
                }
            };
            // Wrap with let init = base_expr when there's a base expression
            return match base_lam {
                Some(base_expr) => RawLambda::let_(LetKind::Strict, init_id, base_expr, result),
                None => result,
            };
        }

        let Some(init_expr) = base_lam else {
            return RawLambda::unit();
        };

        let copy_id = self.fresh_ident("newrecord");
        let mut body = RawLambda::var(copy_id);
        // OCaml uses Array.fold_left which processes fields left-to-right.
        // Each Lsequence(upd, cont) wraps the update around the continuation,
        // so the LAST field ends up outermost in the sequence chain.
        for (_, lbl, def, _) in fields.iter() {
            let expr = match def {
                RecordLabelDefinition::Overridden(_, expr) => expr,
                RecordLabelDefinition::Kept(_)
                | RecordLabelDefinition::OmittedOptionalNone(_, _) => {
                    continue;
                }
            };
            let Some((pos, info)) = raw_record_setfield_access(lbl) else {
                continue;
            };
            let update = RawLambda::prim(
                Primitive::Psetfield(pos, info),
                vec![RawLambda::var(copy_id), self.convert_expr_raw(expr)],
                self.lam_loc(loc),
            );
            body = RawLambda::seq(update, body);
        }

        RawLambda::let_(
            LetKind::Strict,
            copy_id,
            RawLambda::prim(Primitive::Pduprecord, vec![init_expr], self.lam_loc(loc)),
            body,
        )
    }

    fn expand_sparse_record_fields(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &[RecordField],
        omitted_loc: LocIdx,
    ) -> Vec<RecordField> {
        // OCaml compiler/ml/typecore.ml:2833-2842 stores one definition per
        // `lbl_all` entry, then compiler/ml/translcore.ml:1139-1191 lowers
        // that whole array into the Lambda block. Rust's sparse typedtree node
        // is an internal storage optimization, so expand it before Lambda.
        let placeholder_lid = fields
            .first()
            .map(|(lid, _, _, _)| *lid)
            .unwrap_or_else(|| self.arena.placeholder_located(omitted_loc));
        let mut explicit_by_pos: HashMap<usize, &RecordField> =
            HashMap::with_capacity(fields.len());
        for field in fields.iter() {
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
                    label_lid,
                    label.clone(),
                    RecordLabelDefinition::OmittedOptionalNone(label_lid, label.lbl_arg),
                    false,
                ));
            } else {
                // Sparse records are only created after typecore has verified
                // all mandatory labels are present. If a malformed node reaches
                // lambda lowering, keep a unit placeholder rather than changing
                // field order; this mirrors the fallback value OCaml would have
                // placed in the full record array before translcore.ml:1145-1162
                // mapped every slot.
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

    fn compact_sparse_record_fields_for_output<'b>(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &'b [RecordField],
    ) -> Cow<'b, [RecordField]> {
        // If every selected label has a materialized slot, sorting by `lbl_pos`
        // preserves OCaml `lbl_all` field order without walking omitted fields.
        if fields.iter().all(|field| field.1.lbl_pos >= 0) {
            let already_ordered = fields
                .windows(2)
                .all(|pair| pair[0].1.lbl_pos <= pair[1].1.lbl_pos);
            let has_static_optional_none = fields
                .iter()
                .any(|field| record_field_is_static_optional_none(&field.1, &field.2));
            if already_ordered && !has_static_optional_none {
                return Cow::Borrowed(fields);
            }
            let mut compact = fields
                .iter()
                .filter(|field| !record_field_is_static_optional_none(&field.1, &field.2))
                .cloned()
                .collect::<Vec<_>>();
            if !already_ordered {
                compact.sort_by_key(|field| field.1.lbl_pos);
            }
            return Cow::Owned(compact);
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
        Cow::Owned(compact)
    }

    fn sparse_record_fields_for_lambda<'b>(
        &self,
        all_labels: &std::sync::Arc<Vec<LabelDescription>>,
        fields: &'b [RecordField],
        omitted_loc: LocIdx,
    ) -> (Cow<'b, [RecordField]>, Option<usize>) {
        if self.preserve_expanded_sparse_records {
            (
                Cow::Owned(self.expand_sparse_record_fields(all_labels, fields, omitted_loc)),
                None,
            )
        } else {
            (
                self.compact_sparse_record_fields_for_output(all_labels, fields),
                Some(all_labels.len()),
            )
        }
    }

    fn include_bound_idents(sig: &[SignatureItem]) -> Vec<(Ident, usize)> {
        crate::types::decl::signature_runtime_bound_idents(sig)
    }

    fn rebind_included_idents_raw(
        &self,
        mid: &Ident,
        ids: &[(Ident, usize)],
        body: RawLambda,
        loc: LocIdx,
    ) -> RawLambda {
        ids.iter().rev().fold(body, |acc, (id, pos)| {
            RawLambda::let_(
                LetKind::Alias,
                *id,
                RawLambda::prim(
                    Primitive::Pfield(
                        *pos as i32,
                        FieldDbgInfo::Module {
                            name: id.name().to_string(),
                        },
                    ),
                    vec![RawLambda::var(*mid)],
                    self.lam_loc(loc),
                ),
                acc,
            )
        })
    }

    fn materialize_hoisted_exports(&mut self, lam: RawLambda) -> RawLambda {
        fn collect_groups(lam: &RawLambda, groups: &mut HashMap<Ident, RawLambda>) {
            match lam {
                RawLambda::Llet(_, id, value, body) => {
                    groups.insert(*id, (**value).clone());
                    collect_groups(value, groups);
                    collect_groups(body, groups);
                }
                RawLambda::Lletrec(bindings, body) => {
                    groups.extend(bindings.iter().cloned());
                    for (_, value) in bindings {
                        collect_groups(value, groups);
                    }
                    collect_groups(body, groups);
                }
                RawLambda::Lsequence(left, body) => {
                    collect_groups(left, groups);
                    collect_groups(body, groups);
                }
                _ => {}
            }
        }
        fn terminal_exports(lam: &RawLambda) -> Vec<Ident> {
            match lam {
                RawLambda::Llet(_, _, _, body) | RawLambda::Lletrec(_, body) => {
                    terminal_exports(body)
                }
                RawLambda::Lsequence(_, body) => terminal_exports(body),
                RawLambda::Lprim(__prim1)
                    if matches!(
                        __prim1.as_ref(),
                        RawPrimInfo {
                            primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(_ids), _),
                            ..
                        }
                    ) =>
                {
                    let RawPrimInfo {
                        primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _),
                        ..
                    } = __prim1.as_ref()
                    else {
                        unreachable!()
                    };
                    ids.clone()
                }
                _ => Vec::new(),
            }
        }
        fn resolve_binding(
            lam: &RawLambda,
            groups: &HashMap<Ident, RawLambda>,
            seen: &mut HashSet<Ident>,
        ) -> (RawLambda, Option<Ident>) {
            match lam {
                RawLambda::Lvar(id) => {
                    if !seen.insert(*id) {
                        return (lam.clone(), Some(*id));
                    }
                    match groups.get(id) {
                        Some(alias @ (RawLambda::Lvar(_) | RawLambda::Lprim(_))) => {
                            resolve_binding(alias, groups, seen)
                        }
                        Some(resolved) => (resolved.clone(), Some(*id)),
                        None => (lam.clone(), Some(*id)),
                    }
                }
                RawLambda::Lprim(__prim0)
                    if matches!(__prim0.as_ref(), RawPrimInfo {
                    primitive: Primitive::Pfield(pos, _),
                    args,
                    ..
                } if args.len() == 1) =>
                {
                    let RawPrimInfo {
                        primitive: Primitive::Pfield(pos, _),
                        args,
                        ..
                    } = __prim0.as_ref()
                    else {
                        unreachable!()
                    };

                    let (base, _) = resolve_binding(&args[0], groups, seen);
                    if let RawLambda::Lprim(__prim201) = base
                        && let RawPrimInfo {
                            primitive: Primitive::Pmakeblock(TagInfo::Module(_), _),
                            args,
                            ..
                        } = __prim201.as_ref()
                    {
                        if let Some(field) =
                            usize::try_from(*pos).ok().and_then(|pos| args.get(pos))
                        {
                            return resolve_binding(field, groups, seen);
                        }
                    }
                    (lam.clone(), None)
                }
                _ => (lam.clone(), None),
            }
        }
        fn find_path(
            lam: &RawLambda,
            fields: &[String],
            groups: &HashMap<Ident, RawLambda>,
            positions: &mut Vec<(i32, String)>,
        ) -> Option<(Option<Ident>, RawLambda)> {
            if fields.is_empty() {
                let (target, id) = resolve_binding(lam, groups, &mut HashSet::new());
                return Some((id, target));
            }
            let (mut resolved, _) = resolve_binding(lam, groups, &mut HashSet::new());
            resolved = loop {
                match resolved {
                    RawLambda::Llet(_, _, _, body)
                    | RawLambda::Lletrec(_, body)
                    | RawLambda::Lsequence(_, body) => resolved = *body,
                    other => break other,
                }
            };
            let RawLambda::Lprim(__prim200) = resolved else {
                return None;
            };
            let RawPrimInfo {
                primitive: Primitive::Pmakeblock(TagInfo::Module(names), _),
                args,
                ..
            } = __prim200.as_ref()
            else {
                return None;
            };
            let pos = names.iter().position(|name| name == &fields[0])?;
            let arg = args.get(pos)?;
            positions.push((pos as i32, fields[0].clone()));
            find_path(arg, &fields[1..], groups, positions)
        }
        fn unwrap_exotic(name: &str) -> &str {
            if name.len() >= 3 && name.starts_with("\\\"") && name.ends_with('"') {
                &name[2..name.len() - 1]
            } else {
                name
            }
        }
        if self.hoisted_functions.is_empty() {
            return lam;
        }
        let mut groups = HashMap::new();
        collect_groups(&lam, &mut groups);
        let exported_modules = terminal_exports(&lam)
            .into_iter()
            .map(|id| (id.name().to_string(), id))
            .collect::<HashMap<_, _>>();
        let mut occupied = groups
            .keys()
            .map(|id| crate::js_ir::printer::convert_ident_name(id.name()))
            .collect::<HashSet<_>>();
        let mut validated = Vec::new();
        let hoisted_functions = self.hoisted_functions.clone();
        for hoisted in hoisted_functions {
            let Some((top, fields)) = hoisted.path.split_first() else {
                continue;
            };
            let resolved = exported_modules.get(top).and_then(|top_id| {
                let module = groups.get(top_id)?;
                let mut positions = Vec::new();
                let (target_id, _target) = find_path(module, fields, &groups, &mut positions)?;
                Some((*top_id, positions, target_id))
            });
            let Some((_top_id, _positions, Some(target_id))) = resolved else {
                self.report_warning(
                    self.loc_idx_for_lam_loc(hoisted.loc),
                    Warning::MisplacedAttribute {
                        name: "res.hoistedFunction".to_string(),
                    },
                );
                continue;
            };
            if !hoisted.binding.same(&target_id) {
                self.report_warning(
                    self.loc_idx_for_lam_loc(hoisted.loc),
                    Warning::MisplacedAttribute {
                        name: "res.hoistedFunction".to_string(),
                    },
                );
                continue;
            }
            let export_name = hoisted
                .path
                .iter()
                .map(|part| unwrap_exotic(part))
                .collect::<Vec<_>>()
                .join("$");
            let js_name = crate::js_ir::printer::convert_ident_name(&export_name);
            if occupied.contains(&js_name) {
                self.report_diagnostic(
                    self.lam_locs.get(hoisted.target_loc).unwrap_or_else(Location::none),
                    format!(
                        "Cannot hoist this function as `{export_name}` because that name is already used by a top-level binding."
                    ),
                );
                continue;
            }
            occupied.insert(js_name);
            self.hoisted_exports.push(crate::lambda::HoistedExport {
                path: hoisted.path.clone(),
                export_name,
            });
            validated.push(hoisted);
        }
        self.hoisted_functions = validated;
        lam
    }

    /// Convert a structure into raw lambda.
    pub fn convert_structure(&mut self, structure: &Structure) -> RawLambda {
        self.convert_structure_with_coercion(structure, &ModuleCoercion::Tcoerce_none)
    }

    pub fn convert_structure_with_coercion(
        &mut self,
        structure: &Structure,
        cc: &ModuleCoercion,
    ) -> RawLambda {
        if structure_has_config_string(structure, "-bs-noassertfalse", self.arena) {
            self.no_assert_false = true;
        }
        self.register_signature_type_paths(None, &structure.str_type);
        // The typed tree is complete: repeated type queries on it have one
        // answer per (env, type).
        self.type_ctx.set_typeopt_cache(true);
        let mut fields = Vec::new();
        let result = self.convert_structure_items_raw(
            &mut fields,
            &structure.str_items,
            true,
            &self.global_path(),
            cc,
            SrcLoc::Decl(Location::none()),
        );
        self.type_ctx.set_typeopt_cache(false);
        self.materialize_hoisted_exports(result)
    }

    fn pure_module(module_expr: &ModuleExpr) -> LetKind {
        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_ident(_, _) => LetKind::Alias,
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => Self::pure_module(inner),
            _ => LetKind::Strict,
        }
    }

    fn name_lambda_raw<F>(&mut self, strict: LetKind, arg: RawLambda, f: F) -> RawLambda
    where
        F: FnOnce(&mut Self, Ident) -> RawLambda,
    {
        match arg {
            RawLambda::Lvar(id) => f(self, id),
            _ => {
                let id = self.fresh_ident("let");
                let body = f(self, id);
                RawLambda::let_(strict, id, arg, body)
            }
        }
    }

    fn rescript_hide_attributes(&self, attrs: &crate::parser::ast::Attributes) -> bool {
        attrs
            .iter()
            .any(|(name, _)| self.arena.get_string(name.txt) == "internal.local")
    }

    fn translate_normal_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: SrcLoc,
    ) -> RawLambda {
        match path.view() {
            crate::types::path::PathView::Pident(id) => {
                if id.is_global() {
                    RawLambda::global_module(*id)
                } else {
                    RawLambda::var(*id)
                }
            }
            crate::types::path::PathView::Pdot(prefix, name, pos) => {
                let prefix_lam = self.translate_normal_path_raw_in_env(env, prefix, loc);
                // OCaml compiler/ml/lambda.ml:635-643 preserves the Pdot
                // runtime position while translating paths. If Rust path
                // normalization produced a synthetic -1, recover the same
                // position from the module signature before emitting Pfield.
                let resolved_pos = if *pos < 0 {
                    self.resolve_field_position_in_module(env, prefix, name)
                        .unwrap_or(*pos)
                } else {
                    *pos
                };
                RawLambda::prim(
                    Primitive::Pfield(
                        resolved_pos,
                        FieldDbgInfo::Module {
                            name: name.to_string(),
                        },
                    ),
                    vec![prefix_lam],
                    self.lam_loc(loc),
                )
            }
            crate::types::path::PathView::Papply(_, _) => RawLambda::unit(),
        }
    }

    /// Resolve the runtime field position of a name within a module's signature.
    fn resolve_field_position_in_module(
        &mut self,
        env: &crate::types::env::Env,
        module_path: &crate::types::Path,
        field_name: &str,
    ) -> Option<i32> {
        use crate::types::decl::{ModuleType, SignatureItem, ValueKind};

        fn runtime_field_position(sig: &[SignatureItem], field_name: &str) -> Option<i32> {
            let mut runtime_pos = 0i32;
            for item in sig {
                match item {
                    SignatureItem::SigValue(id, desc)
                        if !matches!(desc.val_kind, ValueKind::ValPrim(_)) =>
                    {
                        if id.name() == field_name {
                            return Some(runtime_pos);
                        }
                        runtime_pos += 1;
                    }
                    SignatureItem::SigModule(id, _, _) | SignatureItem::SigTypext(id, _, _) => {
                        if id.name() == field_name {
                            return Some(runtime_pos);
                        }
                        runtime_pos += 1;
                    }
                    SignatureItem::SigValue(_, _) => {}
                    _ => {}
                }
            }
            None
        }

        if let Some(pos) = crate::types::typecore::with_resolved_module_components_for_path(
            module_path,
            env,
            &mut self.persistent_env,
            self.type_ctx,
            |components| runtime_field_position(components.signature(), field_name),
        )
        .flatten()
        {
            return Some(pos);
        }

        fn module_type_for_path(
            this: &mut RawLambdaConverter<'_>,
            env: &crate::types::env::Env,
            module_path: &crate::types::Path,
        ) -> Option<ModuleType> {
            fn submodule_type_from_module_type(
                this: &mut RawLambdaConverter<'_>,
                env: &crate::types::env::Env,
                module_path: &crate::types::Path,
                mty: ModuleType,
                name: &str,
                depth: usize,
            ) -> Option<ModuleType> {
                if depth > 10 {
                    return None;
                }
                match mty {
                    ModuleType::MtySignature(sig) => std::sync::Arc::unwrap_or_clone(sig)
                        .into_iter()
                        .find_map(|item| match item {
                            SignatureItem::SigModule(id, md, _) if id.name() == name => {
                                Some(md.md_type)
                            }
                            _ => None,
                        }),
                    ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                        if alias_path.same(module_path) {
                            return None;
                        }
                        let alias_mty = module_type_for_path(this, env, &alias_path)?;
                        submodule_type_from_module_type(
                            this,
                            env,
                            &alias_path,
                            alias_mty,
                            name,
                            depth + 1,
                        )
                    }
                    ModuleType::MtyFunctor { .. } => None,
                }
            }

            env.lookup_module(module_path)
                .ok()
                .map(|md| md.md_type.clone())
                .or_else(|| {
                    if let crate::types::path::PathView::Pdot(prefix, name, _) = module_path.view()
                    {
                        // OCaml compiler/ml/env.ml:903-913 normalizes dotted
                        // paths through find_module; recover the same nested
                        // module type from the parent signature when this env
                        // has not stored the dotted path as a direct binding.
                        let parent_mty = module_type_for_path(this, env, prefix)?;
                        return submodule_type_from_module_type(
                            this, env, prefix, parent_mty, name, 0,
                        );
                    }
                    if let crate::types::path::PathView::Pident(id) = module_path.view()
                        && (id.is_persistent() || id.is_global())
                    {
                        let sig = this
                            .persistent_env
                            .as_mut()?
                            .read_raw_sig(id.name(), this.type_ctx)?;
                        Some(ModuleType::MtySignature(std::sync::Arc::new(sig)))
                    } else {
                        None
                    }
                })
        }

        fn resolve_runtime_field_position(
            this: &mut RawLambdaConverter<'_>,
            env: &crate::types::env::Env,
            module_path: &crate::types::Path,
            mty: ModuleType,
            field_name: &str,
            depth: usize,
        ) -> Option<i32> {
            if depth > 10 {
                return None;
            }

            match mty {
                ModuleType::MtySignature(sig) => runtime_field_position(&sig, field_name),
                ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                    if alias_path.same(module_path) {
                        return None;
                    }
                    let alias_mty = module_type_for_path(this, env, &alias_path)?;
                    resolve_runtime_field_position(
                        this,
                        env,
                        &alias_path,
                        alias_mty,
                        field_name,
                        depth + 1,
                    )
                }
                ModuleType::MtyFunctor { .. } => None,
            }
        }

        let md_type = module_type_for_path(self, env, module_path)?;
        resolve_runtime_field_position(self, env, module_path, md_type, field_name, 0)
    }

    fn path_may_follow_mty_ident(path: &crate::types::Path) -> bool {
        // OCaml `Path.head` asserts on functor applications, while
        // `Path.flatten` reports `Contains_apply` (compiler/ml/path.ml:58-69).
        // Alias following here is only valid for paths with a stable head.
        let Ok((head, _)) = path.flatten() else {
            return false;
        };
        head.is_persistent() || head.is_global()
    }

    fn module_path_resolves_to_runtime_module(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> bool {
        if env.lookup_module(path).is_ok() {
            return true;
        }

        match path.view() {
            crate::types::path::PathView::Pident(id) if id.is_persistent() || id.is_global() => {
                self.persistent_env
                    .as_mut()
                    .and_then(|pers| pers.find_pers_struct(id.name(), self.type_ctx))
                    .is_some()
            }
            _ => false,
        }
    }

    fn module_declaration_for_path_normalization<'e>(
        env: &'e crate::types::env::Env,
        path: &crate::types::Path,
    ) -> Option<&'e crate::types::decl::ModuleDeclaration> {
        match path.view() {
            // OCaml Env.find_module resolves Pident through IdTbl.find_same
            // (compiler/ml/env.ml:865-875). Do not let an opened same-name
            // component answer for an already-selected persistent root.
            crate::types::path::PathView::Pident(id) => env.find_module_same(id).ok(),
            crate::types::path::PathView::Pdot(..) => env.lookup_module(path).ok(),
            crate::types::path::PathView::Papply(..) => None,
        }
    }

    fn force_qualified_module_for_normalization(
        &mut self,
        env: &crate::types::env::Env,
        parent: &crate::types::Path,
        name: &str,
    ) -> Option<crate::types::decl::ModuleDeclaration> {
        // OCaml has one global Ident counter. Component forcing can run
        // Subst.modtype while raw translation is already allocating binders,
        // so keep the Rust converter and type-context generators in lockstep
        // across the Env.find_module force boundary.
        self.sync_local_stamp_generators();
        let result = crate::types::typecore::lookup_module_in_resolved_path(
            parent,
            name,
            env,
            &mut self.persistent_env,
            self.type_ctx,
        )
        .map(|(_, _, md)| md);
        self.sync_local_stamp_generators();
        result
    }

    /// `Env.normalize_path` (env.ml:903-914) as used by `transl_module_path`.
    fn normalize_module_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        self.normalize_module_path_with_root_force(env, path, true)
    }

    /// The same alias resolution for Rust-side bookkeeping that has no
    /// OCaml counterpart (required-module notes): it must not force a
    /// persistent root's `ps_sig`, which only `Env.normalize_path` does.
    fn resolve_module_path_aliases(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        self.normalize_module_path_with_root_force(env, path, false)
    }

    fn normalize_module_path_with_root_force(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        force_root: bool,
    ) -> crate::types::Path {
        let path = match path.view() {
            crate::types::path::PathView::Pdot(prefix, name, pos) => crate::types::Path::pdot_pos(
                self.normalize_module_path_with_root_force(env, prefix, force_root),
                *name,
                *pos,
            ),
            crate::types::path::PathView::Papply(left, right) => crate::types::Path::papply(
                self.normalize_module_path_with_root_force(env, left, force_root),
                self.normalize_module_path_with_root_force(env, right, force_root),
            ),
            crate::types::path::PathView::Pident(id) => {
                if force_root {
                    self.force_persistent_normalized_prefix(env, id);
                }
                path.clone()
            }
        };

        if let crate::types::path::PathView::Pdot(parent, name, _) = path.view()
            && let Some(md) = self.force_qualified_module_for_normalization(env, parent, name)
            && let crate::types::decl::ModuleType::MtyAlias(_, alias_target) = &md.md_type
            && !alias_target.same(&path)
        {
            return self.normalize_module_path_with_root_force(env, alias_target, force_root);
        }

        if matches!(path.view(), crate::types::path::PathView::Pdot(..))
            && let Some(alias_target) = crate::types::typecore::module_alias_target_for_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            )
            && !alias_target.same(&path)
        {
            // OCaml compiler/ml/env.ml:876-880 resolves dotted modules through
            // `find_module_descr` component tables before following the alias
            // at compiler/ml/env.ml:903-914. A direct Rust env lookup can still
            // see the un-prefixed local alias stored in the source signature.
            return self.normalize_module_path_with_root_force(env, &alias_target, force_root);
        }

        if let Some(md) = Self::module_declaration_for_path_normalization(env, &path) {
            match &md.md_type {
                crate::types::decl::ModuleType::MtyAlias(_, alias_path) => {
                    if !alias_path.same(&path) {
                        return self
                            .normalize_module_path_with_root_force(env, alias_path, force_root);
                    }
                }
                crate::types::decl::ModuleType::MtyIdent(alias_path)
                    if Self::path_may_follow_mty_ident(&path)
                        && !alias_path.same(&path)
                        && self.module_path_resolves_to_runtime_module(env, alias_path) =>
                {
                    return self.normalize_module_path_with_root_force(env, alias_path, force_root);
                }
                _ => {}
            }
        }

        if matches!(path.view(), crate::types::path::PathView::Pdot(..))
            || Self::path_may_follow_mty_ident(&path)
        {
            if let Some(alias_target) = crate::types::typecore::module_alias_target_for_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            ) {
                if !alias_target.same(&path) {
                    // OCaml `transl_module_path` calls `Env.normalize_path`
                    // (compiler/ml/lambda.ml:648-649), whose Pdot case delegates
                    // to `find_module ~alias:true` (compiler/ml/env.ml:876-880)
                    // before following `Mty_alias` (compiler/ml/env.ml:903-914).
                    return self.normalize_module_path_with_root_force(
                        env,
                        &alias_target,
                        force_root,
                    );
                }
            }
        }

        if Self::path_may_follow_mty_ident(&path) {
            if let Some(alias_target) = crate::types::typecore::alias_target_for_module_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            ) {
                if !alias_target.same(&path)
                    && self.module_path_resolves_to_runtime_module(env, &alias_target)
                {
                    return self.normalize_module_path_with_root_force(
                        env,
                        &alias_target,
                        force_root,
                    );
                }
            }
        }
        path
    }

    fn force_persistent_normalized_prefix(&mut self, env: &crate::types::env::Env, id: &Ident) {
        // Env.normalize_path's Pident branch calls find_module ~alias:true.
        // When the identifier is not a local module binding, OCaml's
        // persistent branch forces ps_sig and its Subst.signature freshening
        // (env.ml:865-875, subst.ml:358-364).
        if (id.is_persistent() || id.is_global())
            && env.find_module(id.name()).is_err()
            && let Some(pers) = self.persistent_env.as_mut()
        {
            let _ = pers.force_lazy_signature_rename(id.name(), self.type_ctx);
            self.sync_local_stamp_generators();
        }
    }

    fn normalize_value_prefix_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        let path = match path.view() {
            crate::types::path::PathView::Pdot(prefix, name, pos) => crate::types::Path::pdot_pos(
                self.normalize_value_prefix_path_in_env(env, prefix),
                *name,
                *pos,
            ),
            crate::types::path::PathView::Papply(left, right) => crate::types::Path::papply(
                self.normalize_value_prefix_path_in_env(env, left),
                self.normalize_value_prefix_path_in_env(env, right),
            ),
            crate::types::path::PathView::Pident(id) => {
                self.force_persistent_normalized_prefix(env, id);
                path.clone()
            }
        };

        if let crate::types::path::PathView::Pdot(parent, name, _) = path.view()
            && let Some(md) = self.force_qualified_module_for_normalization(env, parent, name)
            && let crate::types::decl::ModuleType::MtyAlias(_, alias_target) = &md.md_type
            && !alias_target.same(&path)
        {
            return self.normalize_value_prefix_path_in_env(env, alias_target);
        }

        if matches!(path.view(), crate::types::path::PathView::Pdot(..))
            && let Some(alias_target) = crate::types::typecore::module_alias_target_for_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            )
            && !alias_target.same(&path)
        {
            // OCaml compiler/ml/lambda.ml:651-652 calls
            // `Env.normalize_path_prefix`; for a dotted prefix that reaches
            // compiler/ml/env.ml:876-880's component lookup before alias
            // following at compiler/ml/env.ml:903-914.
            return self.normalize_value_prefix_path_in_env(env, &alias_target);
        }

        if let Some(md) = Self::module_declaration_for_path_normalization(env, &path) {
            match &md.md_type {
                crate::types::decl::ModuleType::MtyAlias(_, alias_path) => {
                    if !alias_path.same(&path) {
                        return self.normalize_value_prefix_path_in_env(env, alias_path);
                    }
                }
                crate::types::decl::ModuleType::MtyIdent(alias_path)
                    if Self::path_may_follow_mty_ident(&path)
                        && !alias_path.same(&path)
                        && self.module_path_resolves_to_runtime_module(env, alias_path) =>
                {
                    return self.normalize_value_prefix_path_in_env(env, alias_path);
                }
                _ => {}
            }
        }

        if matches!(path.view(), crate::types::path::PathView::Pdot(..))
            || Self::path_may_follow_mty_ident(&path)
        {
            if let Some(alias_target) = crate::types::typecore::module_alias_target_for_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            ) {
                if !alias_target.same(&path) {
                    // OCaml `transl_value_path` normalizes only the value prefix
                    // (compiler/ml/lambda.ml:651-652); `normalize_path_prefix`
                    // calls `normalize_path` on that prefix
                    // (compiler/ml/env.ml:933-935), and `normalize_path` follows
                    // `Mty_alias` via `find_module ~alias:true`
                    // (compiler/ml/env.ml:903-914).
                    return self.normalize_value_prefix_path_in_env(env, &alias_target);
                }
            }
        }

        if Self::path_may_follow_mty_ident(&path) {
            if let Some(alias_target) = crate::types::typecore::alias_target_for_module_path(
                &path,
                env,
                &mut self.persistent_env,
                self.type_ctx,
            ) {
                if !alias_target.same(&path)
                    && self.module_path_resolves_to_runtime_module(env, &alias_target)
                {
                    return self.normalize_value_prefix_path_in_env(env, &alias_target);
                }
            }
        }

        path
    }

    fn normalize_value_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        match path.view() {
            crate::types::path::PathView::Pdot(prefix, name, pos) => crate::types::Path::pdot_pos(
                self.normalize_value_prefix_path_in_env(env, prefix),
                *name,
                *pos,
            ),
            crate::types::path::PathView::Pident(_) => path.clone(),
            crate::types::path::PathView::Papply(_, _) => path.clone(),
        }
    }

    fn translate_module_path_raw(&mut self, path: &crate::types::Path, loc: SrcLoc) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(self.env, path);
        self.translate_normal_path_raw_in_env(self.env, &normalized, loc)
    }

    fn translate_module_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: SrcLoc,
    ) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(env, path);
        self.translate_normal_path_raw_in_env(env, &normalized, loc)
    }

    fn translate_value_path_raw(&mut self, path: &crate::types::Path, loc: SrcLoc) -> RawLambda {
        if let Some(lam) = self.value_path_loc_constant(path, loc) {
            return lam;
        }
        let normalized = self.normalize_value_path_in_env(self.env, path);
        if let Some(lam) = self.value_path_loc_constant(&normalized, loc) {
            return lam;
        }
        self.translate_normal_path_raw_in_env(self.env, &normalized, loc)
    }

    fn translate_value_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: SrcLoc,
    ) -> RawLambda {
        if let Some(lam) = self.value_path_loc_constant(path, loc) {
            return lam;
        }
        let normalized = self.normalize_value_path_in_env(env, path);
        if let Some(lam) = self.value_path_loc_constant(&normalized, loc) {
            return lam;
        }
        self.translate_normal_path_raw_in_env(env, &normalized, loc)
    }

    fn translate_extension_path_raw(
        &mut self,
        path: &crate::types::Path,
        loc: SrcLoc,
    ) -> RawLambda {
        self.translate_value_path_raw(path, loc)
    }

    fn note_possible_required_modules_from_module_expr(&mut self, module_expr: &ModuleExpr) {
        fn note_from_path(
            this: &mut RawLambdaConverter<'_>,
            env: &crate::types::env::Env,
            path: &crate::types::Path,
        ) {
            let normalized = this.resolve_module_path_aliases(env, path);
            if let Some(alias_target) = crate::types::typecore::alias_target_for_module_path(
                &normalized,
                env,
                &mut this.persistent_env,
                this.type_ctx,
            ) {
                if !alias_target.same(&normalized) {
                    note_from_path(this, env, &alias_target);
                }
            }
            if let Ok(md) = env.lookup_module(&normalized) {
                if let Some(md_path) = md.md_path.as_ref() {
                    if !md_path.same(&normalized) {
                        note_from_path(this, env, md_path);
                    }
                }
            }

            match normalized.view() {
                crate::types::path::PathView::Pident(id) => {
                    if id.is_global() || id.is_persistent() {
                        this.note_possible_required_module(&id);
                    }
                }
                crate::types::path::PathView::Pdot(prefix, _, _) => {
                    note_from_path(this, env, prefix);
                }
                crate::types::path::PathView::Papply(left, right) => {
                    note_from_path(this, env, left);
                    note_from_path(this, env, right);
                }
            }
        }

        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
                self.note_possible_required_modules_from_module_expr(inner);
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                if let Some(env) = self.env_for_module_expr(module_expr) {
                    note_from_path(self, env.as_ref(), path);
                } else {
                    note_from_path(self, self.env, path);
                }
            }
            _ => {}
        }
    }

    fn note_possible_required_modules_from_empty_include(&mut self, module_expr: &ModuleExpr) {
        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
                self.note_possible_required_modules_from_empty_include(inner);
            }
            ModuleExprDesc::Tmod_ident(path, _) if path.as_pident().is_some() => {
                let id = path.as_pident().expect("guarded Pident");
                if let Some(env) = self.env_for_module_expr(module_expr) {
                    if env.lookup_module(path).is_err() {
                        self.note_possible_required_module(id);
                        return;
                    }
                } else if self.env.lookup_module(path).is_err() {
                    self.note_possible_required_module(id);
                    return;
                }
                self.note_possible_required_modules_from_module_expr(module_expr);
            }
            _ => self.note_possible_required_modules_from_module_expr(module_expr),
        }
    }

    fn env_for_expr(&self, expr: &Expression) -> Option<std::sync::Arc<crate::types::env::Env>> {
        self.type_ctx.get_typed_env(expr.exp_env)
    }

    fn env_for_module_expr(
        &self,
        module_expr: &ModuleExpr,
    ) -> Option<std::sync::Arc<crate::types::env::Env>> {
        self.type_ctx.get_typed_env(module_expr.mod_env)
    }

    fn compose_coercions_raw(left: &ModuleCoercion, right: &ModuleCoercion) -> ModuleCoercion {
        match (left, right) {
            (ModuleCoercion::Tcoerce_none, other) => other.clone(),
            (other, ModuleCoercion::Tcoerce_none) => other.clone(),
            (
                ModuleCoercion::Tcoerce_structure(left_positions, left_ids, left_runtime_fields),
                ModuleCoercion::Tcoerce_structure(
                    right_positions,
                    right_ids,
                    _right_runtime_fields,
                ),
            ) => {
                let composed_ids = left_ids
                    .iter()
                    .map(|(id, left_pos, left_cc)| {
                        let (right_pos, right_cc) = &right_positions[*left_pos];
                        (
                            *id,
                            *right_pos,
                            Self::compose_coercions_raw(left_cc, right_cc),
                        )
                    })
                    .collect::<Vec<_>>();

                let composed_positions = left_positions
                    .iter()
                    // Match compiler/ml/translmod.ml:137-157: OCaml turns the
                    // right-hand coercion list into an array and indexes it
                    // directly with the left position. Missing entries are a
                    // malformed coercion, not something to skip.
                    .map(|(left_pos, left_cc)| match left_cc {
                        ModuleCoercion::Tcoerce_primitive(_) => (*left_pos, left_cc.clone()),
                        _ => {
                            let (right_pos, right_cc) = &right_positions[*left_pos];
                            (*right_pos, Self::compose_coercions_raw(left_cc, right_cc))
                        }
                    })
                    .collect::<Vec<_>>();

                ModuleCoercion::Tcoerce_structure(
                    composed_positions,
                    composed_ids
                        .into_iter()
                        .chain(right_ids.iter().cloned())
                        .collect(),
                    left_runtime_fields.clone(),
                )
            }
            (
                ModuleCoercion::Tcoerce_functor(left_arg, left_res),
                ModuleCoercion::Tcoerce_functor(right_arg, right_res),
            ) => ModuleCoercion::Tcoerce_functor(
                Box::new(Self::compose_coercions_raw(right_arg, left_arg)),
                Box::new(Self::compose_coercions_raw(left_res, right_res)),
            ),
            (coercion, ModuleCoercion::Tcoerce_alias(env, path, inner)) => {
                ModuleCoercion::Tcoerce_alias(
                    *env,
                    path.clone(),
                    Box::new(Self::compose_coercions_raw(coercion, inner)),
                )
            }
            (_, other) => other.clone(),
        }
    }

    fn wrap_id_pos_list_raw<F>(
        &mut self,
        loc: SrcLoc,
        id_pos_list: &[(Ident, usize, ModuleCoercion)],
        mut get_field: F,
        lam: RawLambda,
    ) -> RawLambda
    where
        F: FnMut(&mut Self, &str, usize) -> RawLambda,
    {
        // OCaml's fold in compiler/ml/translmod.ml:112-127 leaves `lam`
        // unchanged for an empty `id_pos_list`; avoid the free-variable walk.
        if id_pos_list.is_empty() {
            return lam;
        }

        let fv = raw_free_variables(&lam);
        let mut lam = lam;
        let mut subst = HashMap::new();

        for (id, pos, coercion) in id_pos_list {
            if fv.contains(id) {
                let rebound = self.fresh_ident(id.name());
                let field = get_field(self, id.name(), *pos);
                let value = self.apply_coercion_raw(loc, LetKind::Alias, coercion, field);
                lam = RawLambda::let_(LetKind::Alias, rebound, value, lam);
                subst.insert(*id, rebound);
            }
        }

        if subst.is_empty() {
            lam
        } else {
            // OCaml `wrap_id_pos_list` builds a substitution containing only
            // `id' -> Lvar id''` before calling `Lambda.subst_lambda`
            // (compiler/ml/translmod.ml:112-127). Keep that substitution
            // specialized in Rust and consume `lam` instead of cloning the
            // whole module body.
            raw_subst_idents_owned(&subst, lam)
        }
    }

    fn apply_coercion_result_raw(
        &mut self,
        loc: impl Into<SrcLoc>,
        strict: LetKind,
        funct: RawLambda,
        param: Ident,
        arg: RawLambda,
        cc_res: &ModuleCoercion,
    ) -> RawLambda {
        let loc: SrcLoc = loc.into();
        self.name_lambda_raw(strict, funct, |this, id| {
            let body = this.apply_coercion_raw(
                loc,
                LetKind::Strict,
                cc_res,
                RawLambda::Lapply(Box::new(crate::raw_lambda::RawApply {
                    ap_func: Box::new(RawLambda::var(id)),
                    ap_args: vec![arg],
                    ap_info: ApInfo {
                        loc: this.lam_loc(loc),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
            );
            RawLambda::function_(
                1,
                vec![param],
                body,
                FunctionAttribute {
                    is_a_functor: true,
                    ..FunctionAttribute::default()
                },
                this.lam_loc(loc),
            )
        })
    }

    fn apply_coercion_raw(
        &mut self,
        loc: impl Into<SrcLoc>,
        strict: LetKind,
        coercion: &ModuleCoercion,
        arg: RawLambda,
    ) -> RawLambda {
        let loc: SrcLoc = loc.into();
        self.note_possible_required_modules_in_raw_lambda(&arg);
        let node_loc = self.lam_loc(loc);
        match coercion {
            ModuleCoercion::Tcoerce_none => arg,
            ModuleCoercion::Tcoerce_structure(positions, id_pos_list, runtime_fields) => {
                debug_assert_eq!(positions.len(), runtime_fields.len());
                self.name_lambda_raw(strict, arg, |this, id| {
                    let named = RawLambda::var(id);
                    let lam = RawLambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::Module(runtime_fields.clone()),
                            Mutable::Immutable,
                        ),
                        positions
                            .iter()
                            .zip(runtime_fields.iter())
                            .map(|((pos, cc), name)| {
                                let field = RawLambda::prim(
                                    Primitive::Pfield(
                                        *pos as i32,
                                        FieldDbgInfo::Module { name: name.clone() },
                                    ),
                                    vec![named.clone()],
                                    node_loc,
                                );
                                this.apply_coercion_raw(loc, LetKind::Alias, cc, field)
                            })
                            .collect(),
                        node_loc,
                    );
                    this.wrap_id_pos_list_raw(
                        loc,
                        id_pos_list,
                        |_, name, pos| {
                            RawLambda::prim(
                                Primitive::Pfield(
                                    pos as i32,
                                    FieldDbgInfo::Module {
                                        name: name.to_string(),
                                    },
                                ),
                                vec![named.clone()],
                                node_loc,
                            )
                        },
                        lam,
                    )
                })
            }
            ModuleCoercion::Tcoerce_functor(cc_arg, cc_res) => {
                // Identity functor coercion: both arg and result are identity
                if matches!(cc_arg.as_ref(), ModuleCoercion::Tcoerce_none)
                    && matches!(cc_res.as_ref(), ModuleCoercion::Tcoerce_none)
                {
                    return arg;
                }
                let param = self.fresh_ident("funarg");
                let carg =
                    self.apply_coercion_raw(loc, LetKind::Alias, cc_arg, RawLambda::var(param));
                self.apply_coercion_result_raw(loc, strict, arg, param, carg, cc_res)
            }
            ModuleCoercion::Tcoerce_primitive(pc) => self.transl_primitive_raw(
                &pc.pc_desc,
                pc.pc_type,
                SrcLoc::from(self.type_ctx.resolve_loc(pc.pc_loc)),
            ),
            ModuleCoercion::Tcoerce_alias(env_ref, path, inner) => {
                self.name_lambda_raw(strict, arg, |this, _| {
                    let translated = if let Some(env) = this.type_ctx.get_typed_env(*env_ref) {
                        this.translate_normal_path_raw_in_env(env.as_ref(), path, SrcLoc::from(loc))
                    } else {
                        let env = this.env;
                        this.translate_normal_path_raw_in_env(env, path, SrcLoc::from(loc))
                    };
                    this.apply_coercion_raw(loc, LetKind::Alias, inner, translated)
                })
            }
        }
    }

    fn make_module_block_raw(
        &mut self,
        fields: &[Ident],
        is_top_level: bool,
        cc: &ModuleCoercion,
        loc: impl Into<SrcLoc>,
    ) -> RawLambda {
        let loc: SrcLoc = loc.into();
        match cc {
            ModuleCoercion::Tcoerce_none => {
                // OCaml translmod `make_module_block` exports every field; a
                // shadowed value is dropped by the `simplify_signature`
                // coercion (typemod.ml:1738-1768), not here.
                let deduped_fields = fields.to_vec();
                let block_fields = deduped_fields.iter().cloned().map(RawLambda::var).collect();
                let tag = if is_top_level {
                    TagInfo::ModuleExport(deduped_fields)
                } else {
                    TagInfo::Module(
                        deduped_fields
                            .iter()
                            .map(|id| id.name().to_string())
                            .collect(),
                    )
                };
                RawLambda::prim(
                    Primitive::Pmakeblock(tag, Mutable::Immutable),
                    block_fields,
                    self.lam_loc(loc),
                )
            }
            ModuleCoercion::Tcoerce_structure(positions, id_pos_list, runtime_fields) => {
                debug_assert_eq!(positions.len(), runtime_fields.len());
                let field_ids = fields.iter().cloned().collect::<HashSet<_>>();
                // OCaml matching: Tcoerce_primitive entries generate wrapper functions
                // directly (not via field lookup), while other coercions use get_field(pos).
                let mut block_fields = Vec::new();
                let mut export_ids = Vec::new();
                for ((pos, field_cc), _name) in positions.iter().zip(runtime_fields.iter()) {
                    match field_cc {
                        ModuleCoercion::Tcoerce_primitive(pc) => {
                            // OCaml: transl_primitive p.pc_loc p.pc_desc p.pc_env p.pc_type
                            if is_top_level {
                                export_ids.push(pc.pc_id);
                            }
                            block_fields.push(self.transl_primitive_raw(
                                &pc.pc_desc,
                                pc.pc_type,
                                SrcLoc::from(self.type_ctx.resolve_loc(pc.pc_loc)),
                            ));
                        }
                        _ => {
                            // Use position-based lookup, but verify the name matches.
                            // When @internal.local modules shift positions, fall back
                            // to name-based lookup.
                            let id = fields
                                .get(*pos)
                                .cloned()
                                .and_then(|id| {
                                    if id.name() == _name.as_str() {
                                        Some(id)
                                    } else {
                                        fields
                                            .iter()
                                            .rev()
                                            .find(|f| f.name() == _name.as_str())
                                            .cloned()
                                    }
                                })
                                .or_else(|| {
                                    fields
                                        .iter()
                                        .rev()
                                        .find(|f| f.name() == _name.as_str())
                                        .cloned()
                                });
                            if let Some(id) = id {
                                if is_top_level {
                                    export_ids.push(id);
                                }
                                block_fields.push(self.apply_coercion_raw(
                                    loc,
                                    LetKind::Strict,
                                    field_cc,
                                    RawLambda::var(id),
                                ));
                            }
                        }
                    }
                }
                let tag = if is_top_level {
                    TagInfo::ModuleExport(export_ids)
                } else {
                    TagInfo::Module(runtime_fields.clone())
                };
                let lam = RawLambda::prim(
                    Primitive::Pmakeblock(tag, Mutable::Immutable),
                    block_fields,
                    self.lam_loc(loc),
                );
                let filtered_id_pos = id_pos_list
                    .iter()
                    .filter(|(id, _, _)| !field_ids.contains(id))
                    .cloned()
                    .collect::<Vec<_>>();
                self.wrap_id_pos_list_raw(
                    loc,
                    &filtered_id_pos,
                    |_, name, pos| {
                        fields
                            .get(pos)
                            .filter(|id| id.name() == name)
                            .or_else(|| fields.iter().rev().find(|f| f.name() == name))
                            .cloned()
                            .map(RawLambda::var)
                            .unwrap_or_else(RawLambda::unit)
                    },
                    lam,
                )
            }
            _ => {
                let block_fields = fields
                    .iter()
                    .cloned()
                    .map(|id| self.apply_coercion_raw(loc, LetKind::Alias, cc, RawLambda::var(id)))
                    .collect();
                let tag = if is_top_level {
                    TagInfo::ModuleExport(fields.to_vec())
                } else {
                    TagInfo::Module(fields.iter().map(|id| id.name().to_string()).collect())
                };
                RawLambda::prim(
                    Primitive::Pmakeblock(tag, Mutable::Immutable),
                    block_fields,
                    self.lam_loc(loc),
                )
            }
        }
    }

    fn convert_module_expr_raw_with_coercion(
        &mut self,
        module_expr: &ModuleExpr,
        rootpath: &Option<crate::types::Path>,
        cc: &ModuleCoercion,
    ) -> RawLambda {
        self.check_module_attribute(module_expr);

        if matches!(
            module_expr.mod_type,
            crate::types::decl::ModuleType::MtyAlias(_, _)
        ) {
            // OCaml lowers plain module aliases to Const_module_alias here.
            // They stay compile-time-only unless a later dynamic import/pack
            // path reifies the module reference, so static aliases must not
            // contribute a required JS import on their own.
            return self.apply_coercion_raw(
                module_expr.mod_loc,
                LetKind::Alias,
                cc,
                RawLambda::const_(Constant::ModuleAlias),
            );
        }

        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_structure(structure) => {
                let mut fields = Vec::new();
                self.convert_structure_items_raw(
                    &mut fields,
                    &structure.str_items,
                    false,
                    rootpath,
                    cc,
                    module_expr.mod_loc,
                )
            }
            ModuleExprDesc::Tmod_constraint(inner, _, _, inner_cc) => {
                let composed = Self::compose_coercions_raw(cc, inner_cc);
                self.convert_module_expr_raw_with_coercion(inner, rootpath, &composed)
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                let loc = module_expr.mod_loc;
                let arg = if let Some(env) = self.env_for_module_expr(module_expr) {
                    self.translate_module_path_raw_in_env(env.as_ref(), path, SrcLoc::from(loc))
                } else {
                    self.translate_module_path_raw(path, SrcLoc::from(loc))
                };
                self.apply_coercion_raw(loc, LetKind::Strict, cc, arg)
            }
            ModuleExprDesc::Tmod_unpack(expr, _) => {
                let loc = module_expr.mod_loc;
                let arg = self.convert_expr_raw(expr);
                self.apply_coercion_raw(loc, LetKind::Strict, cc, arg)
            }
            ModuleExprDesc::Tmod_functor(param, _, _, body) => {
                let loc = module_expr.mod_loc;
                let inline_attribute = self.get_inline_attribute_from(&module_expr.mod_attributes);
                let (arg_coercion, res_coercion) = match cc {
                    ModuleCoercion::Tcoerce_none => {
                        (&ModuleCoercion::Tcoerce_none, &ModuleCoercion::Tcoerce_none)
                    }
                    ModuleCoercion::Tcoerce_functor(arg_coercion, res_coercion) => {
                        (arg_coercion.as_ref(), res_coercion.as_ref())
                    }
                    _ => {
                        panic!("raw compile_functor: bad coercion")
                    }
                };
                let body_path = Self::functor_path(rootpath, param);
                let renamed_param = self.rename_ident(param);
                let arg = self.apply_coercion_raw(
                    loc,
                    LetKind::Alias,
                    arg_coercion,
                    RawLambda::var(renamed_param),
                );
                let body = RawLambda::let_(
                    LetKind::Alias,
                    *param,
                    arg,
                    self.convert_module_expr_raw_with_coercion(body, &body_path, res_coercion),
                );
                RawLambda::function_(
                    1,
                    vec![renamed_param],
                    body,
                    FunctionAttribute {
                        is_a_functor: true,
                        inline: inline_attribute,
                        ..FunctionAttribute::default()
                    },
                    self.lam_loc(loc),
                )
            }
            ModuleExprDesc::Tmod_apply(funct, arg, ccarg) => {
                let loc = module_expr.mod_loc;
                let inlined = self.get_inlined_attribute_from(&funct.mod_attributes);
                let funct_lam = self.with_inlined_attribute_check_suppressed(|this| {
                    this.convert_module_expr_raw_with_coercion(
                        funct,
                        &None,
                        &ModuleCoercion::Tcoerce_none,
                    )
                });
                let apply = RawLambda::Lapply(Box::new(crate::raw_lambda::RawApply {
                    ap_func: Box::new(funct_lam),
                    ap_args: vec![self.convert_module_expr_raw_with_coercion(arg, &None, ccarg)],
                    ap_info: ApInfo {
                        loc: self.lam_loc(loc),
                        inlined,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }));
                self.apply_coercion_raw(loc, LetKind::Strict, cc, apply)
            }
        }
    }

    fn convert_module_expr_raw(
        &mut self,
        module_expr: &ModuleExpr,
        rootpath: &Option<crate::types::Path>,
    ) -> RawLambda {
        self.convert_module_expr_raw_with_coercion(
            module_expr,
            rootpath,
            &ModuleCoercion::Tcoerce_none,
        )
    }

    /// Convert a module expression inside a Texp_pack.
    ///
    /// In OCaml, type_package calls type_module with alias=false, so the inner
    /// module expression has mod_type = Mty_signature (not Mty_alias). But in
    /// Rust, type_pack uses alias=true, producing Tmty_alias which causes the
    /// lambda conversion to emit Const_ModuleAlias (0a) instead of the actual
    /// module reference.
    ///
    /// For true alias modules, wrap_alias_ident_in_constraint adds a
    /// Tmod_constraint with Tcoerce_alias carrying the normalized alias target.
    /// When we find Tcoerce_alias + Tmty_alias, we emit 0a and apply the
    /// coercion (matching OCaml). For non-alias modules, we skip the Tmty_alias
    /// check to avoid incorrectly emitting 0a.
    fn convert_module_expr_for_pack_raw(&mut self, module_expr: &ModuleExpr) -> RawLambda {
        self.convert_module_expr_for_pack_inner(module_expr, &ModuleCoercion::Tcoerce_none)
    }

    fn convert_module_expr_for_pack_inner(
        &mut self,
        module_expr: &ModuleExpr,
        cc: &ModuleCoercion,
    ) -> RawLambda {
        // Each level is a `transl_module` call in OCaml, which starts with
        // `check_attribute_on_module` (translmod.ml:278-279); the fallback
        // below checks in `convert_module_expr_raw_with_coercion`.
        if matches!(
            module_expr.mod_desc,
            ModuleExprDesc::Tmod_constraint(..) | ModuleExprDesc::Tmod_ident(..)
        ) {
            self.check_module_attribute(module_expr);
        }
        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_constraint(inner, _, _, inner_cc) => {
                let composed = Self::compose_coercions_raw(cc, inner_cc);
                // If the composed coercion includes Tcoerce_alias and the inner
                // module is an alias (Mty_alias), use 0a + Alias to match OCaml.
                if matches!(composed, ModuleCoercion::Tcoerce_alias(..))
                    && matches!(
                        inner.mod_type,
                        crate::types::decl::ModuleType::MtyAlias(_, _)
                    )
                {
                    // OCaml recurses with `transl_module` into `inner` first,
                    // which checks its attributes (translmod.ml:278-279).
                    self.check_module_attribute(inner);
                    self.note_possible_required_modules_from_module_expr(inner);
                    return self.apply_coercion_raw(
                        inner.mod_loc,
                        LetKind::Alias,
                        &composed,
                        RawLambda::const_(Constant::ModuleAlias),
                    );
                }
                self.convert_module_expr_for_pack_inner(inner, &composed)
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                // Check if this ident is an alias with Tcoerce_alias coercion.
                if matches!(cc, ModuleCoercion::Tcoerce_alias(..))
                    && matches!(
                        module_expr.mod_type,
                        crate::types::decl::ModuleType::MtyAlias(_, _)
                    )
                {
                    self.note_possible_required_modules_from_module_expr(module_expr);
                    return self.apply_coercion_raw(
                        module_expr.mod_loc,
                        LetKind::Alias,
                        cc,
                        RawLambda::const_(Constant::ModuleAlias),
                    );
                }
                let loc = module_expr.mod_loc;
                let arg = if let Some(env) = self.env_for_module_expr(module_expr) {
                    self.translate_module_path_raw_in_env(env.as_ref(), path, SrcLoc::from(loc))
                } else {
                    self.translate_module_path_raw(path, SrcLoc::from(loc))
                };
                self.apply_coercion_raw(loc, LetKind::Strict, cc, arg)
            }
            // For other module expression kinds, fall back to the normal conversion
            _ => self.convert_module_expr_raw_with_coercion(module_expr, &None, cc),
        }
    }

    // ---- Recursive module compilation (Transl_recmodule) ----

    /// Create the location constant for `#init_mod`.
    /// Produces `Const_block(Blk_tuple, [filename, line, char])`.
    fn undefined_location(&self, loc_idx: LocIdx) -> RawLambda {
        self.arena.require_locations();
        let loc = self.loc(loc_idx);
        let fname = self.basename_for_loc(loc);
        RawLambda::Lconst(Constant::Block {
            tag_info: Box::new(TagInfo::Tuple),
            elements: vec![
                Constant::const_string(&fname),
                Constant::int(loc.loc_start.line),
                Constant::int(loc.loc_start.column()),
            ],
        })
    }

    /// Compute the init shape for a recursive module.
    /// Returns `Some((loc_const, shape_const))` if the module can be initialized,
    /// `None` if the module has no shape (e.g., functor).
    ///
    /// Mirrors OCaml's `Transl_recmodule.init_shape`.
    fn init_shape(&self, modl: &ModuleExpr) -> Option<(RawLambda, RawLambda)> {
        let env = self.type_ctx.get_typed_env(modl.mod_env)?;
        // Get the decl::ModuleType.
        // First try the typedtree mod_type directly; if it is unusable, try
        // the Tmod_constraint wrapper or look it up in the env.
        let decl_mty = self.get_decl_module_type(modl, &env);
        let decl_mty = decl_mty?;
        let shape = self.init_shape_mod(&env, &decl_mty)?;
        Some((
            self.undefined_location(modl.mod_loc),
            RawLambda::Lconst(shape),
        ))
    }

    /// Extract decl::ModuleType from a module expression.
    /// Tries multiple strategies:
    /// 1. Convert typedtree mod_type directly (if not placeholder)
    /// 2. For Tmod_constraint, try constraint type, then recurse into inner
    /// 3. For Tmod_structure, build from the structure's str_type
    /// 4. For Tmod_ident, it's a module alias
    fn get_decl_module_type(
        &self,
        modl: &ModuleExpr,
        env: &crate::types::env::Env,
    ) -> Option<crate::types::decl::ModuleType> {
        // Strategy 1: direct semantic mod_type from the typedtree node.
        let direct_mty = modl.mod_type.clone();
        if let crate::types::decl::ModuleType::MtyIdent(_) = &direct_mty {
            if let Some(resolved) = self.scrape_modtype(env, &direct_mty) {
                return Some(resolved);
            }
        }
        if !matches!(
            &direct_mty,
            crate::types::decl::ModuleType::MtySignature(sig) if sig.is_empty()
        ) {
            return Some(direct_mty);
        }

        // Strategy 2: based on mod_desc
        match &modl.mod_desc {
            ModuleExprDesc::Tmod_constraint(inner, constraint_mty, _, _) => {
                // Try the constraint's module type first
                let mty = constraint_mty.clone();
                {
                    // If it's concrete (not MtyIdent), use it directly
                    if !matches!(&mty, crate::types::decl::ModuleType::MtyIdent(_)) {
                        return Some(mty);
                    }
                    // If it's MtyIdent, try to resolve it
                    if let Some(resolved) = self.scrape_modtype(env, &mty) {
                        return Some(resolved);
                    }
                    // Fall through to try the inner module
                }
                // Recurse into the inner module expr - this gets the actual structure type
                return self.get_decl_module_type(inner, env);
            }
            ModuleExprDesc::Tmod_structure(structure) => {
                // Build MtySignature from the structure's str_type (which is decl::Signature)
                return Some(crate::types::decl::ModuleType::MtySignature(
                    std::sync::Arc::new(structure.str_type.clone()),
                ));
            }
            ModuleExprDesc::Tmod_ident(_, _) => {
                // Module alias - treated as alias
                return None; // OCaml returns MtyAlias but we don't have the path info
            }
            _ => {}
        }

        None
    }

    /// Compute the shape constant for a module type.
    /// Returns `None` if the module type can't be initialized (functor, unknown ident).
    fn init_shape_mod(
        &self,
        env: &crate::types::env::Env,
        mty: &crate::types::decl::ModuleType,
    ) -> Option<Constant> {
        use crate::types::decl::ModuleType;

        // Scrape: resolve Mty_ident to its expansion
        let scraped = self.scrape_modtype(env, mty);
        let mty_ref = scraped.as_ref().unwrap_or(mty);

        match mty_ref {
            ModuleType::MtyIdent(_) => None, // couldn't scrape further
            ModuleType::MtyAlias(_, _) => {
                // Module alias: constant value
                Some(Constant::Block {
                    // value tag
                    tag_info: Box::new(TagInfo::constructor("value", 2)),
                    elements: vec![Constant::ModuleAlias],
                })
            }
            ModuleType::MtySignature(sg) => {
                let struct_shape = self.init_shape_struct(env, sg)?;
                Some(Constant::Block {
                    // Module tag
                    tag_info: Box::new(TagInfo::constructor("Module", 2)),
                    elements: vec![Constant::Block {
                        tag_info: Box::new(TagInfo::Tuple),
                        elements: struct_shape,
                    }],
                })
            }
            ModuleType::MtyFunctor { .. } => None, // can't init functors
        }
    }

    /// Compute shape constants for each item in a signature.
    /// Returns `None` if any value item can't be shaped (non-function value).
    fn init_shape_struct(
        &self,
        env: &crate::types::env::Env,
        sg: &[crate::types::decl::SignatureItem],
    ) -> Option<Vec<Constant>> {
        use crate::types::decl::{SignatureItem as DeclSigItem, ValueKind as DeclValueKind};

        let mut result = Vec::new();
        let mut env = env.clone_preserve_id();

        for item in sg {
            match item {
                DeclSigItem::SigValue(id, vd) => {
                    match &vd.val_kind {
                        DeclValueKind::ValPrim(_) => {
                            // Primitive values don't need shapes, skip
                            continue;
                        }
                        DeclValueKind::ValReg => {
                            // Regular value: check if it's a function type
                            let expanded =
                                crate::types::ctype::expand_head(self.type_ctx, &env, vd.val_type);
                            let is_function = matches!(
                                &*self.type_ctx.borrow_desc(expanded),
                                TypeDesc::Tarrow { .. }
                            );
                            if !is_function {
                                return None; // non-function value, can't init
                            }
                            // Match OCaml transl_recmodule.init_shape: keep the
                            // Function constructor metadata even though raw
                            // printing still renders it as `0a`.
                            let init_v = recmodule_function_shape_constant();
                            // add_name: wrap with (shape, name) tuple
                            result.push(Constant::Block {
                                tag_info: Box::new(TagInfo::Tuple),
                                elements: vec![init_v, Constant::const_string(id.name())],
                            });
                        }
                    }
                }
                DeclSigItem::SigType(id, tdecl, _) => {
                    env.add_type(*id, tdecl.clone());
                }
                DeclSigItem::SigTypext(_, _, _) => {
                    return None; // type extensions can't be initialized
                }
                DeclSigItem::SigModule(id, md, _) => {
                    let sub_shape = self.init_shape_mod(&env, &md.md_type)?;
                    // add_name: wrap with (shape, name) tuple
                    result.push(Constant::Block {
                        tag_info: Box::new(TagInfo::Tuple),
                        elements: vec![sub_shape, Constant::const_string(id.name())],
                    });
                    env.add_module(*id, md.clone());
                }
                DeclSigItem::SigModtype(id, minfo) => {
                    env.add_modtype(*id, minfo.clone());
                }
                DeclSigItem::SigClass => {
                    // ReScript doesn't have classes, but just in case
                    return None;
                }
                DeclSigItem::SigClassType => {
                    // Skip class types
                    continue;
                }
            }
        }
        Some(result)
    }

    /// Simple Mtype.scrape: resolve Mty_ident to concrete module type.
    fn scrape_modtype(
        &self,
        env: &crate::types::env::Env,
        mty: &crate::types::decl::ModuleType,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::ModuleType;
        match mty {
            ModuleType::MtyIdent(path) => {
                // Look up the modtype declaration and try to expand
                if let Ok(mtd) = env.lookup_modtype(path) {
                    if let Some(ref expanded) = mtd.mtd_type {
                        // Recursively scrape the expansion
                        let result = self.scrape_modtype(env, expanded);
                        Some(result.unwrap_or_else(|| expanded.clone()))
                    } else {
                        None // abstract module type, can't scrape
                    }
                } else {
                    None
                }
            }
            _ => None, // already concrete
        }
    }

    /// Check if a raw lambda is a block of only functions and constants.
    /// Used to decide if we can use simple `letrec` for recursive modules.
    ///
    /// Mirrors OCaml's `Transl_recmodule.is_function_or_const_block`.
    fn is_function_or_const_block(lam: &RawLambda, acc: &HashSet<Ident>) -> bool {
        match lam {
            RawLambda::Lprim(info) if matches!(info.primitive, Primitive::Pmakeblock(_, _)) => {
                info.args.iter().all(|arg| match arg {
                    RawLambda::Lvar(id) => acc.contains(id),
                    RawLambda::Lfunction(_) | RawLambda::Lconst(_) => true,
                    _ => false,
                })
            }
            RawLambda::Llet(_, id, value, cont) => {
                if matches!(value.as_ref(), RawLambda::Lfunction(_)) {
                    let mut new_acc = acc.clone();
                    new_acc.insert(*id);
                    Self::is_function_or_const_block(cont, &new_acc)
                } else if matches!(value.as_ref(), RawLambda::Lconst(_)) {
                    Self::is_function_or_const_block(cont, acc)
                } else if let RawLambda::Lvar(id2) = value.as_ref() {
                    if acc.contains(id2) {
                        let mut new_acc = acc.clone();
                        new_acc.insert(*id);
                        Self::is_function_or_const_block(cont, &new_acc)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            RawLambda::Lletrec(bindings, cont) => {
                let mut new_acc = acc.clone();
                for (id, rhs) in bindings {
                    if !matches!(rhs, RawLambda::Lfunction(_)) {
                        return false;
                    }
                    new_acc.insert(*id);
                }
                Self::is_function_or_const_block(cont, &new_acc)
            }
            _ => false,
        }
    }

    /// Check if all bindings are either strict (no shape) or all-function blocks.
    fn is_strict_or_all_functions(bindings: &[RecModuleBinding]) -> bool {
        bindings.iter().all(|binding| match &binding.init {
            None => true,
            Some(_) => Self::is_function_or_const_block(&binding.rhs, &HashSet::new()),
        })
    }

    /// Reorder recursive module bindings to honor dependencies.
    /// Bindings without shapes (strict) are ordered after their dependencies.
    /// Bindings with shapes (init_mod) can appear in any order.
    ///
    /// Mirrors OCaml's `Transl_recmodule.reorder_rec_bindings`.
    fn reorder_rec_bindings(&mut self, bindings: Vec<RecModuleBinding>) -> Vec<RecModuleBinding> {
        let n = bindings.len();
        if n == 0 {
            return bindings;
        }

        // Compute free variables for each RHS
        let fvs: Vec<HashSet<Ident>> = bindings
            .iter()
            .map(|binding| raw_free_variables(&binding.rhs))
            .collect();
        let ids: Vec<&Ident> = bindings.iter().map(|binding| &binding.id).collect();
        let locs: Vec<Location> = bindings.iter().map(|binding| binding.loc).collect();

        #[derive(Clone, Copy, PartialEq)]
        enum Status {
            Undefined,
            Inprogress,
            Defined,
        }
        let mut status = vec![Status::Undefined; n];
        let mut result_indices: Vec<usize> = Vec::with_capacity(n);
        let mut diagnostic: Option<(Location, String)> = None;

        fn emit_binding(
            i: usize,
            ids: &[&Ident],
            locs: &[Location],
            fvs: &[HashSet<Ident>],
            inits: &[&Option<(RawLambda, RawLambda)>],
            status: &mut [Status],
            result: &mut Vec<usize>,
            diagnostic: &mut Option<(Location, String)>,
        ) {
            match status[i] {
                Status::Defined => (),
                Status::Inprogress => {
                    if diagnostic.is_none() {
                        *diagnostic = Some((
                            locs[i],
                            format!(
                                "Cannot safely evaluate the definition of the recursively-defined module {}",
                                ids[i].name()
                            ),
                        ));
                    }
                }
                Status::Undefined => {
                    if inits[i].is_none() {
                        // Strict binding: must order after dependencies
                        status[i] = Status::Inprogress;
                        for j in 0..ids.len() {
                            if fvs[i].contains(ids[j]) {
                                emit_binding(j, ids, locs, fvs, inits, status, result, diagnostic);
                            }
                        }
                    }
                    result.push(i);
                    status[i] = Status::Defined;
                }
            }
        }

        let inits: Vec<&Option<(RawLambda, RawLambda)>> =
            bindings.iter().map(|binding| &binding.init).collect();

        for i in 0..n {
            if status[i] == Status::Undefined {
                emit_binding(
                    i,
                    &ids,
                    &locs,
                    &fvs,
                    &inits,
                    &mut status,
                    &mut result_indices,
                    &mut diagnostic,
                );
            }
        }

        if let Some((loc, message)) = diagnostic {
            self.report_diagnostic(loc, message);
        }

        // Reorder bindings according to result_indices
        let mut reordered = Vec::with_capacity(n);
        // Use a vec of Options so we can take values out
        let mut slots: Vec<Option<RecModuleBinding>> = bindings.into_iter().map(Some).collect();
        for i in result_indices {
            if let Some(binding) = slots[i].take() {
                reordered.push(binding);
            }
        }
        reordered
    }

    /// Generate the init_mod/update_mod code or simple letrec for recursive modules.
    ///
    /// Three phases for init_mod/update_mod:
    /// 1. `let M = #init_mod(loc, shape)` for modules with shapes
    /// 2. `let M = rhs` for strict modules (no shape)
    /// 3. `seq #update_mod(shape, M, rhs)` to fill in actual values
    fn eval_rec_bindings(bindings: Vec<RecModuleBinding>, cont: RawLambda) -> RawLambda {
        if Self::is_strict_or_all_functions(&bindings) {
            // Simple letrec: all modules are just function/const blocks
            let rec_bindings: Vec<(Ident, RawLambda)> = bindings
                .into_iter()
                .map(|binding| (binding.id, binding.rhs))
                .collect();
            // transl_recmodule.ml `eval_rec_bindings`: `Lambda_scc.bind_rec`.
            return crate::raw_lambda::lambda_scc::bind_rec(rec_bindings, cont);
        }

        // Phase 3: patch_forwards - update_mod for each shaped binding
        let mut result = cont;
        for binding in bindings.iter().rev() {
            if let Some((_loc, shape)) = &binding.init {
                let patch = if Self::shape_is_empty(shape) {
                    binding.rhs.clone()
                } else {
                    RawLambda::prim(
                        Primitive::PupdateMod,
                        vec![
                            shape.clone(),
                            RawLambda::Lvar(binding.id),
                            binding.rhs.clone(),
                        ],
                        LamLoc::NONE,
                    )
                };
                result = RawLambda::seq(patch, result);
            }
        }

        // Phase 2: bind_strict - let bindings for modules without shapes
        for binding in bindings.iter().rev() {
            if binding.init.is_none() {
                result = RawLambda::let_(LetKind::Strict, binding.id, binding.rhs.clone(), result);
            }
        }

        // Phase 1: bind_inits - init_mod for modules with shapes
        for binding in bindings.iter().rev() {
            if let Some((loc, shape)) = &binding.init {
                let init = if Self::shape_is_empty(shape) {
                    RawLambda::unit()
                } else {
                    RawLambda::prim(
                        Primitive::PinitMod,
                        vec![loc.clone(), shape.clone()],
                        LamLoc::NONE,
                    )
                };
                result = RawLambda::let_(LetKind::Strict, binding.id, init, result);
            }
        }

        result
    }

    /// OCaml `Transl_recmodule.shape_is_empty`: a shape with no fields has
    /// nothing to initialize and nothing to patch, but the right hand side
    /// still runs for its effects.
    fn shape_is_empty(shape: &RawLambda) -> bool {
        matches!(
            shape,
            RawLambda::Lconst(Constant::Block { elements, .. })
                if matches!(
                    elements.as_slice(),
                    [Constant::Block { elements: inner, .. }] if inner.is_empty()
                )
        )
    }

    /// Compile recursive module bindings.
    /// Mirrors OCaml's `Transl_recmodule.compile_recmodule`.
    fn compile_recmodule(
        &mut self,
        bindings: &[crate::types::typedtree::ModuleBinding],
        cont: RawLambda,
        rootpath: &Option<crate::types::Path>,
    ) -> RawLambda {
        // Collect (id, init_shape, rhs) for each binding
        let collected: Vec<RecModuleBinding> = bindings
            .iter()
            .map(|mb| {
                let id = mb.mb_id;
                let loc = mb.mb_expr.mod_loc;
                let shape = self.init_shape(&mb.mb_expr);
                let rhs = self
                    .convert_module_expr_raw(&mb.mb_expr, &Self::field_path(rootpath, &mb.mb_id));
                RecModuleBinding {
                    id,
                    loc: self.loc(loc),
                    init: shape,
                    rhs,
                }
            })
            .collect();

        let reordered = self.reorder_rec_bindings(collected);
        Self::eval_rec_bindings(reordered, cont)
    }

    fn convert_structure_items_raw(
        &mut self,
        fields: &mut Vec<Ident>,
        items: &[StructureItem],
        is_top_level: bool,
        rootpath: &Option<crate::types::Path>,
        cc: &ModuleCoercion,
        loc: impl Into<SrcLoc>,
    ) -> RawLambda {
        let loc: SrcLoc = loc.into();
        let Some((item, rem)) = items.split_first() else {
            return self.make_module_block_raw(fields, is_top_level, cc, loc);
        };

        match &item.str_desc {
            StructureItemDesc::Tstr_eval(expr, _) => {
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                let expr = self.convert_expr_raw(expr);
                RawLambda::seq(expr, body)
            }
            StructureItemDesc::Tstr_value(rec_flag, bindings) => {
                let old_len = fields.len();
                fields.extend(let_bound_idents(bindings));
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                if is_top_level && *rec_flag == crate::parser::ast::RecFlag::Nonrecursive {
                    for binding in bindings {
                        match &binding.vb_pat.pat_desc {
                            PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_alias(_, _, _) => {}
                            _ if !crate::types::typecore::parmatch_irrefutable(
                                self.type_ctx,
                                self.arena,
                                self.env,
                                &mut self.persistent_env,
                                &binding.vb_pat,
                            ) =>
                            {
                                self.report_diagnostic(
                                    self.loc(binding.vb_pat.pat_loc),
                                    "This pattern can fail to match, so it is not allowed in a top-level `let` binding.".to_string(),
                                );
                                // translmod.ml:392 raises here, so the binding
                                // itself is never translated.
                                return body;
                            }
                            _ => {}
                        }
                    }
                }
                self.convert_let_with_body_raw_at_root(*rec_flag, bindings, body, rootpath)
            }
            StructureItemDesc::Tstr_module(binding) => {
                let old_len = fields.len();
                // OCaml always skips @internal.local modules from the field list,
                // regardless of coercion type. Hidden modules don't get position
                // indices in the runtime field layout.
                let is_hidden = self.rescript_hide_attributes(&binding.mb_attributes);
                if !is_hidden {
                    fields.push(binding.mb_id);
                }
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                let mut module_body = self.convert_module_expr_raw(
                    &binding.mb_expr,
                    &Self::field_path(rootpath, &binding.mb_id),
                );
                // Apply @inline attribute from module binding (matches OCaml's
                // Translattribute.add_inline_attribute)
                let inline_attr = self.get_inline_attribute_from(&binding.mb_attributes);
                module_body =
                    self.apply_inline_attribute_raw(module_body, binding.mb_loc, inline_attr);

                RawLambda::let_(
                    Self::pure_module(&binding.mb_expr),
                    binding.mb_id,
                    module_body,
                    body,
                )
            }
            StructureItemDesc::Tstr_typext(tyext) => {
                let old_len = fields.len();
                fields.extend(tyext.tyext_constructors.iter().map(|ext| ext.ext_id));
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                self.transl_type_extension_raw(rootpath, tyext, body)
            }
            StructureItemDesc::Tstr_exception(ext) => {
                let old_len = fields.len();
                fields.push(ext.ext_id);
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                RawLambda::let_(
                    LetKind::Strict,
                    ext.ext_id,
                    self.transl_extension_constructor_raw(
                        Self::field_path(rootpath, &ext.ext_id),
                        ext,
                    ),
                    body,
                )
            }
            StructureItemDesc::Tstr_include(incl) => {
                let ids = Self::include_bound_idents(&incl.incl_type);
                if ids.is_empty() {
                    self.note_possible_required_modules_from_empty_include(&incl.incl_mod);
                }
                let old_len = fields.len();
                fields.extend(ids.iter().map(|(id, _)| *id));
                let mid = self.fresh_ident("include");
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                let body = self.rebind_included_idents_raw(&mid, &ids, body, incl.incl_loc);

                RawLambda::let_(
                    Self::pure_module(&incl.incl_mod),
                    mid,
                    self.convert_module_expr_raw(&incl.incl_mod, &None),
                    body,
                )
            }
            StructureItemDesc::Tstr_recmodule(bindings) => {
                // OCaml: add all recursive module idents to fields, then generate letrec
                let old_len = fields.len();
                for mb in bindings.iter() {
                    fields.push(mb.mb_id);
                }
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);

                self.compile_recmodule(bindings, body, rootpath)
            }
            StructureItemDesc::Tstr_primitive(_)
            | StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_modtype(_)
            | StructureItemDesc::Tstr_open(_)
            | StructureItemDesc::Tstr_attribute(_) => {
                self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc)
            }
        }
    }

    fn warning_attribute_spec(
        &self,
        attr: &crate::parser::ast::Attribute,
    ) -> Option<(bool, String)> {
        let name = self.arena.get_string(attr.0.txt);
        let is_error = matches!(name, "warnerror" | "ocaml.warnerror");
        if !is_error && !matches!(name, "warning" | "ocaml.warning") {
            return None;
        }
        let crate::parser::ast::Payload::PStr(items) = &attr.1 else {
            return None;
        };
        let [item] = items.as_slice() else {
            return None;
        };
        let crate::parser::ast::StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
            return None;
        };
        let expr = self.arena.get_expr(eval.0);
        // builtin_attributes.ml `string_of_payload`.
        let spec = crate::ast_payload::semantic_string_of_expression(self.arena, expr).ok()??;
        Some((is_error, spec))
    }

    fn with_warning_scope<T>(
        &mut self,
        attrs: &crate::parser::ast::Attributes,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        if attrs.is_empty() {
            return f(self);
        }
        let previous = self.warning_config.clone();
        // `Builtin_attributes.warning_attribute` (builtin_attributes.ml:180-212):
        // an unusable payload is reported, a usable one updates the state.
        for attr in attrs.iter().rev() {
            let name = self.arena.get_string(attr.0.txt);
            if !matches!(
                name,
                "warning" | "ocaml.warning" | "warnerror" | "ocaml.warnerror"
            ) {
                continue;
            }
            let Some((is_error, spec)) = self.warning_attribute_spec(attr) else {
                self.report_warning(
                    attr.0.loc,
                    Warning::AttributePayload {
                        attr: name.to_string(),
                        message: "A single string literal is expected".to_string(),
                    },
                );
                continue;
            };
            let mut scratch = WarningConfig::new();
            let parsed = if is_error {
                scratch.parse_as_error(&spec)
            } else {
                scratch.parse(&spec)
            };
            if parsed.is_err() {
                self.report_warning(
                    attr.0.loc,
                    Warning::AttributePayload {
                        attr: name.to_string(),
                        message: "Ill-formed list of warnings".to_string(),
                    },
                );
                continue;
            }
            if is_error {
                let _ = self.warning_config.parse_as_error(&spec);
            } else {
                let _ = self.warning_config.parse(&spec);
            }
        }
        let result = f(self);
        self.warning_config = previous;
        result
    }

    fn convert_expr_raw(&mut self, expr: &Expression) -> RawLambda {
        self.with_warning_scope(&expr.exp_attributes, |this| {
            this.convert_expr_raw_unscoped(expr)
        })
    }

    fn convert_expr_raw_unscoped(&mut self, expr: &Expression) -> RawLambda {
        self.check_expr_attribute(expr);
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => {
                    // translcore.ml `transl_primitive` warns about a
                    // polymorphic comparison used as a value.
                    let warn_loc = Some(expr.exp_loc);
                    if let Some(env) = self.env_for_expr(expr) {
                        self.translate_primitive_raw_in_env(
                            SrcLoc::from(expr.exp_loc),
                            prim,
                            expr.exp_type,
                            env.as_ref(),
                            desc.val_type,
                            warn_loc,
                        )
                    } else {
                        let env = self.env;
                        self.translate_primitive_raw_in_env(
                            SrcLoc::from(expr.exp_loc),
                            prim,
                            expr.exp_type,
                            env,
                            desc.val_type,
                            warn_loc,
                        )
                    }
                }
                ValueKind::ValReg => {
                    if let Some(env) = self.env_for_expr(expr) {
                        self.translate_value_path_raw_in_env(
                            env.as_ref(),
                            path,
                            SrcLoc::from(expr.exp_loc),
                        )
                    } else {
                        self.translate_value_path_raw(path, SrcLoc::from(expr.exp_loc))
                    }
                }
            },
            ExpressionDesc::Texp_constant(cst) => RawLambda::const_(self.convert_constant(cst)),
            ExpressionDesc::Texp_let(rec_flag, bindings, body) => {
                let body_lam = self.convert_expr_raw(body);
                self.convert_let_with_body_raw(*rec_flag, bindings, body_lam)
            }
            ExpressionDesc::Texp_function {
                params,
                body,
                async_,
            } => {
                let directive =
                    Self::get_directive_attribute_from(&expr.exp_attributes, self.arena);
                let inline = self.get_inline_attribute_from(&expr.exp_attributes);
                self.convert_nary_function_raw(
                    Some(expr),
                    params,
                    body,
                    *async_,
                    directive,
                    inline,
                    expr.exp_loc,
                )
            }
            // translcore.ml `Texp_tagged_template`: `transl_exp tag ::
            // transl_list values`; OCaml evaluates the cons tail first.
            ExpressionDesc::Texp_tagged_template {
                tag,
                raw_sources,
                values,
            } => {
                let values: Vec<RawLambda> = values
                    .iter()
                    .map(|value| self.convert_expr_raw(value))
                    .collect();
                let mut args = Vec::with_capacity(values.len() + 1);
                args.push(self.convert_expr_raw(tag));
                args.extend(values);
                RawLambda::prim(
                    Primitive::PtaggedTemplate(raw_sources.clone()),
                    args,
                    self.lam_loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_template { segments, values } => {
                let args = values
                    .iter()
                    .map(|value| self.convert_expr_raw(value))
                    .collect();
                RawLambda::prim(
                    Primitive::Ptemplate(segments.clone()),
                    args,
                    self.lam_loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => self.convert_apply_raw(
                expr.exp_loc,
                expr.exp_loc,
                funct,
                args,
                *partial,
                *transformed_jsx,
            ),
            ExpressionDesc::Texp_match(scrut, cases, exn_cases, partial) => {
                // OCaml transl_match allocates the exception binder before it
                // translates either case list, even when exn_pat_expr_list is
                // empty (compiler/ml/translcore.ml:1215-1218). Keep that shared
                // Ident allocation order; ordinary matches intentionally do
                // not retain this binder in the resulting lambda.
                let exn_id = self.name_pattern_ident("exn", exn_cases);
                if !exn_cases.is_empty() {
                    // Match with exception cases: wrap in try-with + static catch.
                    // Matches OCaml's transl_match logic from translcore.ml.
                    let loc = expr.exp_loc;
                    let partial = *partial;
                    self.compile_match_with_exceptions_raw(
                        loc, scrut, cases, exn_cases, partial, expr, exn_id,
                    )
                } else {
                    // For single-case matches with unboxed constructor patterns,
                    // use the irrefutable path which correctly handles transparent field access.
                    if cases.len() == 1 && cases[0].c_guard.is_none() {
                        if let PatternDesc::Tpat_construct(_, cstr, _) = &cases[0].c_lhs.pat_desc {
                            if matches!(
                                cstr.cstr_kind,
                                crate::types::ConstructorKind::Ordinary(reference)
                                    if matches!(reference.representation(self.type_ctx),
                                        crate::types::VariantConstructorCase::Block(ref block)
                                            if block.is_untagged())
                            ) {
                                if let Some(result) =
                                    self.compile_irrefutable_match_raw(scrut, cases)
                                {
                                    return result;
                                }
                            }
                        }
                    }
                    let partial = *partial;
                    let loc = expr.exp_loc;
                    // Use full matching compiler (ported from OCaml's matching.ml)
                    self.compile_full_matching(loc, scrut, cases, partial)
                }
            }
            ExpressionDesc::Texp_try(body, cases) => {
                let _loc = expr.exp_loc;
                let exn_id = self.name_pattern_ident("exn", cases);
                let handler = self.compile_trywith_handler_raw(&exn_id, cases);
                let (exn_id, handler) = self.pack_trywith_exn(exn_id, handler);
                let body_lam = self.convert_expr_raw(body);
                RawLambda::LtryWith(Box::new(body_lam), exn_id, Box::new(handler))
            }
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items
                    .iter()
                    .map(|item| self.convert_expr_raw(item))
                    .collect::<Vec<_>>();
                self.raw_block_or_prim(0, TagInfo::Tuple, elems, expr.exp_loc)
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => {
                self.convert_construct_raw(SrcLoc::from(expr.exp_loc), cstr, args)
            }
            ExpressionDesc::Texp_variant(tag, arg) => match arg {
                None => raw_polyvariant_const(tag),
                Some(arg) => {
                    let arg_lam = self.convert_expr_raw(arg);
                    self.raw_block_or_prim(
                        0,
                        TagInfo::PolyVar(tag.to_string()),
                        vec![
                            RawLambda::const_(Constant::int(crate::types::btype::hash_variant(
                                tag,
                            ))),
                            arg_lam,
                        ],
                        expr.exp_loc,
                    )
                }
            },
            ExpressionDesc::Texp_ifthenelse(cond, then_, else_) => {
                let else_lam = else_
                    .as_ref()
                    .map(|e| self.convert_expr_raw(e))
                    .unwrap_or_else(RawLambda::unit);
                // Keeps the converter's existing order: else, condition, then.
                let cond_lam = self.convert_expr_raw(cond);
                let then_lam = self.convert_expr_raw(then_);
                RawLambda::if_(cond_lam, then_lam, else_lam)
            }
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
                ..
            } => self.convert_record_raw(
                SrcLoc::from(expr.exp_loc),
                fields,
                extended_expression.as_deref(),
                None,
                None,
            ),
            ExpressionDesc::Texp_record_sparse {
                fields,
                all_labels,
                omitted_loc,
                ..
            } => {
                let (record_fields, logical_field_count) =
                    self.sparse_record_fields_for_lambda(all_labels, fields, *omitted_loc);
                self.convert_record_raw(
                    SrcLoc::from(expr.exp_loc),
                    &record_fields,
                    None,
                    None,
                    logical_field_count,
                )
            }
            ExpressionDesc::Texp_field(record, _, lbl) => {
                if matches!(lbl.lbl_repres, RecordRepresentation::RecordUnboxed(_)) {
                    self.convert_expr_raw(record)
                } else if let Some((pos, info)) = raw_record_field_access(lbl) {
                    RawLambda::prim(
                        Primitive::Pfield(pos, info),
                        vec![self.convert_expr_raw(record)],
                        self.lam_loc(expr.exp_loc),
                    )
                } else {
                    RawLambda::unit()
                }
            }
            ExpressionDesc::Texp_setfield(record, _, lbl, value) => {
                if let Some((pos, info)) = raw_record_setfield_access(lbl) {
                    RawLambda::prim(
                        Primitive::Psetfield(pos, info),
                        vec![self.convert_expr_raw(record), self.convert_expr_raw(value)],
                        self.lam_loc(expr.exp_loc),
                    )
                } else {
                    RawLambda::unit()
                }
            }
            ExpressionDesc::Texp_array(items) => {
                let elems = items
                    .iter()
                    .map(|item| self.convert_expr_raw(item))
                    .collect::<Vec<_>>();
                RawLambda::prim(Primitive::Pmakearray, elems, self.lam_loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_sequence(a, b) => {
                // OCaml builds `Lsequence (transl_exp a, transl_exp b)`, and the
                // constructor arguments are evaluated right-to-left. Match that
                // traversal so raise-count allocation stays in sync.
                let second = self.convert_expr_raw(b);
                let first = self.convert_expr_raw(a);
                RawLambda::seq(first, second)
            }
            // OCaml `Translcore.transl_exp0` after #8348:
            // `Texp_break -> Lbreak | Texp_continue -> Lcontinue`.
            ExpressionDesc::Texp_break => RawLambda::Lbreak,
            ExpressionDesc::Texp_continue => RawLambda::Lcontinue,
            ExpressionDesc::Texp_while(cond, body) => RawLambda::Lwhile(
                Box::new(self.convert_expr_raw(cond)),
                Box::new(self.convert_expr_raw(body)),
            ),
            ExpressionDesc::Texp_for(var, _pat, start, end, dir, body) => {
                let dir = match dir {
                    crate::parser::ast::DirectionFlag::Upto => crate::lambda::DirectionFlag::Upto,
                    crate::parser::ast::DirectionFlag::Downto => {
                        crate::lambda::DirectionFlag::Downto
                    }
                };
                RawLambda::Lfor(
                    *var,
                    Box::new(self.convert_expr_raw(start)),
                    Box::new(self.convert_expr_raw(end)),
                    dir,
                    Box::new(self.convert_expr_raw(body)),
                )
            }
            // Upstream #7887: typed for-of / for-await-of -> raw lambda.
            ExpressionDesc::Texp_for_of(var, _pat, iterable, body) => RawLambda::Lfor_of(
                *var,
                Box::new(self.convert_expr_raw(iterable)),
                Box::new(self.convert_expr_raw(body)),
            ),
            ExpressionDesc::Texp_for_await_of(var, _pat, iterable, body) => {
                RawLambda::Lfor_await_of(
                    *var,
                    Box::new(self.convert_expr_raw(iterable)),
                    Box::new(self.convert_expr_raw(body)),
                )
            }
            // translcore.ml `Texp_object_literal`.
            ExpressionDesc::Texp_object_literal(fields) => {
                let labels = fields
                    .iter()
                    .map(|(s, _)| crate::types::external_ffi_types::ObjParam {
                        obj_arg_label: crate::types::external_ffi_types::Label::ObjLabel {
                            name: s.txt.clone(),
                        },
                        obj_arg_type: crate::types::external_ffi_types::Attr::Nothing,
                    })
                    .collect();
                let args = fields
                    .iter()
                    .map(|(_, field)| self.convert_expr_raw(field))
                    .collect();
                RawLambda::prim(
                    Primitive::PjsObjectCreate(labels),
                    args,
                    self.lam_loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_object_get(obj_expr, name) => RawLambda::prim(
                Primitive::PjsObjectGet(name.txt.clone()),
                vec![self.convert_expr_raw(obj_expr)],
                self.lam_loc(expr.exp_loc),
            ),
            ExpressionDesc::Texp_object_set(obj_expr, name, value) => {
                // OCaml evaluates the list literal `[transl_exp expr;
                // transl_exp value]` right to left.
                let value = self.convert_expr_raw(value);
                let obj = self.convert_expr_raw(obj_expr);
                RawLambda::prim(
                    Primitive::PjsObjectSet(name.txt.clone()),
                    vec![obj, value],
                    self.lam_loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_letmodule(id, _, modl, body) => RawLambda::let_(
                LetKind::Strict,
                *id,
                self.convert_module_expr_raw(modl, &None),
                self.convert_expr_raw(body),
            ),
            ExpressionDesc::Texp_letexception(ext, body) => RawLambda::let_(
                LetKind::Strict,
                ext.ext_id,
                self.transl_extension_constructor_raw(None, ext),
                self.convert_expr_raw(body),
            ),
            ExpressionDesc::Texp_extension_constructor(_, path) => {
                self.translate_extension_path_raw(path, SrcLoc::from(expr.exp_loc))
            }
            ExpressionDesc::Texp_pack(modl) => self.convert_module_expr_for_pack_raw(modl),
            ExpressionDesc::Texp_assert(inner_expr) => {
                if matches!(
                    inner_expr.exp_desc,
                    ExpressionDesc::Texp_construct(_, ref cstr, ref args)
                        if cstr.cstr_name == "false" && args.is_empty()
                ) {
                    self.raw_assert_false(expr.exp_loc)
                } else if self.noassert {
                    // OCaml translcore.ml:926-931 handles `assert false`
                    // first, then lowers ordinary assertions to unit under
                    // Clflags.noassert.
                    RawLambda::unit()
                } else {
                    let failure = self.raw_assert_failed(expr.exp_loc);
                    RawLambda::LifThenElse(
                        Box::new(self.convert_expr_raw(inner_expr)),
                        Box::new(RawLambda::unit()),
                        Box::new(failure),
                    )
                }
            }
        }
    }

    fn convert_constant(&self, cst: &TConstant) -> Constant {
        match cst {
            TConstant::Int(i) => i32::try_from(*i)
                .map(|i| Constant::Int { i, comment: None })
                .unwrap_or(Constant::NativeInt {
                    i: *i,
                    comment: None,
                }),
            TConstant::Char(c) => Constant::Char(*c),
            // lambda.ml `const_of_typed`: `Const_string s -> Const_string s`.
            TConstant::String(s) => Constant::String(s.clone()),
            TConstant::Float(f) => Constant::Float(f.clone()),
            TConstant::BigInt(positive, v) => Constant::BigInt {
                negative: !*positive,
                value: v.clone(),
            },
        }
    }

    /// Use the full matching compiler (matching.rs) for patterns that
    /// the simple matchers can't handle.
    fn compile_full_matching(
        &mut self,
        loc: LocIdx,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> RawLambda {
        let pat_act_list = self.cases_to_pat_act_list(cases);

        // OCaml optimization: when the scrutinee is a tuple, decompose into
        // individual arguments and use for_multiple_match, which can flatten
        // the tuple pattern matching without allocating a tuple.
        // (See OCaml's translcore.ml lines 1259-1260)
        if let ExpressionDesc::Texp_tuple(argl) = &scrut.exp_desc {
            let paraml: Vec<RawLambda> = argl.iter().map(|a| self.convert_expr_raw(a)).collect();
            return self.for_multiple_match_with_synced_stamps(loc, paraml, pat_act_list, partial);
        }

        let scrut_lam = self.convert_expr_raw(scrut);

        let loc_for_handler = self.loc(loc);
        let node_loc = self.lam_loc(loc);
        let fname = self.basename_for_loc(loc_for_handler);
        let arena = self.arena;
        let handler_fun = || {
            arena.require_locations();
            let line = loc_for_handler.loc_start.line;
            let char_pos = loc_for_handler.loc_start.column();
            let match_failure_ident =
                predef_exception_ident("Match_failure", PREDEF_MATCH_FAILURE_STAMP);
            let exn = RawLambda::global_module(match_failure_ident);
            let payload = RawLambda::Lconst(Constant::Block {
                tag_info: Box::new(TagInfo::Tuple),
                elements: vec![
                    Constant::const_string(&fname),
                    Constant::int(line),
                    Constant::int(char_pos),
                ],
            });
            RawLambda::Lprim(Box::new(RawPrimInfo {
                primitive: Primitive::Praise,
                args: vec![RawLambda::Lprim(Box::new(RawPrimInfo {
                    primitive: Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
                    args: vec![exn, payload],
                    loc: node_loc,
                }))],
                loc: node_loc,
            }))
        };
        self.compile_matching_with_synced_stamps(handler_fun, scrut_lam, pat_act_list, partial)
    }

    /// Compile a Texp_match with exception cases.
    /// Matches OCaml's transl_match from translcore.ml.
    ///
    /// Structure:
    ///   Lstaticcatch(
    ///     Ltrywith(
    ///       Lstaticraise(static_id, [scrut_value]),
    ///       exn_id,
    ///       for_trywith(exn_id, exn_cases)
    ///     ),
    ///     (static_id, [val_id]),
    ///     for_function(val_id, normal_cases)
    ///   )
    fn compile_match_with_exceptions_raw(
        &mut self,
        loc: LocIdx,
        scrut: &Expression,
        cases: &[Case],
        exn_cases: &[Case],
        partial: Partial,
        _expr: &Expression,
        exn_id: Ident,
    ) -> RawLambda {
        let val_id = self.name_pattern_ident("val", cases);

        // OCaml evaluates the `static_catch [transl_exp arg] ...` scrutinee
        // before Matching.for_trywith builds the exception handler
        // (translcore.ml:1266-1271). In particular, value-path normalization
        // may force a persistent ps_sig and allocate its substituted binders
        // before Matching allocates extension-switch temporaries.
        let scrut_lam = self.convert_expr_raw(scrut);

        // Compile the exception handler: matching on the exception.
        let exn_handler = self.compile_trywith_handler_raw(&exn_id, exn_cases);
        let (exn_id, exn_handler) = self.pack_trywith_exn(exn_id, exn_handler);

        // Compile normal cases with val_id as the scrutinee
        let normal_handler = {
            // Note: do NOT allocate a raise_count here for Partial matches.
            // compile_matching allocates its own raise_num internally.
            let pat_act_list = self.cases_to_pat_act_list(cases);
            let loc_for_handler = self.loc(loc);
            let node_loc = self.lam_loc(loc);
            let fname = self.basename_for_loc(loc_for_handler);
            let arena = self.arena;
            let handler_fun = || {
                arena.require_locations();
                let line = loc_for_handler.loc_start.line;
                let char_pos = loc_for_handler.loc_start.column();
                let match_failure_ident =
                    predef_exception_ident("Match_failure", PREDEF_MATCH_FAILURE_STAMP);
                let exn = RawLambda::global_module(match_failure_ident);
                let payload = RawLambda::Lconst(Constant::Block {
                    tag_info: Box::new(TagInfo::Tuple),
                    elements: vec![
                        Constant::const_string(&fname),
                        Constant::int(line),
                        Constant::int(char_pos),
                    ],
                });
                RawLambda::Lprim(Box::new(RawPrimInfo {
                    primitive: Primitive::Praise,
                    args: vec![RawLambda::Lprim(Box::new(RawPrimInfo {
                        primitive: Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
                        args: vec![exn, payload],
                        loc: node_loc,
                    }))],
                    loc: node_loc,
                }))
            };
            self.compile_matching_with_synced_stamps(
                handler_fun,
                RawLambda::var(val_id),
                pat_act_list,
                partial,
            )
        };

        // Build the structure:
        // Lstaticcatch(
        //   Ltrywith(Lstaticraise(id, [scrut_value]), exn_id, exn_handler),
        //   (id, [val_id]),
        //   normal_handler
        // )
        let static_exception_id = self.next_negative_raise_count();

        let try_body = RawLambda::LstaticRaise(static_exception_id, vec![scrut_lam]);
        let try_with = RawLambda::LtryWith(Box::new(try_body), exn_id, Box::new(exn_handler));
        RawLambda::LstaticCatch(
            Box::new(try_with),
            (static_exception_id, vec![val_id]),
            Box::new(normal_handler),
        )
    }

    /// Compile try-with exception handler from exception cases.
    /// Matches OCaml's Matching.for_trywith.
    fn compile_trywith_handler_raw(&mut self, exn_id: &Ident, exn_cases: &[Case]) -> RawLambda {
        let pat_act_list = self.cases_to_pat_act_list(exn_cases);
        self.for_trywith_with_synced_stamps(RawLambda::var(*exn_id), pat_act_list)
    }

    fn compile_irrefutable_match_raw(
        &mut self,
        scrut: &Expression,
        cases: &[Case],
    ) -> Option<RawLambda> {
        if cases.len() != 1 || cases[0].c_guard.is_some() {
            return None;
        }

        if !self.is_irrefutable_pattern(&cases[0].c_lhs) {
            return None;
        }

        let body = self.convert_expr_raw(&cases[0].c_rhs);
        let scrut_lam = self.convert_expr_raw(scrut);

        // OCaml's compile_matching uses args=[(arg, Strict)], which means
        // when arg_to_var creates a temp for a non-variable scrutinee, it
        // gets a Strict binding. Match this for non-trivial patterns.
        match (&cases[0].c_lhs.pat_desc, &scrut_lam) {
            (PatternDesc::Tpat_var(_, _), _) | (_, RawLambda::Lvar(_)) => {
                // Simple var pattern or variable scrutinee — no wrapping needed
                Some(self.bind_irrefutable_pattern_raw(&cases[0].c_lhs, scrut_lam, body))
            }
            _ => {
                // Non-variable scrutinee with complex pattern (record, tuple, etc.)
                // OCaml's compile_matching binds with Strict via arg_to_var
                let match_id = self.fresh_ident("match");
                let bound = self.bind_irrefutable_pattern_raw(
                    &cases[0].c_lhs,
                    RawLambda::Lvar(match_id),
                    body,
                );
                Some(RawLambda::let_(LetKind::Strict, match_id, scrut_lam, bound))
            }
        }
    }

    fn bind_constructor_args_irrefutably_raw(
        &mut self,
        scrut_id: &Ident,
        pat: &Pattern,
        cstr: &crate::types::ConstructorDescription,
        args: &[Pattern],
        body: RawLambda,
    ) -> RawLambda {
        if cstr.cstr_inlined.is_some() {
            return match args {
                [arg_pat] => {
                    self.bind_irrefutable_pattern_raw(arg_pat, RawLambda::var(*scrut_id), body)
                }
                [] => body,
                _ => RawLambda::unit(),
            };
        }

        let pat_loc = pat.pat_loc;
        let mut result = body;

        if constructor_has_optional_shape(cstr) {
            if let [arg_pat] = args {
                let from_option = self
                    .type_ctx
                    .get_typed_env(arg_pat.pat_env)
                    .map(|env| {
                        if type_cannot_contain_undefined(
                            self.type_ctx,
                            env.as_ref(),
                            arg_pat.pat_type,
                        ) {
                            Primitive::PvalFromOptionNotNest
                        } else {
                            Primitive::PvalFromOption
                        }
                    })
                    .unwrap_or_else(|| {
                        if type_cannot_contain_undefined_no_env(self.type_ctx, arg_pat.pat_type) {
                            Primitive::PvalFromOptionNotNest
                        } else {
                            Primitive::PvalFromOption
                        }
                    });
                let payload = RawLambda::prim(
                    from_option,
                    vec![RawLambda::var(*scrut_id)],
                    self.lam_loc(pat_loc),
                );
                // For Tpat_any, OCaml's matching.ml still creates a binding
                if matches!(arg_pat.pat_desc, PatternDesc::Tpat_any) {
                    let match_id = self.fresh_ident("match");
                    result = RawLambda::let_(LetKind::Alias, match_id, payload, result);
                } else {
                    // matching.ml:2407-2410 (`lower_bind`): eliminates
                    // `let v = val_from_option(x) in v`.
                    if let PatternDesc::Tpat_var(id, _) = &arg_pat.pat_desc
                        && let RawLambda::Lvar(body_id) = &result
                        && body_id.same(id)
                    {
                        return payload;
                    }
                    result = self.bind_irrefutable_pattern_raw(arg_pat, payload, result);
                }
                return result;
            }
        }

        for (idx, arg_pat) in args.iter().enumerate() {
            let field = match cstr.cstr_kind {
                crate::types::ConstructorKind::Ordinary(reference) => {
                    match reference.representation(self.type_ctx) {
                        crate::types::VariantConstructorCase::Block(block)
                            if block.is_untagged() =>
                        {
                            RawLambda::var(*scrut_id)
                        }
                        crate::types::VariantConstructorCase::Block(_) => RawLambda::prim(
                            Primitive::Pfield(
                                idx as i32,
                                if cstr.cstr_name == "::" {
                                    FieldDbgInfo::Cons
                                } else {
                                    FieldDbgInfo::Variant
                                },
                            ),
                            vec![RawLambda::var(*scrut_id)],
                            self.lam_loc(pat_loc),
                        ),
                        crate::types::VariantConstructorCase::Constant(_) => {
                            unreachable!("constant constructor payload")
                        }
                    }
                }
                crate::types::ConstructorKind::Extension(_) => RawLambda::prim(
                    Primitive::Pfield(idx as i32 + 1, FieldDbgInfo::Extension),
                    vec![RawLambda::var(*scrut_id)],
                    self.lam_loc(pat_loc),
                ),
            };
            // For Tpat_any, OCaml's matching.ml still creates a binding
            // (let (match/N =a (field:var/K scrut)) body). Match this behavior.
            if matches!(arg_pat.pat_desc, PatternDesc::Tpat_any) {
                let match_id = self.fresh_ident("match");
                result = RawLambda::let_(LetKind::Alias, match_id, field, result);
            } else {
                result = self.bind_irrefutable_pattern_raw(arg_pat, field, result);
            }
        }

        result
    }

    fn is_irrefutable_pattern(&self, pat: &Pattern) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
            PatternDesc::Tpat_alias(inner, _, _) => self.is_irrefutable_pattern(inner),
            PatternDesc::Tpat_tuple(items) => {
                items.iter().all(|pat| self.is_irrefutable_pattern(pat))
            }
            // OCaml `Parmatch.irrefutable` = `le_pat pat omega`, which falls back to
            // `satisfiable` for arrays: an array pattern never covers every length.
            PatternDesc::Tpat_array(_) => false,
            PatternDesc::Tpat_record(fields, _, _) => fields
                .iter()
                .all(|(_, _, pat, _)| self.is_irrefutable_pattern(pat)),
            PatternDesc::Tpat_construct(_, cstr, args) => match cstr.cstr_kind {
                crate::types::ConstructorKind::Extension(_) => false,
                crate::types::ConstructorKind::Ordinary(reference) => {
                    let has_one_constructor = self
                        .type_ctx
                        .with_variant_layout(reference.variant, |layout| {
                            layout.constructors.len() == 1
                        });
                    match reference.representation(self.type_ctx) {
                        crate::types::VariantConstructorCase::Constant(_) => {
                            args.is_empty() && has_one_constructor
                        }
                        crate::types::VariantConstructorCase::Block(_) => {
                            has_one_constructor
                                && args.iter().all(|pat| self.is_irrefutable_pattern(pat))
                        }
                    }
                }
            },
            PatternDesc::Tpat_variant(_, Some(inner), _) => self.is_irrefutable_pattern(inner),
            PatternDesc::Tpat_variant(_, None, _) => false,
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_or(_, _, _) => false,
        }
    }

    fn bind_irrefutable_pattern_raw(
        &mut self,
        pat: &Pattern,
        scrut: RawLambda,
        body: RawLambda,
    ) -> RawLambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_var(id, _) => {
                // OCaml's bind_check: skip binding when scrut is already the same variable
                if let RawLambda::Lvar(v) = &scrut {
                    if v.same(id) {
                        return body;
                    }
                }
                RawLambda::let_(LetKind::Alias, *id, scrut, body)
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner = self.bind_irrefutable_pattern_raw(inner, scrut.clone(), body);
                // OCaml's bind_check: skip binding when scrut is already the same variable
                if let RawLambda::Lvar(v) = &scrut {
                    if v.same(id) {
                        return inner;
                    }
                }
                RawLambda::let_(LetKind::Alias, *id, scrut, inner)
            }
            PatternDesc::Tpat_tuple(items) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.fresh_ident("match");
                        (tmp, Some((tmp, scrut)))
                    }
                };
                let pat_loc = pat.pat_loc;
                let mut result = body;
                for (idx, item) in items.iter().enumerate() {
                    let field = RawLambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![RawLambda::var(tmp)],
                        self.lam_loc(pat_loc),
                    );
                    // OCaml's make_tuple_matching always generates field access
                    // for ALL positions, even wildcards. The wildcard gets a
                    // fresh "match" ident that's never used.
                    if matches!(item.pat_desc, PatternDesc::Tpat_any) {
                        let match_id = self.fresh_ident("match");
                        result = RawLambda::let_(LetKind::Alias, match_id, field, result);
                    } else {
                        result = self.bind_irrefutable_pattern_raw(item, field, result);
                    }
                }
                match wrap_tmp {
                    // OCaml's bind_check uses Alias for field accesses (pure expressions),
                    // Strict for computations.
                    Some((tmp, scrut)) => {
                        let kind = if matches!(&scrut, RawLambda::Lprim(info) if matches!(info.primitive, Primitive::Pfield(_, _)))
                        {
                            LetKind::Alias
                        } else {
                            LetKind::Strict
                        };
                        RawLambda::let_(kind, tmp, scrut, result)
                    }
                    None => result,
                }
            }
            PatternDesc::Tpat_record(fields, _, rest) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.fresh_ident("match");
                        (tmp, Some((tmp, scrut)))
                    }
                };
                let mut result = match rest {
                    Some(rest) => RawLambda::let_(
                        LetKind::Strict,
                        rest.rest_ident,
                        RawLambda::prim(
                            Primitive::PrecordRest(rest.excluded_runtime_labels.clone()),
                            vec![RawLambda::var(tmp)],
                            self.lam_loc(pat.pat_loc),
                        ),
                        body,
                    ),
                    None => body,
                };

                // OCaml's make_record_matching binds ALL fields (from lbl_all),
                // not just the ones mentioned in the pattern.
                // Build a map of pattern-mentioned positions.
                let mut mentioned: HashMap<
                    i32,
                    (
                        &crate::types::typedtree::Loc<LidentIdx>,
                        &LabelDescription,
                        &Pattern,
                    ),
                > = HashMap::new();
                for (lid, lbl, inner_pat, _) in fields.iter() {
                    mentioned.insert(lbl.lbl_pos, (lid, lbl, inner_pat));
                }

                // Try to resolve all labels for this record type
                let first_lbl = fields.first().map(|(_, lbl, _, _)| lbl);
                let all_labels =
                    first_lbl.and_then(|lbl| self.resolve_all_record_labels(lbl.lbl_res));
                let pat_loc_idx = pat.pat_loc;

                if let Some(all_labels) = all_labels {
                    // Handle unboxed records separately (field IS the scrutinee)
                    if all_labels.iter().any(|(_, _, _, repr, _)| {
                        matches!(repr, RecordRepresentation::RecordUnboxed(_))
                    }) {
                        for (_, pos, _, repr, _) in all_labels.iter() {
                            if !matches!(repr, RecordRepresentation::RecordUnboxed(_)) {
                                continue;
                            }
                            if let Some((_, _, inner_pat)) = mentioned.get(pos) {
                                let field = RawLambda::var(tmp);
                                if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                                    result = RawLambda::let_(LetKind::Alias, *id, field, result);
                                } else {
                                    result =
                                        self.bind_irrefutable_pattern_raw(inner_pat, field, result);
                                }
                            }
                        }
                    } else {
                        // Collect non-skipped field indices and their let-kinds.
                        // OCaml's compile_match processes fields in position order (0..N),
                        // then bind_check uses lower_bind for Alias fields which pushes
                        // them past existing Alias Llets. StrictOpt (mutable) fields stay
                        // at the outermost position. We simulate this reordering here.
                        let mut field_indices: Vec<(usize, LetKind)> = Vec::new();
                        for (idx, (_, _, mutflag, repr, _)) in all_labels.iter().enumerate() {
                            if matches!(repr, RecordRepresentation::RecordFloatUnused) {
                                continue;
                            }
                            let kind = if matches!(mutflag, TypeMutableFlag::Mutable) {
                                LetKind::StrictOpt
                            } else {
                                LetKind::Alias
                            };
                            field_indices.push((idx, kind));
                        }

                        // Compute OCaml's output order (outermost first).
                        // OCaml's compile_match unwinds from last field to first:
                        // - StrictOpt: wraps outside everything (insert at front)
                        // - Alias: lower_bind pushes past leading Alias entries
                        //   (insert at first non-Alias position)
                        let mut ocaml_order: Vec<(usize, LetKind)> = Vec::new();
                        for &(idx, kind) in field_indices.iter().rev() {
                            if kind == LetKind::StrictOpt {
                                ocaml_order.insert(0, (idx, kind));
                            } else {
                                // Alias: find position of first non-Alias entry
                                let insert_pos = ocaml_order
                                    .iter()
                                    .position(|(_, k)| *k != LetKind::Alias)
                                    .unwrap_or(ocaml_order.len());
                                ocaml_order.insert(insert_pos, (idx, kind));
                            }
                        }

                        // Iterate in REVERSE of ocaml_order for inside-out wrapping.
                        // Last in ocaml_order (innermost) is wrapped first.
                        for &(idx, _) in ocaml_order.iter().rev() {
                            let (name, pos, mutflag, repr, _) = &all_labels[idx];

                            let field_pos = match repr {
                                RecordRepresentation::RecordExtension => pos + 1,
                                _ => *pos,
                            };
                            let info = match repr {
                                RecordRepresentation::RecordRegular => {
                                    FieldDbgInfo::Record { name: name.clone() }
                                }
                                RecordRepresentation::RecordFloatUnused => continue,
                                RecordRepresentation::RecordInlined { .. } => {
                                    FieldDbgInfo::RecordInline { name: name.clone() }
                                }
                                RecordRepresentation::RecordExtension => {
                                    FieldDbgInfo::RecordExtension { name: name.clone() }
                                }
                                RecordRepresentation::RecordUnboxed(_) => unreachable!(),
                            };
                            let field_let_kind = if matches!(mutflag, TypeMutableFlag::Mutable) {
                                LetKind::StrictOpt
                            } else {
                                LetKind::Alias
                            };

                            let loc = if let Some((lid, _, _)) = mentioned.get(pos) {
                                lid.loc
                            } else {
                                pat_loc_idx
                            };

                            let field = RawLambda::prim(
                                Primitive::Pfield(field_pos, info),
                                vec![RawLambda::var(tmp)],
                                self.lam_loc(loc),
                            );

                            if let Some((_, _, inner_pat)) = mentioned.get(pos) {
                                // Mentioned in pattern: bind using the pattern's variable
                                if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                                    result = RawLambda::let_(field_let_kind, *id, field, result);
                                } else {
                                    result =
                                        self.bind_irrefutable_pattern_raw(inner_pat, field, result);
                                }
                            } else {
                                // Not mentioned: bind to a fresh match/N variable (OCaml's omega pattern)
                                let fresh = self.fresh_ident("match");
                                result = RawLambda::let_(field_let_kind, fresh, field, result);
                            }
                        }
                    }
                } else {
                    // Fallback: bind only mentioned fields (can't resolve all labels)
                    for (lid, lbl, inner_pat, _) in fields.iter() {
                        let field = match &lbl.lbl_repres {
                            RecordRepresentation::RecordUnboxed(_) => RawLambda::var(tmp),
                            _ => {
                                let Some((pos, info)) = raw_record_field_access(lbl) else {
                                    continue;
                                };
                                RawLambda::prim(
                                    Primitive::Pfield(pos, info),
                                    vec![RawLambda::var(tmp)],
                                    self.lam_loc(lid.loc),
                                )
                            }
                        };
                        let field_let_kind = if matches!(lbl.lbl_mut, TypeMutableFlag::Mutable) {
                            LetKind::StrictOpt
                        } else {
                            LetKind::Alias
                        };
                        if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                            result = RawLambda::let_(field_let_kind, *id, field, result);
                        } else {
                            result = self.bind_irrefutable_pattern_raw(inner_pat, field, result);
                        }
                    }
                }

                match wrap_tmp {
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_array(items) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.fresh_ident("array");
                        (tmp, Some((tmp, scrut)))
                    }
                };
                let pat_loc = pat.pat_loc;
                let mut result = body;
                for (idx, item) in items.iter().enumerate() {
                    let field = RawLambda::prim(
                        Primitive::Parrayrefs,
                        vec![
                            RawLambda::var(tmp),
                            RawLambda::const_(Constant::int(idx as i32)),
                        ],
                        self.lam_loc(pat_loc),
                    );
                    result = self.bind_irrefutable_pattern_raw(item, field, result);
                }
                match wrap_tmp {
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if constructor_payload_is_unboxed(self.type_ctx, cstr) =>
            {
                args.first().map_or(body.clone(), |arg| {
                    self.bind_irrefutable_pattern_raw(arg, scrut, body)
                })
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(
                    constructor_case(self.type_ctx, cstr),
                    Some(crate::types::VariantConstructorCase::Constant(_))
                ) && args.is_empty() =>
            {
                body
            }
            PatternDesc::Tpat_construct(_, cstr, args) => {
                // Single-constructor block type: bind fields directly from scrutinee
                let (scrut_id, wrap_let) = match &scrut {
                    RawLambda::Lvar(id) => (*id, None),
                    _ => {
                        let id = self.fresh_ident("match");
                        (id, Some((id, scrut)))
                    }
                };
                let result =
                    self.bind_constructor_args_irrefutably_raw(&scrut_id, pat, cstr, args, body);
                match wrap_let {
                    Some((id, value)) => RawLambda::let_(LetKind::Alias, id, value, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_variant(_, Some(inner), _) => {
                let payload = RawLambda::prim(
                    Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                    vec![scrut],
                    self.lam_loc(pat.pat_loc),
                );
                self.bind_irrefutable_pattern_raw(inner, payload, body)
            }
            _ => unreachable!("expected irrefutable pattern"),
        }
    }

    fn convert_let_with_body_raw(
        &mut self,
        rec_flag: crate::parser::ast::RecFlag,
        bindings: &[ValueBinding],
        body: RawLambda,
    ) -> RawLambda {
        self.convert_let_with_body_raw_at_root(rec_flag, bindings, body, &None)
    }

    fn convert_let_with_body_raw_at_root(
        &mut self,
        rec_flag: crate::parser::ast::RecFlag,
        bindings: &[ValueBinding],
        body: RawLambda,
        rootpath: &Option<crate::types::Path>,
    ) -> RawLambda {
        match rec_flag {
            crate::parser::ast::RecFlag::Nonrecursive => {
                if bindings.iter().any(|binding| {
                    simple_let_binding_id(binding).is_none()
                        && !self.is_irrefutable_pattern(&binding.vb_pat)
                }) {
                    // Use OCaml's simple_for_let / for_let approach via full matching compiler
                    let converted_bindings = bindings
                        .iter()
                        .map(|binding| {
                            let mut value = self
                                .with_warning_scope(&binding.vb_attributes, |this| {
                                    this.convert_expr_raw(&binding.vb_expr)
                                });
                            let inline_attr =
                                self.get_inline_attribute_from(&binding.vb_attributes);
                            value =
                                self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                            self.mark_js_hoisted_pattern(
                                rootpath,
                                &binding.vb_attributes,
                                &binding.vb_pat,
                                &value,
                                binding.vb_expr.exp_loc,
                            );
                            (binding, value)
                        })
                        .collect::<Vec<_>>();
                    let mut acc = body;
                    for (binding, value) in converted_bindings.into_iter().rev() {
                        if let Some(id) = simple_let_binding_id(binding) {
                            if nonrecursive_alias_any_binding(binding) {
                                self.next_raise_count();
                            }
                            let kind = match &binding.vb_pat.pat_desc {
                                PatternDesc::Tpat_alias(inner, _, _)
                                    if matches!(inner.pat_desc, PatternDesc::Tpat_any)
                                        && matches!(value, RawLambda::Lvar(_)) =>
                                {
                                    LetKind::Alias
                                }
                                _ => LetKind::Strict,
                            };
                            acc = RawLambda::let_(kind, id, value, acc);
                        } else {
                            // Use matching compiler's for_let (OCaml: Matching.for_let)
                            let pat_act_list = vec![(&binding.vb_pat, acc.into())];
                            let loc = binding.vb_pat.pat_loc;
                            let loc_for_handler = self.loc(loc);
                            let fname = self.basename_for_loc(loc_for_handler);
                            let arena = self.arena;
                            let handler_fun = move || {
                                arena.require_locations();
                                let line = loc_for_handler.loc_start.line;
                                let char_pos = loc_for_handler.loc_start.column();
                                let match_failure_ident = predef_exception_ident(
                                    "Match_failure",
                                    PREDEF_MATCH_FAILURE_STAMP,
                                );
                                let exn = RawLambda::global_module(match_failure_ident);
                                let payload = RawLambda::Lconst(Constant::Block {
                                    tag_info: Box::new(TagInfo::Tuple),
                                    elements: vec![
                                        Constant::const_string(&fname),
                                        Constant::int(line),
                                        Constant::int(char_pos),
                                    ],
                                });
                                RawLambda::Lprim(Box::new(RawPrimInfo {
                                    primitive: Primitive::Praise,
                                    args: vec![RawLambda::Lprim(Box::new(RawPrimInfo {
                                        primitive: Primitive::Pmakeblock(
                                            TagInfo::Extension,
                                            Mutable::Immutable,
                                        ),
                                        args: vec![exn, payload],
                                        loc: LamLoc::NONE,
                                    }))],
                                    loc: LamLoc::NONE,
                                }))
                            };
                            acc = self.compile_matching_with_synced_stamps(
                                handler_fun,
                                value,
                                pat_act_list,
                                Partial::Partial,
                            );
                        }
                    }
                    return acc;
                }

                let converted_bindings = bindings
                    .iter()
                    .map(|binding| {
                        let mut value = self.with_warning_scope(&binding.vb_attributes, |this| {
                            this.convert_expr_raw(&binding.vb_expr)
                        });
                        // OCaml's transl_let applies inline attributes from vb_attributes
                        let inline_attr = self.get_inline_attribute_from(&binding.vb_attributes);
                        value = self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                        self.mark_js_hoisted_pattern(
                            rootpath,
                            &binding.vb_attributes,
                            &binding.vb_pat,
                            &value,
                            binding.vb_expr.exp_loc,
                        );
                        (binding, value)
                    })
                    .collect::<Vec<_>>();
                let mut acc = body;
                for (binding, value) in converted_bindings.into_iter().rev() {
                    if let Some(id) = simple_let_binding_id(binding) {
                        if nonrecursive_alias_any_binding(binding) {
                            self.next_raise_count();
                        }
                        let kind = match &binding.vb_pat.pat_desc {
                            PatternDesc::Tpat_alias(inner, _, _)
                                if matches!(inner.pat_desc, PatternDesc::Tpat_any)
                                    && matches!(value, RawLambda::Lvar(_)) =>
                            {
                                LetKind::Alias
                            }
                            _ => LetKind::Strict,
                        };
                        acc = RawLambda::let_(kind, id, value, acc);
                    } else if self.is_irrefutable_pattern(&binding.vb_pat) {
                        acc = self.for_let_with_synced_stamps(
                            binding.vb_pat.pat_loc,
                            value,
                            &binding.vb_pat,
                            acc,
                        );
                    }
                }
                acc
            }
            crate::parser::ast::RecFlag::Recursive => {
                if bindings
                    .iter()
                    .all(|binding| simple_let_binding_id(binding).is_some())
                {
                    let lam_bindings = bindings
                        .iter()
                        .map(|binding| {
                            let mut value = self
                                .with_warning_scope(&binding.vb_attributes, |this| {
                                    this.convert_expr_raw(&binding.vb_expr)
                                });
                            let inline_attr =
                                self.get_inline_attribute_from(&binding.vb_attributes);
                            value =
                                self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                            self.mark_js_hoisted_pattern(
                                rootpath,
                                &binding.vb_attributes,
                                &binding.vb_pat,
                                &value,
                                binding.vb_expr.exp_loc,
                            );
                            (
                                simple_let_binding_id(binding).expect("checked above"),
                                value,
                            )
                        })
                        .collect();
                    // translcore.ml `transl_let`: `Lambda_scc.bind_rec`.
                    crate::raw_lambda::lambda_scc::bind_rec(lam_bindings, body)
                } else {
                    bindings.iter().rev().fold(body, |acc, binding| {
                        let mut value = self.with_warning_scope(&binding.vb_attributes, |this| {
                            this.convert_expr_raw(&binding.vb_expr)
                        });
                        let inline_attr = self.get_inline_attribute_from(&binding.vb_attributes);
                        value = self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                        self.mark_js_hoisted_pattern(
                            rootpath,
                            &binding.vb_attributes,
                            &binding.vb_pat,
                            &value,
                            binding.vb_expr.exp_loc,
                        );
                        self.for_let_with_synced_stamps(
                            binding.vb_pat.pat_loc,
                            value,
                            &binding.vb_pat,
                            acc,
                        )
                    })
                }
            }
        }
    }

    /// Mirrors compiler/ml/translcore.ml:615-637 and `transl_function` for the
    /// upstream n-ary Typedtree representation.
    #[allow(clippy::too_many_arguments)]
    fn convert_nary_function_raw(
        &mut self,
        function: Option<&Expression>,
        params: &[FunctionParam],
        body: &Expression,
        async_: bool,
        directive: Option<String>,
        inline: InlineAttribute,
        loc: LocIdx,
    ) -> RawLambda {
        fn pattern_binds_value(pattern: &Pattern) -> bool {
            match &pattern.pat_desc {
                PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_alias(_, _, _) => true,
                PatternDesc::Tpat_tuple(items)
                | PatternDesc::Tpat_array(items)
                | PatternDesc::Tpat_construct(_, _, items) => items.iter().any(pattern_binds_value),
                PatternDesc::Tpat_variant(_, Some(item), _) => pattern_binds_value(item),
                PatternDesc::Tpat_record(fields, _, rest) => {
                    rest.is_some()
                        || fields
                            .iter()
                            .any(|(_, _, item, _)| pattern_binds_value(item))
                }
                PatternDesc::Tpat_or(left, right, _) => {
                    pattern_binds_value(left) || pattern_binds_value(right)
                }
                _ => false,
            }
        }

        let param_ids = params
            .iter()
            .map(|param| param.fp_param)
            .collect::<Vec<_>>();
        // `transl_function` (translcore.ml:1395-1409) evaluates its result
        // tuple right to left: `is_base_type body.exp_env body.exp_type
        // Predef.path_unit` runs before the body is translated.
        let return_unit = match self.env_for_expr(body) {
            Some(env) => self.is_base_type_with_env(body.exp_type, "unit", &env),
            None => self.is_base_type(body.exp_type, "unit"),
        };
        let mut lambda_body = self.convert_expr_raw(body);
        for param in params.iter().rev() {
            let pat = &param.fp_pat;
            let id = &param.fp_param;
            lambda_body = match &pat.pat_desc {
                PatternDesc::Tpat_any => lambda_body,
                PatternDesc::Tpat_var(bound, _) if bound.same(id) => lambda_body,
                _ => self.for_function_with_synced_stamps(
                    pat.pat_loc,
                    RawLambda::var(*id),
                    vec![(pat, lambda_body.into())],
                    param.fp_partial,
                ),
            };
        }
        // `one_unit_arg` (translcore.ml:1015-1022) is computed after
        // `transl_function`, from the function's own type in `e.exp_env`.
        let one_unit_arg = match params {
            [param] if !pattern_binds_value(&param.fp_pat) => {
                function.is_some_and(|function| self.function_takes_one_unit_arg(function))
            }
            _ => false,
        };
        RawLambda::function_(
            param_ids.len() as i32,
            param_ids,
            lambda_body,
            FunctionAttribute {
                return_unit,
                async_,
                directive,
                inline,
                one_unit_arg,
                is_a_functor: false,
            },
            self.lam_loc(loc),
        )
    }

    /// The `one_unit_arg` test of `Texp_function` (translcore.ml:1015-1022):
    /// the expanded function type takes one unlabelled argument whose
    /// expanded type is a `Pident` named `unit`.
    fn function_takes_one_unit_arg(&self, function: &Expression) -> bool {
        use crate::types::asttypes::ArgLabel;
        use crate::types::type_expr::TypeDesc;
        let env = self.env_for_expr(function);
        let env = env.as_deref().unwrap_or(self.env);
        let ctx = self.type_ctx;
        let fn_type = ctx.repr(crate::types::ctype::expand_head(
            ctx,
            env,
            function.exp_type,
        ));
        let arg_type = match &*ctx.get_desc(fn_type) {
            TypeDesc::Tarrow { args, .. } => match args.as_slice() {
                [arg] if matches!(arg.label(), ArgLabel::Nolabel) => arg.typ,
                _ => return false,
            },
            _ => return false,
        };
        let arg_type = ctx.repr(crate::types::ctype::expand_head(ctx, env, arg_type));
        matches!(
            &*ctx.get_desc(arg_type),
            TypeDesc::Tconstr { path, args, .. }
                if path.as_pident().is_some_and(|id| id.name() == "unit") && args.is_empty()
        )
    }

    fn convert_apply_raw(
        &mut self,
        loc_idx: LocIdx,
        loc: LocIdx,
        funct: &Expression,
        args: &[ApplyArg],
        partial: bool,
        transformed_jsx: bool,
    ) -> RawLambda {
        if let ExpressionDesc::Texp_ident(_, _, desc) = &funct.exp_desc {
            if let ValueKind::ValPrim(prim) = &desc.val_kind {
                let raw_name = Self::raw_primitive_name(&prim.prim_name);
                let prim_arity = prim.prim_arity.max(0) as usize;
                if args.len() >= prim_arity
                    && args
                        .iter()
                        .take(prim_arity)
                        .all(|arg| arg.expression.is_some())
                {
                    let (applied, rest) = args.split_at(prim_arity);
                    let applied_exprs = applied
                        .iter()
                        .map(|arg| arg.expression.as_ref().expect("checked above"))
                        .collect::<Vec<_>>();
                    if let Some(kind) = Self::raw_loc_kind(raw_name) {
                        let base = match applied {
                            [] => self.raw_loc_constant(kind, SrcLoc::from(loc)),
                            [arg] => {
                                let expr = arg.expression.as_ref().expect("checked above");
                                RawLambda::prim(
                                    Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                                    vec![
                                        self.raw_loc_constant(kind, SrcLoc::from(expr.exp_loc)),
                                        self.convert_expr_raw(expr),
                                    ],
                                    self.lam_loc(loc),
                                )
                            }
                            _ => RawLambda::unit(),
                        };
                        return if rest.is_empty() {
                            base
                        } else {
                            let inlined = self.get_inlined_attribute_from(&funct.exp_attributes);
                            self.transl_apply_raw(base, rest, loc, transformed_jsx, None, inlined)
                        };
                    }
                    let base = if matches!(raw_name, "%import" | "#import")
                        && let [arg] = applied_exprs.as_slice()
                    {
                        // translcore.ml:1030-1032
                        self.transl_dynamic_import(SrcLoc::from(loc), arg)
                    } else {
                        let arg_lams = applied_exprs
                            .iter()
                            .map(|expr| self.convert_expr_raw(expr))
                            .collect::<Vec<_>>();
                        match self.translate_primitive_application_raw(
                            prim,
                            funct.exp_type,
                            &applied_exprs,
                            SrcLoc::from(loc),
                        ) {
                            // an external: expand its FFI spec here; %raw
                            // parses and classifies its snippet
                            None => match (raw_name, arg_lams.as_slice()) {
                                ("#raw_expr" | "#raw_stmt", [code]) => {
                                    let code = match code {
                                        RawLambda::Lconst(Constant::String(s))
                                        | RawLambda::Lconst(Constant::ImmString(s)) => s.clone(),
                                        _ => unreachable!("%raw takes a string constant"),
                                    };
                                    RawLambda::prim(
                                        Primitive::PrawJsCode(
                                            crate::lambda::lam_primitive::JsRawInfo {
                                                code,
                                                is_stmt: raw_name == "#raw_stmt",
                                            },
                                        ),
                                        vec![],
                                        self.lam_loc(loc),
                                    )
                                }
                                _ => {
                                    let env = self.env_for_expr(funct);
                                    let env = env.as_deref().unwrap_or(self.env);
                                    self.transl_external_application(
                                        SrcLoc::from(loc),
                                        env,
                                        prim,
                                        desc.val_type,
                                        arg_lams,
                                        transformed_jsx,
                                    )
                                }
                            },
                            Some(primitive) => {
                                self.report_polymorphic_comparison_warning(
                                    loc_idx, &primitive, &arg_lams,
                                );
                                self.mk_builtin(primitive, arg_lams, SrcLoc::from(loc))
                            }
                        }
                    };
                    return if rest.is_empty() {
                        base
                    } else {
                        let inlined = self.get_inlined_attribute_from(&funct.exp_attributes);
                        self.transl_apply_raw(base, rest, loc, transformed_jsx, None, inlined)
                    };
                }
            }
        }

        let inlined = self.get_inlined_attribute_from(&funct.exp_attributes);
        let funct_lam =
            self.with_inlined_attribute_check_suppressed(|this| this.convert_expr_raw(funct));
        let uncurried_partial_application = if partial {
            self.env_for_expr(funct).and_then(|env| {
                self.get_function_arity_from_type(env.as_ref(), funct.exp_type)
                    .and_then(|arity| {
                        let real_args =
                            args.iter().filter(|arg| arg.expression.is_some()).count() as i32;
                        (arity > real_args).then_some(arity)
                    })
            })
        } else {
            None
        };
        self.transl_apply_raw(
            funct_lam,
            args,
            loc,
            transformed_jsx,
            uncurried_partial_application,
            inlined,
        )
    }

    fn transl_apply_raw(
        &mut self,
        lam: RawLambda,
        sargs: &[ApplyArg],
        loc: LocIdx,
        transformed_jsx: bool,
        uncurried_partial_application: Option<i32>,
        inlined: InlineAttribute,
    ) -> RawLambda {
        let loc = loc;
        fn lapply(
            loc: LamLoc,
            func: RawLambda,
            args: Vec<RawLambda>,
            transformed_jsx: bool,
            inlined: InlineAttribute,
        ) -> RawLambda {
            RawLambda::Lapply(Box::new(crate::raw_lambda::RawApply {
                ap_func: Box::new(func),
                ap_args: args,
                ap_info: ApInfo {
                    loc,
                    inlined,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: transformed_jsx,
            }))
        }

        fn is_simple(lam: &RawLambda) -> bool {
            matches!(lam, RawLambda::Lvar(_) | RawLambda::Lconst(_))
        }

        fn build_apply(
            conv: &mut RawLambdaConverter<'_>,
            lam: RawLambda,
            mut args_rev: Vec<(RawLambda, bool)>,
            mut pending: std::collections::VecDeque<(Option<RawLambda>, bool)>,
            loc: LamLoc,
            transformed_jsx: bool,
            inlined: InlineAttribute,
        ) -> RawLambda {
            match pending.pop_front() {
                Some((None, optional)) => {
                    let mut defs: Vec<(Ident, RawLambda)> = Vec::new();
                    let protect =
                        |conv: &mut RawLambdaConverter<'_>,
                         name: &str,
                         lam: RawLambda,
                         defs: &mut Vec<(Ident, RawLambda)>| {
                            if is_simple(&lam) {
                                lam
                            } else {
                                let id = conv.fresh_ident(name);
                                defs.push((id, lam));
                                RawLambda::var(id)
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
                            loc,
                            lam,
                            args_rev.into_iter().rev().map(|(arg, _)| arg).collect(),
                            transformed_jsx,
                            InlineAttribute::Default,
                        )
                    };
                    let handle = protect(conv, "func", applied, &mut defs);
                    let protected_tail = pending
                        .into_iter()
                        .map(|(arg, is_optional)| {
                            (
                                arg.map(|lam| protect(conv, "arg", lam, &mut defs)),
                                is_optional,
                            )
                        })
                        .collect::<std::collections::VecDeque<_>>();
                    let id_arg = conv.fresh_ident("param");
                    let mut next_args_rev = Vec::with_capacity(1 + remaining_args.len());
                    next_args_rev.push((RawLambda::var(id_arg), optional));
                    next_args_rev.extend(remaining_args);
                    let body = match build_apply(
                        conv,
                        handle,
                        next_args_rev,
                        protected_tail,
                        loc,
                        transformed_jsx,
                        inlined,
                    ) {
                        RawLambda::Lfunction(func) => {
                            RawLambda::Lfunction(Box::new(crate::raw_lambda::RawLFunction {
                                arity: func.arity + 1,
                                params: std::iter::once(id_arg).chain(func.params).collect(),
                                body: func.body,
                                attr: func.attr,
                                loc: func.loc,
                            }))
                        }
                        lam => RawLambda::function_(
                            1,
                            vec![id_arg],
                            lam,
                            FunctionAttribute::default(),
                            loc,
                        ),
                    };
                    defs.into_iter().fold(body, |body, (id, lam)| {
                        RawLambda::let_(LetKind::Strict, id, lam, body)
                    })
                }
                Some((Some(arg), optional)) => {
                    args_rev.insert(0, (arg, optional));
                    build_apply(conv, lam, args_rev, pending, loc, transformed_jsx, inlined)
                }
                None => lapply(
                    loc,
                    lam,
                    args_rev.into_iter().rev().map(|(arg, _)| arg).collect(),
                    transformed_jsx,
                    inlined,
                ),
            }
        }

        match uncurried_partial_application {
            Some(arity) => {
                let extra_arity = arity - sargs.len() as i32;
                let mut none_ids = Vec::new();
                let args = sargs
                    .iter()
                    .map(|arg| match &arg.expression {
                        Some(expr) => self.convert_expr_raw(expr),
                        None => {
                            let id = self.fresh_ident("none");
                            none_ids.push(id);
                            RawLambda::var(id)
                        }
                    })
                    .collect::<Vec<_>>();
                let extra_ids = (0..extra_arity)
                    .map(|_| self.fresh_ident("extra"))
                    .collect::<Vec<_>>();
                let mut ap_args = args;
                ap_args.extend(extra_ids.iter().cloned().map(RawLambda::var));
                let body = lapply(self.lam_loc(loc), lam, ap_args, transformed_jsx, inlined);
                RawLambda::function_(
                    (none_ids.len() + extra_ids.len()) as i32,
                    none_ids.into_iter().chain(extra_ids).collect(),
                    body,
                    FunctionAttribute::default(),
                    self.lam_loc(loc),
                )
            }
            None => {
                let pending = sargs
                    .iter()
                    .map(|arg| {
                        (
                            arg.expression
                                .as_ref()
                                .map(|expr| self.convert_expr_raw(expr)),
                            arg.label.is_optional(),
                        )
                    })
                    .collect::<Vec<_>>();
                build_apply(
                    self,
                    lam,
                    Vec::new(),
                    pending.into(),
                    self.lam_loc(loc),
                    transformed_jsx,
                    inlined,
                )
            }
        }
    }

    /// `Translcore.transl_primitive`: eta-expand a primitive used as a value.
    fn translate_primitive_raw_in_env(
        &mut self,
        loc: SrcLoc,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
        val_type: TypeExprRef,
        warn_loc: Option<LocIdx>,
    ) -> RawLambda {
        let raw_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some(kind) = Self::raw_loc_kind(raw_name) {
            let lam = self.raw_loc_constant(kind, loc);
            return match prim.prim_arity {
                0 => lam,
                1 => {
                    let param = self.fresh_ident("prim");
                    RawLambda::function_(
                        1,
                        vec![param],
                        RawLambda::prim(
                            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                            vec![lam, RawLambda::var(param)],
                            self.lam_loc(loc),
                        ),
                        FunctionAttribute::default(),
                        self.lam_loc(loc),
                    )
                }
                _ => RawLambda::unit(),
            };
        }
        // translcore.ml `erased_builtins`: `Constant` entries become
        // constants at translation. They are found by `specialize_primitive`
        // (translcore.ml:423-438), which first scrapes the type with
        // `is_function_type`; neither unified ops nor comparisons know these
        // names, so `find_builtin` returns the constant.
        if matches!(raw_name, "%null" | "#null" | "%undefined" | "#undefined")
            && prim.prim_arity == 0
        {
            self.is_function_type_with_env(ty, env);
            return RawLambda::const_(if matches!(raw_name, "%null" | "#null") {
                Constant::JsNull
            } else {
                Constant::JsUndefined { is_unit: false }
            });
        }
        let Some(primitive) = self.specialize_primitive_raw_with_env(prim, ty, env) else {
            if raw_name == "%import" || raw_name == "#import" {
                self.report_diagnostic(
                    self.loc(loc),
                    "Dynamic import must be applied directly to a module or a value from another module; it cannot be used as a first-class value.".to_string(),
                );
                return RawLambda::unit();
            }
            // an external: expand its FFI spec, eta-expanded to its arity
            if prim.prim_from_constructor || prim.prim_arity == 0 {
                return self.transl_external_application(loc, env, prim, val_type, vec![], false);
            }
            let params: Vec<Ident> = if prim.prim_arity == 1 {
                vec![self.fresh_ident("prim")]
            } else {
                (0..prim.prim_arity)
                    .map(|i| self.fresh_ident(&format!("prim{i}")))
                    .collect()
            };
            let args = params.iter().cloned().map(RawLambda::var).collect();
            let body = self.transl_external_application(loc, env, prim, val_type, args, false);
            return RawLambda::function_(
                prim.prim_arity,
                params,
                body,
                FunctionAttribute::default(),
                self.lam_loc(loc),
            );
        };
        if let Some(warn_loc) = warn_loc {
            self.report_polymorphic_comparison_warning(warn_loc, &primitive, &[]);
        }

        if prim.prim_from_constructor || prim.prim_arity == 0 {
            self.mk_builtin(primitive, vec![], loc)
        } else {
            let params = if prim.prim_arity == 1 {
                vec![self.fresh_ident("prim")]
            } else {
                let mut params = (0..prim.prim_arity)
                    .rev()
                    .map(|i| self.fresh_ident(&format!("prim{i}")))
                    .collect::<Vec<_>>();
                params.reverse();
                params
            };
            let args = params
                .iter()
                .cloned()
                .map(RawLambda::var)
                .collect::<Vec<_>>();
            let body = self.mk_builtin(primitive, args, loc);
            RawLambda::function_(
                prim.prim_arity,
                params,
                body,
                FunctionAttribute::default(),
                self.lam_loc(loc),
            )
        }
    }

    /// OCaml `Lambda.mk_builtin` (lambda.ml): builtins with no primitive form
    /// are erased at translation. `%identity` is its argument and `%ignore`
    /// sequences its argument with unit; every other primitive is built
    /// through the folding `Lambda.prim`.
    fn mk_builtin(&mut self, primitive: Primitive, args: Vec<RawLambda>, loc: SrcLoc) -> RawLambda {
        match primitive {
            Primitive::Pidentity => {
                let [arg] = <[RawLambda; 1]>::try_from(args).expect("%identity takes one argument");
                arg
            }
            // lambda.ml `mk_builtin`: `Eliminated Ignore` builds
            // `Lsequence (arg, lambda_unit)` directly, bypassing the folding
            // `Lambda.seq`. Keep it as `Pignore` so lowering does the same.
            Primitive::Pignore => {
                let [arg] = <[RawLambda; 1]>::try_from(args).expect("%ignore takes one argument");
                RawLambda::prim(Primitive::Pignore, vec![arg], self.lam_loc(loc))
            }
            primitive => RawLambda::prim_folded(primitive, args, self.lam_loc(loc)),
        }
    }

    fn raw_primitive_name(name: &str) -> &str {
        name.strip_suffix("[js]").unwrap_or(name)
    }
}

#[cfg(test)]
mod tests {
    fn test_signature_module_type(
        items: Vec<crate::types::SignatureItem>,
    ) -> crate::types::decl::ModuleType {
        crate::types::decl::ModuleType::MtySignature(std::sync::Arc::new(items))
    }

    use super::*;
    use crate::types::typedtree::EnvRef;

    use crate::context::IdGenerator;
    use crate::parse_arena::ParseArena;

    use crate::parser::ast::Attributes;

    use crate::types::env::initial_env;

    #[test]
    fn nullary_unboxed_constructor_keeps_constructor_metadata_in_raw_lambda() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let layout =
            crate::types::variant_runtime::plain_layout(&ctx, [("OnlyOne".to_string(), false)]);

        let cstr = crate::types::ConstructorDescription {
            cstr_name: "OnlyOne".to_string(),
            cstr_res: crate::types::TypeExprRef(0),
            cstr_existentials: Vec::new(),
            cstr_args: Vec::new(),
            cstr_arity: 0,
            cstr_kind: crate::types::ConstructorKind::Ordinary(
                crate::types::ConstructorReference {
                    variant: layout,
                    position: 0,
                },
            ),
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: crate::types::DeclLoc::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: None,
        };

        let lowered = converter.convert_construct_raw(SrcLoc::from(Location::none()), &cstr, &[]);

        assert!(matches!(
            lowered,
            RawLambda::Lconst(Constant::Constructor(crate::types::VariantTag { name, .. }))
                if name == "OnlyOne"
        ));
    }

    #[test]
    fn empty_inlined_record_constructor_keeps_inlined_record_metadata() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let layout = crate::types::variant_runtime::plain_layout(&ctx, [("B".to_string(), true)]);
        let representation = crate::types::ConstructorReference {
            variant: layout,
            position: 0,
        };

        let arg = Expression::new(
            ExpressionDesc::Texp_record {
                fields: vec![],
                extended_expression: None,
                empty_representation: None,
            },
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            EnvRef(0),
            Attributes::new(),
        );
        let cstr = crate::types::ConstructorDescription {
            cstr_name: "B".to_string(),
            cstr_res: crate::types::TypeExprRef(0),
            cstr_existentials: Vec::new(),
            cstr_args: Vec::new(),
            cstr_arity: 1,
            cstr_kind: crate::types::ConstructorKind::Ordinary(representation),
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: crate::types::DeclLoc::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: Some(Box::new(crate::types::TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: crate::types::decl::TypeKind::TypeRecord(
                    crate::types::decl::SharedVec::from(vec![]),
                    crate::types::decl::RecordRepresentation::RecordInlined {
                        name: "B".to_string(),
                        representation,
                    },
                ),
                type_private: crate::types::asttypes::PrivateFlag::Public,
                type_manifest: None,
                type_variance: vec![],
                type_newtype_level: None,
                type_loc: crate::types::DeclLoc::none(),
                type_attributes: vec![],
                type_immediate: false,
                type_representation: crate::types::TypeRepresentation::Boxed,
                type_inlined_types: vec![],
                type_path: None,
            })),
        };

        let lowered =
            converter.convert_construct_raw(SrcLoc::from(Location::none()), &cstr, &[arg]);

        assert!(matches!(
            lowered,
            RawLambda::Lconst(Constant::Block { tag_info, elements })
                if elements.is_empty()
                    && matches!(
                        &*tag_info,
                        TagInfo::RecordInlined {
                            name,
                            num_nonconst,
                            fields,
                            mutable_flag: ParserMutableFlag::Immutable,
                            ..
                        } if name == "B" && *num_nonconst == 1 && fields.is_empty()
                    )
        ));
    }

    fn try_handler_exit_id(raw: &RawLambda) -> Option<i32> {
        let RawLambda::LtryWith(_, _, handler) = raw else {
            return None;
        };
        // `pack_trywith_exn` binds the caught value around the handler.
        let handler = match handler.as_ref() {
            RawLambda::Llet(_, _, _, body) => body.as_ref(),
            handler => handler,
        };
        let RawLambda::LstaticCatch(_, (id, params), _) = handler else {
            return None;
        };
        if params.is_empty() { Some(*id) } else { None }
    }

    fn simple_extension_try(
        arena: &mut ParseArena,
        name: &str,
        body_value: i64,
        handler_value: i64,
    ) -> Expression {
        let lid = Located::mknoloc(arena.push_lident(name));
        let path = crate::types::Path::pident(Ident::create_persistent(name));
        let constructor = crate::types::ConstructorDescription {
            cstr_name: name.to_string(),
            cstr_res: crate::types::TypeExprRef(0),
            cstr_existentials: Vec::new(),
            cstr_args: Vec::new(),
            cstr_arity: 0,
            cstr_kind: crate::types::ConstructorKind::Extension(path.clone()),
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: crate::types::DeclLoc::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: None,
        };
        let case = Case::simple(
            Pattern::new(
                PatternDesc::Tpat_construct(lid, std::sync::Arc::new(constructor), Vec::new()),
                LocIdx::none(),
                crate::types::TypeExprRef(0),
                EnvRef(0),
                Attributes::new(),
            ),
            Expression::new(
                ExpressionDesc::Texp_constant(TConstant::Int(handler_value)),
                LocIdx::none(),
                crate::types::TypeExprRef(0),
                EnvRef(0),
                Attributes::new(),
            ),
        );
        Expression::new(
            ExpressionDesc::Texp_try(
                Box::new(Expression::new(
                    ExpressionDesc::Texp_constant(TConstant::Int(body_value)),
                    LocIdx::none(),
                    crate::types::TypeExprRef(0),
                    EnvRef(0),
                    Attributes::new(),
                )),
                vec![case],
            ),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            EnvRef(0),
            Attributes::new(),
        )
    }

    fn simple_value_binding(id: Ident, expr: Expression) -> ValueBinding {
        ValueBinding {
            vb_pat: Pattern::new(
                PatternDesc::Tpat_var(id, Located::mknoloc(id.name().to_string())),
                LocIdx::none(),
                crate::types::TypeExprRef(0),
                EnvRef(0),
                Attributes::new(),
            ),
            vb_expr: expr,
            vb_attributes: Attributes::new(),
            vb_loc: LocIdx::none(),
        }
    }

    #[test]
    fn function_expression_preserves_directive_attribute() {
        let mut arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let any_ty = ctx.new_var(None);

        let directive_expr = crate::parser::ast::Expression {
            pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_constant(
                arena.string_constant("'use memo'"),
            ),
            pexp_loc: LocIdx::none(),
            pexp_attributes: Attributes::new(),
        };
        let directive_expr_idx = arena.push_expr(directive_expr);
        let directive_attrs = Attributes::from_vec(vec![(
            Located::mknoloc(arena.intern_string("directive")),
            crate::parser::ast::Payload::PStr(Box::new(vec![crate::parser::ast::StructureItem {
                pstr_desc: crate::parser::ast::StructureItemDesc::Pstr_eval(Box::new((
                    directive_expr_idx,
                    Attributes::new(),
                ))),
                pstr_loc: LocIdx::none(),
            }])),
        )]);

        let param_id = Ident::create_local("name");
        let param_pat = Pattern::new(
            PatternDesc::Tpat_var(param_id, Located::mknoloc("name".to_string())),
            LocIdx::none(),
            any_ty,
            EnvRef(0),
            Attributes::new(),
        );
        let expr = Expression::new(
            ExpressionDesc::Texp_function {
                params: vec![FunctionParam {
                    fp_lbl: crate::types::ArgLabel::Nolabel,
                    fp_param: param_id,
                    fp_pat: param_pat,
                    fp_partial: Partial::Total,
                    fp_has_default: false,
                }],
                body: Box::new(Expression::new(
                    ExpressionDesc::Texp_constant(TConstant::Int(1)),
                    LocIdx::none(),
                    any_ty,
                    EnvRef(0),
                    Attributes::new(),
                )),
                async_: false,
            },
            LocIdx::none(),
            any_ty,
            EnvRef(0),
            directive_attrs,
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let RawLambda::Lfunction(func) = converter.convert_expr_raw(&expr) else {
            panic!("expected raw function");
        };
        assert_eq!(func.attr.directive.as_deref(), Some("'use memo'"));
    }

    #[test]
    fn indexed_producer_uses_one_generator_through_convert_lower_coerce_and_consumer() {
        let arena = ParseArena::new();
        let generator = std::sync::Arc::new(IdGenerator::with_start_stamp(100));
        let ctx = TypeContext::new(generator.clone());
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::with_id_generator_and_unit_name(
            &arena,
            &ctx,
            &env,
            ctx.id_generator(),
            "Fixture".into(),
        );
        assert!(converter.shares_id_generator(&generator));
        let primitive_type = ctx.new_var(None);
        let converted = converter.transl_primitive_raw(
            &crate::types::PrimitiveDescription {
                prim_name: "%addint".into(),
                prim_arity: 2,
                prim_kind: crate::types::decl::PrimKind::KindIntrinsic,
                prim_native_float: false,
                prim_from_constructor: false,
            },
            primitive_type,
            SrcLoc::from(Location::none()),
        );
        let RawLambda::Lfunction(function) = converted else {
            panic!("expected primitive conversion to allocate a wrapper")
        };
        assert_eq!(
            function
                .params
                .iter()
                .map(|id| (id.name(), id.stamp(), id.flags()))
                .collect::<Vec<_>>(),
            vec![
                ("prim0", 102, crate::ident::IdentFlags::NONE),
                ("prim1", 101, crate::ident::IdentFlags::NONE),
            ]
        );

        let export = Ident::new("value", 1, crate::ident::IdentFlags::NONE);
        let caught = Ident::new("caught", 7, crate::ident::IdentFlags::NONE);
        let raw = RawLambda::Lprim(Box::new(RawPrimInfo {
            primitive: Primitive::Pmakeblock(
                crate::lambda::TagInfo::ModuleExport(vec![export]),
                crate::lambda::lam_primitive::Mutable::Immutable,
            ),
            args: vec![RawLambda::LtryWith(
                Box::new(RawLambda::unit()),
                caught,
                Box::new(RawLambda::var(caught)),
            )],
            loc: LamLoc::NONE,
        }));
        let indexed_raw = converter.finish_indexed_raw(raw);
        let mut inline = |_: &Ident, _: &str| None;
        let mut arity = |_: &Ident, _: &str| None;
        let result =
            crate::lambda::lam_compile_main_indexed::lower_and_optimize_for_pre_js_indexed(
                indexed_raw,
                vec![export],
                &[],
                &ahash::AHashSet::new(),
                false,
                &mut inline,
                &mut arity,
            )
            .unwrap();
        assert_eq!(
            (
                result.exports()[0].name(),
                result.exports()[0].stamp(),
                result.exports()[0].flags()
            ),
            ("value", 103, crate::ident::IdentFlags::NONE)
        );
        let consumer = result.generator().create("consumer");
        assert_eq!(
            (consumer.name(), consumer.stamp(), consumer.flags()),
            ("consumer", 104, crate::ident::IdentFlags::NONE)
        );
        assert_eq!(generator.current_stamp(), 104);
    }

    #[test]
    fn sealed_indexed_producer_threads_warning_config_and_observer() {
        fn compile(
            config: &crate::diagnostics::WarningConfig,
        ) -> (
            Result<bool, crate::lambda::lam_compile_main_indexed::IndexedPreJsError>,
            Vec<crate::lambda::lam_compile_main_indexed::IndexedHoistedWarning>,
        ) {
            let arena = ParseArena::new();
            let generator = std::sync::Arc::new(IdGenerator::with_start_stamp(20));
            let ctx = TypeContext::new(generator.clone());
            let env = initial_env(&ctx);
            let converter = RawLambdaConverter::with_id_generator_and_unit_name(
                &arena,
                &ctx,
                &env,
                generator,
                "Fixture".into(),
            );
            let export = Ident::new("value", 1, IdentFlags::NONE);
            let raw = RawLambda::prim(
                Primitive::Pmakeblock(
                    crate::lambda::TagInfo::ModuleExport(vec![export]),
                    crate::lambda::lam_primitive::Mutable::Immutable,
                ),
                vec![RawLambda::unit()],
                LamLoc::NONE,
            );
            let hoisted_loc =
                converter.lam_loc(Location::new_for_error("sealed-warning.res", 2, 4));
            let indexed_raw = converter.finish_indexed_raw(raw);
            let hoisted = crate::lambda::HoistedFunction {
                binding: Ident::new("missing", 9, IdentFlags::NONE),
                path: vec!["Missing".into()],
                loc: hoisted_loc,
                target_loc: LamLoc::NONE,
            };
            let mut inline = |_: &Ident, _: &str| None;
            let mut arity = |_: &Ident, _: &str| None;
            let mut warnings = Vec::new();
            let result = crate::lambda::lam_compile_main_indexed::lower_and_optimize_for_pre_js_indexed_with_diagnostics(
                indexed_raw,
                vec![export],
                &[hoisted],
                &ahash::AHashSet::new(),
                false,
                &mut inline,
                &mut arity,
                config,
                Some(&mut |warning: &crate::lambda::lam_compile_main_indexed::IndexedHoistedWarning| warnings.push(warning.clone())),
                None,
            )
            .map(|backend| backend.check_fatal_warnings().is_err());
            (result, warnings)
        }

        let mut disabled = crate::diagnostics::WarningConfig::new();
        disabled.parse("-53").unwrap();
        let (result, warnings) = compile(&disabled);
        assert!(!result.unwrap());
        assert!(warnings.is_empty());

        let mut fatal = crate::diagnostics::WarningConfig::new();
        fatal.parse_as_error("@53").unwrap();
        let (result, warnings) = compile(&fatal);
        assert!(result.unwrap());
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].is_error);
        assert_eq!(warnings[0].warning.number(), 53);
    }

    #[test]
    fn sync_matching_stamps_advances_raw_converter_after_matching_allocations() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::with_start_stamp(100);
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::with_start_stamp(&arena, &ctx, &env, 10);

        let pre_match_raw = converter.id_gen.create("raw_pre");
        assert_eq!(pre_match_raw.stamp(), 11);

        ctx.set_current_time(200);
        converter.sync_matching_stamps();

        let first_match_id = ctx.create_ident("match");
        let second_match_id = ctx.create_ident("match");
        assert_eq!(first_match_id.stamp(), 201);
        assert_eq!(second_match_id.stamp(), 202);

        converter.sync_matching_stamps();
        assert_eq!(converter.current_stamp(), 202);
        assert_eq!(converter.id_gen.current_stamp(), 202);

        let post_match_raw = converter.id_gen.create("raw_post");
        assert_eq!(post_match_raw.stamp(), 203);
    }

    #[test]
    fn fresh_ident_advances_past_type_context_allocations() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::with_start_stamp(100);
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::with_start_stamp(&arena, &ctx, &env, 10);

        ctx.set_current_time(200);
        let include_id = converter.fresh_ident("include");
        assert_eq!(include_id.stamp(), 201);
        assert_eq!(converter.current_stamp(), 201);
        assert_eq!(ctx.current_stamp(), 201);

        ctx.set_current_time(250);
        let match_id = converter.fresh_ident("match");
        assert_eq!(match_id.stamp(), 251);
        assert_eq!(converter.id_gen.current_stamp(), 251);
        assert_eq!(ctx.current_stamp(), 251);
    }

    #[test]
    fn rename_ident_shares_the_type_context_stamp_stream() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::with_start_stamp(100);
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::with_start_stamp(&arena, &ctx, &env, 10);
        let source_id = Ident::new("err", 7, IdentFlags::NONE);

        ctx.set_current_time(200);
        let renamed = converter.rename_ident(&source_id);
        assert_eq!(renamed.stamp(), 201);
        assert_eq!(converter.current_stamp(), 201);
        assert_eq!(ctx.current_stamp(), 201);

        let forced_id = ctx.create_ident("forced");
        assert_eq!(forced_id.stamp(), 202);
        let renamed_after_force = converter.rename_ident(&source_id);
        assert_eq!(renamed_after_force.stamp(), 203);
        assert_eq!(ctx.current_stamp(), 203);
    }

    #[test]
    fn raw_sequence_converts_rhs_before_lhs_for_raise_counts() {
        let mut arena = ParseArena::new();
        let first_try = simple_extension_try(&mut arena, "A", 1, 11);
        let second_try = simple_extension_try(&mut arena, "B", 2, 22);
        let sequence = Expression::new(
            ExpressionDesc::Texp_sequence(Box::new(first_try), Box::new(second_try)),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            EnvRef(0),
            Attributes::new(),
        );

        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lam = converter.convert_expr_raw(&sequence);

        let RawLambda::Lsequence(first, second) = lam else {
            panic!("expected sequence");
        };
        assert_eq!(try_handler_exit_id(&first), Some(2));
        assert_eq!(try_handler_exit_id(&second), Some(1));
    }

    #[test]
    fn raw_structure_eval_converts_tail_before_head_for_raise_counts() {
        let mut arena = ParseArena::new();
        let first_try = simple_extension_try(&mut arena, "A", 1, 11);
        let second_try = simple_extension_try(&mut arena, "B", 2, 22);
        let structure = Structure {
            str_items: vec![
                StructureItem {
                    str_desc: StructureItemDesc::Tstr_eval(first_try, Attributes::new()),
                    str_loc: LocIdx::none(),
                    str_env: EnvRef(0),
                },
                StructureItem {
                    str_desc: StructureItemDesc::Tstr_eval(second_try, Attributes::new()),
                    str_loc: LocIdx::none(),
                    str_env: EnvRef(0),
                },
            ],
            str_type: Vec::new(),
            str_final_env: EnvRef(0),
        };

        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lam = converter.convert_structure(&structure);

        let RawLambda::Lsequence(first, second) = lam else {
            panic!("expected outer sequence");
        };
        let RawLambda::Lsequence(second, _) = *second else {
            panic!("expected inner sequence");
        };

        assert_eq!(try_handler_exit_id(&first), Some(2));
        assert_eq!(try_handler_exit_id(&second), Some(1));
    }

    #[test]
    fn raw_nonrecursive_let_converts_bindings_in_source_order_for_raise_counts() {
        let mut arena = ParseArena::new();
        let first_id = Ident::create_local("first");
        let second_id = Ident::create_local("second");
        let bindings = vec![
            simple_value_binding(first_id, simple_extension_try(&mut arena, "A", 1, 11)),
            simple_value_binding(second_id, simple_extension_try(&mut arena, "B", 2, 22)),
        ];

        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lam = converter.convert_let_with_body_raw(
            crate::parser::ast::RecFlag::Nonrecursive,
            &bindings,
            RawLambda::unit(),
        );

        let RawLambda::Llet(_, outer_id, outer_value, inner) = lam else {
            panic!("expected outer let");
        };
        let RawLambda::Llet(_, inner_id, inner_value, _) = inner.as_ref() else {
            panic!("expected inner let");
        };

        assert!(outer_id.same(&first_id));
        assert!(inner_id.same(&second_id));
        assert_eq!(try_handler_exit_id(outer_value.as_ref()), Some(1));
        assert_eq!(try_handler_exit_id(inner_value.as_ref()), Some(2));
    }

    fn type_alias_decl(manifest: TypeExprRef) -> crate::types::TypeDeclaration {
        crate::types::TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: crate::types::decl::TypeKind::TypeAbstract,
            type_private: crate::types::asttypes::PrivateFlag::Public,
            type_manifest: Some(manifest),
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: crate::types::TypeRepresentation::Boxed,
            type_inlined_types: vec![],
            type_path: None,
        }
    }

    fn primitive_wrapper_body_primitive(lam: RawLambda) -> Primitive {
        let RawLambda::Lfunction(function) = lam else {
            panic!("expected primitive wrapper function");
        };
        let RawLambda::Lprim(info) = *function.body else {
            panic!("expected primitive wrapper body");
        };
        info.primitive
    }

    #[test]
    fn primitive_value_compare_specializes_through_alias_env() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);
        let int_ty = ctx.predef_int();
        let compare_ty = ctx.new_arrow_simple(int_ty, ctx.new_arrow_simple(int_ty, int_ty));
        let alias_id = Ident::create_local("cmp_alias");
        env.add_type(alias_id, type_alias_decl(compare_ty));

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "%compare".to_string(),
            prim_arity: 2,
            prim_kind: crate::types::decl::PrimKind::KindIntrinsic,
            prim_native_float: false,
            prim_from_constructor: false,
        };
        let alias_ty = ctx.new_constr(crate::types::Path::pident(alias_id), vec![]);

        let primitive = primitive_wrapper_body_primitive(converter.translate_primitive_raw_in_env(
            SrcLoc::from(Location::none()),
            &prim,
            alias_ty,
            &env,
            alias_ty,
            None,
        ));

        assert_eq!(primitive, Primitive::Pintorder);
    }

    #[test]
    fn coercion_alias_keeps_original_path_instead_of_normalizing_through_module_alias() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let original_module = Ident::create_local("M'");
        let local_n = Ident::create_local("N");
        env.add_module(
            original_module,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigModule(
                    local_n,
                    crate::types::decl::ModuleDeclaration {
                        md_type: crate::types::decl::ModuleType::MtyAlias(
                            crate::types::decl::AliasPresence::MtaPresent,
                            crate::types::Path::pident(local_n),
                        ),
                        md_attributes: Vec::new(),
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                )]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let alias_path =
            crate::types::Path::pdot_pos(crate::types::Path::pident(original_module), "N", 0);
        let coercion = ModuleCoercion::Tcoerce_alias(
            EnvRef(0),
            alias_path,
            Box::new(ModuleCoercion::Tcoerce_none),
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.apply_coercion_raw(
            Location::none(),
            LetKind::Alias,
            &coercion,
            RawLambda::var(Ident::create_local("arg")),
        );

        let RawLambda::Lprim(info) = lowered else {
            panic!("expected coercion alias to translate to a field access");
        };
        assert!(matches!(
            info.primitive,
            Primitive::Pfield(0, FieldDbgInfo::Module { ref name }) if name == "N"
        ));
        assert!(matches!(
            info.args.as_slice(),
            [RawLambda::Lvar(id)] if id.same(&original_module)
        ));
    }

    #[test]
    fn primitive_value_equality_specializes_through_alias_env() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);
        let string_ty = ctx.predef_string();
        let bool_ty = ctx.predef_bool();
        let eq_ty = ctx.new_arrow_simple(string_ty, ctx.new_arrow_simple(string_ty, bool_ty));
        let alias_id = Ident::create_local("string_eq_alias");
        env.add_type(alias_id, type_alias_decl(eq_ty));

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "%equal".to_string(),
            prim_arity: 2,
            prim_kind: crate::types::decl::PrimKind::KindIntrinsic,
            prim_native_float: false,
            prim_from_constructor: false,
        };
        let alias_ty = ctx.new_constr(crate::types::Path::pident(alias_id), vec![]);

        let primitive = primitive_wrapper_body_primitive(converter.translate_primitive_raw_in_env(
            SrcLoc::from(Location::none()),
            &prim,
            alias_ty,
            &env,
            alias_ty,
            None,
        ));

        assert_eq!(
            primitive,
            Primitive::Pstringcomp(crate::lambda::Comparison::Eq)
        );
    }

    #[test]
    fn translate_module_path_raw_follows_mty_ident_flattened_submodule_aliases() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let pkg = Ident::create_persistent("Pkg");
        let pkg_list = Ident::create_persistent("Pkg_List");
        env.add_module(
            pkg,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigModule(
                    Ident::create_local("List"),
                    crate::types::decl::ModuleDeclaration {
                        md_type: crate::types::decl::ModuleType::MtyIdent(
                            crate::types::Path::pident(pkg_list),
                        ),
                        md_attributes: Vec::new(),
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                )]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );
        env.add_module(
            pkg_list,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_module_path_raw(
            &crate::types::Path::pdot(crate::types::Path::pident(pkg), "List"),
            SrcLoc::from(Location::none()),
        );

        assert!(matches!(
            lowered,
            RawLambda::LglobalModule(id) if id.same(&pkg_list)
        ));
    }

    #[test]
    fn translate_module_path_raw_leaves_possible_required_modules_to_later_passes() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let side_effect = Ident::create_persistent("Side_effect");

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_module_path_raw(
            &crate::types::path::Path::pident(side_effect),
            SrcLoc::from(Location::none()),
        );
        let possible_required_modules = converter.take_possible_required_modules();

        assert!(matches!(
            lowered,
            RawLambda::LglobalModule(id) if id.same(&side_effect)
        ));
        assert!(possible_required_modules.is_empty());
    }

    #[test]
    fn empty_include_records_possible_required_modules() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let side_effect = Ident::create_persistent("Side_effect");
        let module_expr = crate::types::typedtree::ModuleExpr {
            mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_ident(
                crate::types::Path::pident(side_effect),
                crate::parse_arena::Located::mknoloc(crate::parse_arena::LidentIdx(0)),
            ),
            mod_loc: crate::parse_arena::LocIdx::default(),
            mod_type: crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaAbsent,
                crate::types::Path::pident(side_effect),
            ),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        };

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        converter.note_possible_required_modules_from_empty_include(&module_expr);
        let possible_required_modules = converter.take_possible_required_modules();
        let expected = ModuleId {
            id: side_effect,
            kind: Kind::Ml,
            dynamic_import: false,
        };

        assert!(possible_required_modules.contains(&expected));
    }

    #[test]
    fn plain_module_aliases_do_not_record_possible_required_modules() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let side_effect = Ident::create_persistent("Side_effect");
        let module_expr = crate::types::typedtree::ModuleExpr {
            mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_ident(
                crate::types::Path::pident(side_effect),
                crate::parse_arena::Located::mknoloc(crate::parse_arena::LidentIdx(0)),
            ),
            mod_loc: crate::parse_arena::LocIdx::default(),
            mod_type: crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaPresent,
                crate::types::Path::pident(side_effect),
            ),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        };

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.convert_module_expr_raw(&module_expr, &None);
        let possible_required_modules = converter.take_possible_required_modules();

        assert!(matches!(lowered, RawLambda::Lconst(Constant::ModuleAlias)));
        assert!(possible_required_modules.is_empty());
    }

    #[test]
    fn translate_value_path_raw_keeps_local_unpack_prefixes() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let modtype_x = Ident::create_local("X");
        let local_l = Ident::create_local("L");
        env.add_module(
            local_l,
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtyIdent(crate::types::Path::pident(
                    modtype_x,
                )),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot(crate::types::Path::pident(local_l), "length"),
            SrcLoc::from(Location::none()),
        );

        let RawLambda::Lprim(info) = lowered else {
            panic!("expected value path to lower to a field access");
        };
        assert!(matches!(
            info.primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { ref name }) if name == "length"
        ));
        assert!(matches!(
            info.args.as_slice(),
            [RawLambda::Lvar(id)] if id.same(&local_l)
        ));
    }

    #[test]
    fn translate_value_path_raw_follows_persistent_mty_ident_flattened_submodule_aliases() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let pkg = Ident::create_persistent("Pkg");
        let pkg_list = Ident::create_persistent("Pkg_List");
        env.add_module(
            pkg,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigModule(
                    Ident::create_local("List"),
                    crate::types::decl::ModuleDeclaration {
                        md_type: crate::types::decl::ModuleType::MtyIdent(
                            crate::types::Path::pident(pkg_list),
                        ),
                        md_attributes: Vec::new(),
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                )]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );
        env.add_module(
            pkg_list,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigValue(
                    Ident::create_local("length"),
                    crate::types::decl::ValueDescription {
                        val_type: ctx.new_var(None),
                        val_kind: crate::types::decl::ValueKind::ValReg,
                        val_loc: crate::types::DeclLoc::none(),
                        val_attributes: Vec::new(),
                        val_path: None,
                    },
                )]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot(
                crate::types::Path::pdot(crate::types::Path::pident(pkg), "List"),
                "length",
            ),
            SrcLoc::from(Location::none()),
        );

        let RawLambda::Lprim(info) = lowered else {
            panic!("expected value path to lower to a field access");
        };
        assert!(matches!(
            info.primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { ref name }) if name == "length"
        ));
        assert!(matches!(
            info.args.as_slice(),
            [RawLambda::LglobalModule(id)] if id.same(&pkg_list)
        ));
    }

    #[test]
    fn translate_value_path_raw_follows_persistent_nested_module_alias_prefixes() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let icon = Ident::create_persistent("Icon");
        let export = Ident::create_local("Export");
        let subtitles = Ident::create_local("Subtitles");
        let main = Ident::create_local("Main");
        let separate = Ident::create_local("Separate");
        let make = Ident::create_local("make");

        let icon_export_path =
            crate::types::Path::pdot(crate::types::Path::pident(icon), export.name().to_string());
        let subtitles_path =
            crate::types::Path::pdot(icon_export_path.clone(), subtitles.name().to_string());
        let main_path = crate::types::Path::pdot(subtitles_path.clone(), main.name().to_string());

        let main_decl = crate::types::decl::ModuleDeclaration {
            md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigValue(
                make,
                crate::types::decl::ValueDescription {
                    val_type: ctx.new_var(None),
                    val_kind: crate::types::decl::ValueKind::ValReg,
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Vec::new(),
                    val_path: None,
                },
            )]),
            md_attributes: Vec::new(),
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        };

        env.add_module(
            icon,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![crate::types::SignatureItem::SigModule(
                    export,
                    crate::types::decl::ModuleDeclaration {
                        md_type: test_signature_module_type(vec![
                            crate::types::SignatureItem::SigModule(
                                subtitles,
                                crate::types::decl::ModuleDeclaration {
                                    md_type: test_signature_module_type(vec![
                                        crate::types::SignatureItem::SigModule(
                                            main,
                                            main_decl,
                                            crate::types::decl::RecStatus::TrecNot,
                                        ),
                                        crate::types::SignatureItem::SigModule(
                                            separate,
                                            crate::types::decl::ModuleDeclaration {
                                                md_type: crate::types::decl::ModuleType::MtyAlias(
                                                    crate::types::decl::AliasPresence::MtaPresent,
                                                    main_path.clone(),
                                                ),
                                                md_attributes: Vec::new(),
                                                md_loc: crate::types::DeclLoc::none(),
                                                md_path: None,
                                            },
                                            crate::types::decl::RecStatus::TrecNot,
                                        ),
                                    ]),
                                    md_attributes: Vec::new(),
                                    md_loc: crate::types::DeclLoc::none(),
                                    md_path: None,
                                },
                                crate::types::decl::RecStatus::TrecNot,
                            ),
                        ]),
                        md_attributes: Vec::new(),
                        md_loc: crate::types::DeclLoc::none(),
                        md_path: None,
                    },
                    crate::types::decl::RecStatus::TrecNot,
                )]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let path = crate::types::Path::pdot(
            crate::types::Path::pdot(subtitles_path, separate.name().to_string()),
            make.name().to_string(),
        );
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered =
            converter.translate_value_path_raw_in_env(&env, &path, SrcLoc::from(Location::none()));

        let RawLambda::Lprim(make_info) = lowered else {
            panic!("expected value path to lower to make field access");
        };
        assert!(matches!(
            make_info.primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { ref name }) if name == "make"
        ));
        assert!(matches!(
            make_info.args.as_slice(),
            [RawLambda::Lprim(main_info)]
                if matches!(
                    main_info.primitive,
                    Primitive::Pfield(_, FieldDbgInfo::Module { ref name }) if name == "Main"
                )
        ));
    }

    #[test]
    fn translate_value_path_raw_keeps_constrained_persistent_submodule_prefixes() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let mut env = initial_env(&ctx);

        let inner_define = Ident::create_persistent("Inner_define");
        let runtime_n = Ident::create_local("N");
        let constrained_n0 = Ident::create_local("N0");
        let runtime_n1 = Ident::create_local("N1");
        let modtype_s0 = Ident::create_local("S0");
        env.add_module(
            inner_define,
            crate::types::decl::ModuleDeclaration {
                md_type: test_signature_module_type(vec![
                    crate::types::SignatureItem::SigModule(
                        runtime_n,
                        crate::types::decl::ModuleDeclaration {
                            md_type: test_signature_module_type(vec![]),
                            md_attributes: Vec::new(),
                            md_loc: crate::types::DeclLoc::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                    crate::types::SignatureItem::SigModtype(
                        modtype_s0,
                        crate::types::decl::ModtypeDeclaration {
                            mtd_type: Some(test_signature_module_type(vec![
                                crate::types::SignatureItem::SigValue(
                                    Ident::create_local("f1"),
                                    crate::types::decl::ValueDescription {
                                        val_type: ctx.new_var(None),
                                        val_kind: crate::types::decl::ValueKind::ValReg,
                                        val_loc: crate::types::DeclLoc::none(),
                                        val_attributes: Vec::new(),
                                        val_path: None,
                                    },
                                ),
                            ])),
                            mtd_attributes: Vec::new(),
                            mtd_loc: crate::types::DeclLoc::none(),
                        },
                    ),
                    crate::types::SignatureItem::SigModule(
                        constrained_n0,
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtyIdent(
                                crate::types::Path::pdot(
                                    crate::types::Path::pident(inner_define),
                                    "S0",
                                ),
                            ),
                            md_attributes: Vec::new(),
                            md_loc: crate::types::DeclLoc::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                    crate::types::SignatureItem::SigModule(
                        runtime_n1,
                        crate::types::decl::ModuleDeclaration {
                            md_type: test_signature_module_type(vec![]),
                            md_attributes: Vec::new(),
                            md_loc: crate::types::DeclLoc::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot_pos(
                crate::types::Path::pdot_pos(crate::types::Path::pident(inner_define), "N0", 1),
                "f1",
                0,
            ),
            SrcLoc::from(Location::none()),
        );

        let RawLambda::Lprim(info) = lowered else {
            panic!("expected constrained value path to lower to a field access");
        };
        assert!(matches!(
            info.primitive,
            Primitive::Pfield(0, FieldDbgInfo::Module { ref name }) if name == "f1"
        ));
        assert!(matches!(
            info.args.as_slice(),
            [RawLambda::Lprim(prefix_info)]
                if matches!(
                    prefix_info.primitive,
                    Primitive::Pfield(1, FieldDbgInfo::Module { ref name }) if name == "N0"
                ) && matches!(
                    prefix_info.args.as_slice(),
                    [RawLambda::LglobalModule(id)] if id.same(&inner_define)
                )
        ));
    }

    #[test]
    fn recmodule_function_init_shape_keeps_function_constructor_metadata() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);

        let param = ctx.new_var(None);
        let ret = ctx.new_var(None);
        let func_ty = ctx.new_arrow_simple(param, ret);
        let sig = vec![crate::types::decl::SignatureItem::SigValue(
            Ident::create_local("u"),
            crate::types::decl::ValueDescription {
                val_type: func_ty,
                val_kind: crate::types::decl::ValueKind::ValReg,
                val_loc: crate::types::DeclLoc::none(),
                val_attributes: Vec::new(),
                val_path: None,
            },
        )];

        let shape = converter
            .init_shape_struct(&env, &sig)
            .expect("function signatures should produce recursive-module shapes");
        let [Constant::Block { elements, .. }] = shape.as_slice() else {
            panic!("expected named tuple shape");
        };
        let [init_v, Constant::String(s)] = elements.as_slice() else {
            panic!("expected function shape tuple");
        };
        assert_eq!(s, "u");
        assert!(matches!(
            init_v,
            Constant::Constructor(crate::types::VariantTag {
                name,
                literal: None,
            }) if name == "Function"
        ));
    }
}
