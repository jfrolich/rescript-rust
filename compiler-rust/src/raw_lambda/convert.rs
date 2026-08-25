//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use ahash::AHashSet;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path as StdPath;
use std::sync::{Mutex, OnceLock};

use crate::cmi::marshal_reader::{MarshalReader, OcamlValue};
use crate::context::IdGenerator;
use crate::diagnostics::{Warning, WarningConfig};
use crate::ident::{Ident, IdentFlags};
use crate::js_ir::{Kind, ModuleId};
use crate::lambda::Constant;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::{
    ConstructorRuntimeTag, ConstructorTag as PointerConstructorTag, PointerInfo, StringDelim,
};
use crate::lambda::lam_primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName, ExternalObjLabel,
    ExternalObjSpec, ExternalReturnWrapper, ExternalSpec, ImportAttributes, Mutable,
};
use crate::lambda::lam_tag_info::{
    Attribute as TagAttribute, AttributePayload as TagAttributePayload, TagInfo,
};
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, Comparison, FieldDbgInfo, FunctionAttribute, InlineAttribute,
    Lambda, LambdaSwitch, Primitive, SetFieldDbgInfo,
};
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::{Arity, MutableFlag as ParserMutableFlag};
use crate::raw_lambda::matching as full_matching;
use crate::raw_lambda::typeopt::{
    constructor_has_optional_shape, is_base_type as typeopt_is_base_type,
    type_cannot_contain_undefined, type_cannot_contain_undefined_no_env, type_is_builtin_object,
};
use crate::raw_lambda::{RawLambda, RawPrimInfo};
use crate::types::ConstructorTag;
use crate::types::SignatureItem;
use crate::types::asttypes::MutableFlag as TypeMutableFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{LabelDescription, RecordRepresentation, ValueKind};
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typecore::TypeCoreWarning;
use crate::types::typedtree::{
    ApplyArg, Case, Constant as TConstant, EnvRef, Expression, ExpressionDesc, FunctionParam,
    FunctionParamPattern, MethKind, ModuleCoercion, ModuleExpr, ModuleExprDesc, Partial, Pattern,
    PatternDesc, RecordField, RecordLabelDefinition, Structure, StructureItem, StructureItemDesc,
    ValueBinding,
};

const PREDEF_MATCH_FAILURE_STAMP: i32 = 17;
const PREDEF_ASSERT_FAILURE_STAMP: i32 = 27;
const REC_MODULE_FUNCTION_CSTR_CONST: i32 = 3;
const REC_MODULE_FUNCTION_CSTR_NON_CONST: i32 = 2;

#[derive(Clone)]
enum RawFunctionBinding {
    Value(Vec<ValueBinding>),
    Module(Ident, Located<String>, ModuleExpr),
}

enum RawFunctionBindingRef<'a> {
    Value(&'a [ValueBinding]),
    Module(&'a Ident, &'a ModuleExpr),
}

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
    Constant::Int {
        i: 0,
        comment: Some(PointerInfo::Constructor(PointerConstructorTag {
            name: "Function".to_string(),
            const_: REC_MODULE_FUNCTION_CSTR_CONST,
            non_const: REC_MODULE_FUNCTION_CSTR_NON_CONST,
            runtime_tag: None,
        })),
    }
}

fn raw_constructor_constant(cstr: &crate::types::ConstructorDescription, tag: i32) -> Constant {
    // OCaml compiler/ml/translcore.ml:800-816 emits Pt_shape_none
    // only when Datarepr.constructor_has_optional_shape marks the
    // constructor; an ordinary constructor named `None` stays Pt_constructor.
    let comment = if constructor_has_optional_shape(cstr) {
        PointerInfo::ShapeNone
    } else {
        PointerInfo::Constructor(PointerConstructorTag {
            name: cstr.cstr_name.clone(),
            const_: cstr.cstr_consts,
            non_const: cstr.cstr_nonconsts,
            runtime_tag: constructor_runtime_tag(&cstr.cstr_attributes),
        })
    };
    Constant::Int {
        i: tag,
        comment: Some(comment),
    }
}

fn raw_optional_none_constant() -> Constant {
    Constant::Int {
        i: 0,
        comment: Some(PointerInfo::ShapeNone),
    }
}

fn raw_optional_none() -> RawLambda {
    RawLambda::const_(raw_optional_none_constant())
}

fn lambda_optional_none() -> Lambda {
    Lambda::const_(Constant::Pointer("0a".to_string()))
}

fn raw_free_variables(lam: &RawLambda) -> HashSet<Ident> {
    fn collect(lam: &RawLambda, fv: &mut HashSet<Ident>) {
        match lam {
            RawLambda::Lvar(id) => {
                fv.insert(id.clone());
            }
            RawLambda::LglobalModule(_, _) | RawLambda::Lconst(_) => {}
            RawLambda::Lapply(apply) => {
                collect(&apply.ap_func, fv);
                for arg in &apply.ap_args {
                    collect(arg, fv);
                }
            }
            RawLambda::Lfunction(func) => {
                collect(&func.body, fv);
                for param in &func.params {
                    fv.remove(param);
                }
            }
            RawLambda::Llet(_, id, arg, body) => {
                collect(arg, fv);
                collect(body, fv);
                fv.remove(id);
            }
            RawLambda::Lletrec(bindings, body) => {
                collect(body, fv);
                for (_, expr) in bindings {
                    collect(expr, fv);
                }
                for (id, _) in bindings {
                    fv.remove(id);
                }
            }
            RawLambda::Lprim(info) => {
                for arg in &info.args {
                    collect(arg, fv);
                }
            }
            RawLambda::Lswitch(arg, sw, _) => {
                collect(arg, fv);
                for (_, lam) in &sw.sw_consts {
                    collect(lam, fv);
                }
                for (_, lam) in &sw.sw_blocks {
                    collect(lam, fv);
                }
                if let Some(fail) = &sw.sw_failaction {
                    collect(fail, fv);
                }
            }
            RawLambda::LstringSwitch(arg, cases, default) => {
                collect(arg, fv);
                for (_, lam) in cases {
                    collect(lam, fv);
                }
                if let Some(default) = default {
                    collect(default, fv);
                }
            }
            RawLambda::LstaticRaise(_, args) => {
                for arg in args {
                    collect(arg, fv);
                }
            }
            RawLambda::LstaticCatch(body, (_, vars), handler) => {
                collect(body, fv);
                collect(handler, fv);
                for var in vars {
                    fv.remove(var);
                }
            }
            RawLambda::LtryWith(body, exn, handler) => {
                collect(body, fv);
                collect(handler, fv);
                fv.remove(exn);
            }
            RawLambda::LifThenElse(cond, ifso, ifnot) => {
                collect(cond, fv);
                collect(ifso, fv);
                collect(ifnot, fv);
            }
            RawLambda::Lsequence(first, second) => {
                collect(first, fv);
                collect(second, fv);
            }
            RawLambda::Lwhile(cond, body) => {
                collect(cond, fv);
                collect(body, fv);
            }
            RawLambda::Lfor(var, lo, hi, _, body) => {
                collect(lo, fv);
                collect(hi, fv);
                collect(body, fv);
                fv.remove(var);
            }
            RawLambda::Lfor_of(var, iterable, body)
            | RawLambda::Lfor_await_of(var, iterable, body) => {
                collect(iterable, fv);
                collect(body, fv);
                fv.remove(var);
            }
            RawLambda::Lassign(id, expr) => {
                collect(expr, fv);
                fv.insert(id.clone());
            }
            RawLambda::Lsend(_, obj, _) => collect(obj, fv),
            RawLambda::Lbreak | RawLambda::Lcontinue => {}
        }
    }

    let mut fv = HashSet::new();
    collect(lam, &mut fv);
    fv
}

fn raw_subst_idents_owned(subst: &HashMap<Ident, Ident>, lam: RawLambda) -> RawLambda {
    if subst.is_empty() {
        return lam;
    }

    match lam {
        RawLambda::Lvar(id) => subst
            .get(&id)
            .cloned()
            .map(RawLambda::Lvar)
            .unwrap_or(RawLambda::Lvar(id)),
        RawLambda::LglobalModule(_, _) | RawLambda::Lconst(_) => lam,
        RawLambda::Lapply(apply) => RawLambda::Lapply(crate::raw_lambda::RawApply {
            ap_func: Box::new(raw_subst_idents_owned(subst, *apply.ap_func)),
            ap_args: apply
                .ap_args
                .into_iter()
                .map(|arg| raw_subst_idents_owned(subst, arg))
                .collect(),
            ap_info: apply.ap_info,
            ap_transformed_jsx: apply.ap_transformed_jsx,
        }),
        RawLambda::Lfunction(func) => RawLambda::Lfunction(crate::raw_lambda::RawLFunction {
            arity: func.arity,
            params: func.params,
            body: Box::new(raw_subst_idents_owned(subst, *func.body)),
            attr: func.attr,
        }),
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
        RawLambda::Lprim(info) => RawLambda::Lprim(crate::raw_lambda::RawPrimInfo {
            primitive: info.primitive,
            args: info
                .args
                .into_iter()
                .map(|arg| raw_subst_idents_owned(subst, arg))
                .collect(),
            loc: info.loc,
        }),
        RawLambda::Lswitch(arg, sw, loc) => RawLambda::Lswitch(
            Box::new(raw_subst_idents_owned(subst, *arg)),
            crate::raw_lambda::RawLambdaSwitch {
                sw_numconsts: sw.sw_numconsts,
                sw_consts_full: sw.sw_consts_full,
                sw_consts: sw
                    .sw_consts
                    .into_iter()
                    .map(|(tag, lam)| (tag, raw_subst_idents_owned(subst, lam)))
                    .collect(),
                sw_numblocks: sw.sw_numblocks,
                sw_blocks_full: sw.sw_blocks_full,
                sw_blocks: sw
                    .sw_blocks
                    .into_iter()
                    .map(|(tag, lam)| (tag, raw_subst_idents_owned(subst, lam)))
                    .collect(),
                sw_failaction: sw
                    .sw_failaction
                    .map(|lam| Box::new(raw_subst_idents_owned(subst, *lam))),
                sw_names: sw.sw_names,
            },
            loc,
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
        RawLambda::Lsend(name, obj, loc) => {
            RawLambda::Lsend(name, Box::new(raw_subst_idents_owned(subst, *obj)), loc)
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

fn let_bound_idents(bindings: &[ValueBinding]) -> Vec<Ident> {
    let mut ids = Vec::new();
    for binding in bindings {
        iter_bound_pattern_idents(&binding.vb_pat, &mut |id| ids.push(id.clone()));
    }
    ids
}

fn simple_let_binding_id(binding: &ValueBinding) -> Option<Ident> {
    match &binding.vb_pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id.clone()),
        PatternDesc::Tpat_alias(inner, id, _)
            if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
        {
            Some(id.clone())
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

fn to_parser_mutable(flag: TypeMutableFlag) -> ParserMutableFlag {
    match flag {
        TypeMutableFlag::Mutable => ParserMutableFlag::Mutable,
        TypeMutableFlag::Immutable => ParserMutableFlag::Immutable,
    }
}

/// OCaml's Lambda.find_name: check for @as attribute to get the JS runtime name.
/// Falls back to the label's declared name.
fn label_runtime_name(lbl: &LabelDescription) -> String {
    for attr in &lbl.lbl_attributes {
        if attr.attr_name.txt == "as" {
            if let crate::types::decl::AttributePayload::Str(name) = &attr.attr_payload {
                return name.clone();
            }
        }
    }
    lbl.lbl_name.clone()
}

fn constructor_runtime_tag(
    attrs: &[crate::types::decl::Attribute],
) -> Option<ConstructorRuntimeTag> {
    attrs.iter().find_map(|attr| {
        if attr.attr_name.txt != "as" {
            return None;
        }
        match &attr.attr_payload {
            crate::types::decl::AttributePayload::Int(value) => {
                Some(ConstructorRuntimeTag::Int(*value))
            }
            crate::types::decl::AttributePayload::IntLiteral(value) => {
                crate::types::decl::parse_ocaml_int_literal(value).map(ConstructorRuntimeTag::Int)
            }
            crate::types::decl::AttributePayload::Str(value) => {
                Some(ConstructorRuntimeTag::String(value.clone()))
            }
            crate::types::decl::AttributePayload::Float(value) => {
                Some(ConstructorRuntimeTag::Float(value.clone()))
            }
            crate::types::decl::AttributePayload::BigInt(value) => {
                Some(ConstructorRuntimeTag::BigInt(value.clone()))
            }
            crate::types::decl::AttributePayload::Bool(value) => {
                Some(ConstructorRuntimeTag::Bool(*value))
            }
            crate::types::decl::AttributePayload::Ident(value) if value == "null" => {
                Some(ConstructorRuntimeTag::Null)
            }
            crate::types::decl::AttributePayload::Ident(value) if value == "undefined" => {
                Some(ConstructorRuntimeTag::Undefined)
            }
            _ => None,
        }
    })
}

fn lower_tag_info_attributes(attrs: &[crate::types::decl::Attribute]) -> Vec<TagAttribute> {
    attrs
        .iter()
        .map(|attr| TagAttribute {
            name: attr.attr_name.txt.clone(),
            payload: match &attr.attr_payload {
                crate::types::decl::AttributePayload::Empty => TagAttributePayload::Empty,
                crate::types::decl::AttributePayload::Str(value) => {
                    TagAttributePayload::Str(value.clone())
                }
                crate::types::decl::AttributePayload::Int(value) => {
                    TagAttributePayload::Int(*value)
                }
                crate::types::decl::AttributePayload::IntLiteral(value) => {
                    crate::types::decl::parse_ocaml_int_literal(value)
                        .map(TagAttributePayload::Int)
                        .unwrap_or(TagAttributePayload::Empty)
                }
                crate::types::decl::AttributePayload::Float(value) => {
                    TagAttributePayload::Float(value.clone())
                }
                crate::types::decl::AttributePayload::BigInt(value) => {
                    TagAttributePayload::BigInt(value.clone())
                }
                crate::types::decl::AttributePayload::Bool(value) => {
                    TagAttributePayload::Bool(*value)
                }
                crate::types::decl::AttributePayload::Ident(value) => {
                    TagAttributePayload::Ident(value.clone())
                }
                crate::types::decl::AttributePayload::Deprecated { reason, .. } => {
                    TagAttributePayload::Str(reason.clone())
                }
                crate::types::decl::AttributePayload::Structure(_) => TagAttributePayload::Empty,
            },
        })
        .collect()
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
        let crate::parser::ast::StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc else {
            return false;
        };
        let (expr_idx, _) = &**inner;
        let expr = arena.get_expr(*expr_idx);
        let PExpressionDesc::Pexp_record(record) = &*expr.pexp_desc else {
            return false;
        };
        let (fields, _) = &**record;
        fields.iter().any(|field| {
            let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) else {
                return false;
            };
            if arena.get_string(*name_idx) != "flags" {
                return false;
            }
            let field_expr = arena.get_expr(field.expr);
            let PExpressionDesc::Pexp_array(elements) = &*field_expr.pexp_desc else {
                return false;
            };
            elements.iter().any(|elem_idx| {
                let elem = arena.get_expr(*elem_idx);
                matches!(
                    &*elem.pexp_desc,
                    PExpressionDesc::Pexp_constant(c)
                        if matches!(&**c, PConstant::String(s, _) if s.as_ref() == value)
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
        comment: Some(PointerInfo::PolyVariant(tag.to_string())),
    })
}

fn raw_polyvariant_compare(scrutinee: RawLambda, tag: &str, loc: Location) -> RawLambda {
    RawLambda::prim(
        Primitive::Pjscomp(Comparison::Eq),
        vec![scrutinee, raw_polyvariant_const(tag)],
        loc,
    )
}

fn raw_record_field_access(lbl: &LabelDescription) -> Option<(i32, FieldDbgInfo)> {
    let name = label_runtime_name(lbl);
    let info = match &lbl.lbl_repres {
        RecordRepresentation::RecordRegular => FieldDbgInfo::Record {
            name,
            mutable_flag: to_parser_mutable(lbl.lbl_mut),
        },
        RecordRepresentation::RecordFloatUnused => return None,
        RecordRepresentation::RecordUnboxed(_) => FieldDbgInfo::Record {
            name,
            mutable_flag: to_parser_mutable(lbl.lbl_mut),
        },
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

fn trace_raw_fallback(kind: &'static str) {
    if !crate::debug_flags::raw_fallback_trace() {
        return;
    }

    static SEEN: OnceLock<Mutex<BTreeSet<&'static str>>> = OnceLock::new();
    let seen = SEEN.get_or_init(|| Mutex::new(BTreeSet::new()));
    let mut guard = seen.lock().expect("trace set poisoned");
    if guard.insert(kind) {
        eprintln!("[raw-fallback] {kind}");
    }
}

fn trace_raw_match_fallback(loc: &Location, scrut: &Expression, cases: &[Case]) {
    if !crate::debug_flags::raw_fallback_trace() {
        return;
    }

    static SEEN: OnceLock<Mutex<BTreeSet<String>>> = OnceLock::new();
    let seen = SEEN.get_or_init(|| Mutex::new(BTreeSet::new()));
    let mut guard = seen.lock().expect("trace set poisoned");
    let pat = cases
        .first()
        .map(|case| RawLambdaConverter::pattern_desc_name(&case.c_lhs))
        .unwrap_or("none");
    let key = format!(
        "match:scrut={}:pat={}:cases={}:loc={}:{}-{}:{}",
        RawLambdaConverter::expr_desc_name(&scrut.exp_desc),
        pat,
        cases.len(),
        loc.loc_start.line,
        loc.loc_start.column_1indexed(),
        loc.loc_end.line,
        loc.loc_end.column_1indexed()
    );
    if guard.insert(key.clone()) {
        eprintln!("[raw-fallback] {key}");
    }
}

#[derive(Clone, PartialEq, Eq)]
enum SimpleSwitchKey {
    Int(i32),
    ConstCtor(i32),
    BlockCtor(i32),
}

impl SimpleSwitchKey {
    fn tag(&self) -> i32 {
        match self {
            SimpleSwitchKey::Int(i)
            | SimpleSwitchKey::ConstCtor(i)
            | SimpleSwitchKey::BlockCtor(i) => *i,
        }
    }

    fn is_block(&self) -> bool {
        matches!(self, SimpleSwitchKey::BlockCtor(_))
    }
}

#[derive(Clone)]
struct ExpandedTupleCase<'a> {
    case: &'a Case,
    items: Vec<&'a Pattern>,
}

#[derive(Clone)]
struct TupleCaseState<'a> {
    case: ExpandedTupleCase<'a>,
    selected: Vec<(usize, &'a Pattern)>,
}

fn peel_aliases<'a>(mut pat: &'a Pattern) -> (&'a Pattern, Vec<Ident>) {
    let mut aliases = Vec::new();
    while let PatternDesc::Tpat_alias(inner, id, _) = &pat.pat_desc {
        aliases.push(id.clone());
        pat = inner;
    }
    (pat, aliases)
}

fn wrap_aliases(aliases: &[Ident], scrut: Lambda, body: Lambda) -> Lambda {
    aliases.iter().rev().fold(body, |acc, id| {
        Lambda::let_(LetKind::Alias, id.clone(), scrut.clone(), acc)
    })
}

fn wrap_aliases_raw(aliases: &[Ident], scrut: RawLambda, body: RawLambda) -> RawLambda {
    aliases.iter().rev().fold(body, |acc, id| {
        // Skip self-bindings (e.g., `let e/1 =a e/1` when alias matches scrutinee var)
        if let RawLambda::Lvar(scrut_id) = &scrut {
            if scrut_id.same(id) {
                return acc;
            }
        }
        RawLambda::let_(LetKind::Alias, id.clone(), scrut.clone(), acc)
    })
}

fn collect_string_pattern_arms(pat: &Pattern) -> Option<Vec<(String, Vec<Ident>)>> {
    fn collect_rec(
        pat: &Pattern,
        aliases: Vec<Ident>,
        out: &mut Vec<(String, Vec<Ident>)>,
    ) -> Option<()> {
        match &pat.pat_desc {
            PatternDesc::Tpat_alias(inner, id, _) => {
                let mut aliases = aliases;
                aliases.push(id.clone());
                collect_rec(inner, aliases, out)
            }
            PatternDesc::Tpat_or(left, right, _) => {
                collect_rec(left, aliases.clone(), out)?;
                collect_rec(right, aliases, out)
            }
            PatternDesc::Tpat_constant(TConstant::String(s, _)) => {
                out.push((s.clone(), aliases));
                Some(())
            }
            _ => None,
        }
    }

    let mut out = Vec::new();
    collect_rec(pat, Vec::new(), &mut out)?;
    Some(out)
}

fn pattern_name_hint(pat: &Pattern) -> Option<String> {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
            Some(id.name().to_string())
        }
        PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => match &args[0].pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                Some(id.name().to_string())
            }
            _ => None,
        },
        _ => None,
    }
}

fn case_name_hint(default: &str, cases: &[Case]) -> Option<String> {
    cases
        .iter()
        .find_map(|case| pattern_name_hint(&case.c_lhs))
        .or_else(|| {
            if cases.is_empty() {
                None
            } else {
                Some(default.to_string())
            }
        })
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

#[derive(Debug, Clone)]
pub struct RawLambdaDiagnostic {
    pub loc: Location,
    pub message: String,
}

/// Converter from typedtree to raw lambda.
pub struct RawLambdaConverter<'a> {
    arena: &'a ParseArena,
    type_ctx: &'a TypeContext,
    env: &'a crate::types::env::Env,
    persistent_env: Option<crate::cmi::persistent_env::PersistentEnv>,
    possible_required_modules: AHashSet<ModuleId>,
    id_gen: IdGenerator,
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
            possible_required_modules: AHashSet::new(),
            id_gen: IdGenerator::new(),
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
            possible_required_modules: AHashSet::new(),
            id_gen: IdGenerator::with_start_stamp(start_stamp),
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
            possible_required_modules: AHashSet::new(),
            id_gen: IdGenerator::with_start_stamp(start_stamp),
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
        }
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

    pub fn take_possible_required_modules(&mut self) -> AHashSet<ModuleId> {
        std::mem::take(&mut self.possible_required_modules)
    }

    pub fn take_diagnostic(&mut self) -> Option<RawLambdaDiagnostic> {
        self.diagnostic.take()
    }

    pub fn take_warnings(&mut self) -> Vec<TypeCoreWarning> {
        std::mem::take(&mut self.warnings)
    }

    fn report_unknown_builtin_primitive(&mut self, loc: Location, prim_name: &str) {
        if prim_name.starts_with('%') {
            self.report_diagnostic(loc, format!("Unknown builtin primitive \"{prim_name}\""));
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

    fn note_possible_required_module(&mut self, id: &Ident, dynamic_import: bool) {
        self.possible_required_modules.insert(ModuleId {
            id: id.clone(),
            kind: Kind::Ml,
            dynamic_import,
        });
    }

    fn note_possible_required_modules_in_raw_lambda(&mut self, lam: &RawLambda) {
        self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(lam, false);
    }

    fn note_possible_required_modules_in_raw_lambda_with_dynamic_import(
        &mut self,
        lam: &RawLambda,
        dynamic_import_scope: bool,
    ) {
        match lam {
            RawLambda::Lvar(_) | RawLambda::Lconst(_) => {}
            RawLambda::LglobalModule(id, dynamic_import) => {
                self.note_possible_required_module(id, dynamic_import_scope || *dynamic_import);
            }
            RawLambda::Lapply(apply) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    &apply.ap_func,
                    false,
                );
                for arg in &apply.ap_args {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        arg, false,
                    );
                }
            }
            RawLambda::Lfunction(func) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    &func.body, false,
                );
            }
            RawLambda::Llet(_, _, value, body) => {
                if dynamic_import_scope {
                    if let RawLambda::LglobalModule(id, dynamic_import) = value.as_ref() {
                        self.note_possible_required_module(
                            id,
                            *dynamic_import || dynamic_import_scope,
                        );
                        return;
                    }
                }
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(value, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
            }
            RawLambda::Lletrec(bindings, body) => {
                for (_, value) in bindings {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        value, false,
                    );
                }
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
            }
            RawLambda::Lprim(info) => {
                let child_dynamic_import =
                    dynamic_import_scope || matches!(info.primitive, Primitive::Pimport);
                for arg in &info.args {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        arg,
                        child_dynamic_import,
                    );
                }
            }
            RawLambda::Lswitch(scrutinee, switch, _) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    scrutinee, false,
                );
                for (_, branch) in &switch.sw_consts {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        branch, false,
                    );
                }
                for (_, branch) in &switch.sw_blocks {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        branch, false,
                    );
                }
                if let Some(failaction) = &switch.sw_failaction {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        failaction, false,
                    );
                }
            }
            RawLambda::LstringSwitch(scrutinee, cases, default) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    scrutinee, false,
                );
                for (_, branch) in cases {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        branch, false,
                    );
                }
                if let Some(default) = default {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        default, false,
                    );
                }
            }
            RawLambda::LstaticRaise(_, args) => {
                for arg in args {
                    self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                        arg, false,
                    );
                }
            }
            RawLambda::LstaticCatch(body, _, handler) | RawLambda::LtryWith(body, _, handler) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    handler, false,
                );
            }
            RawLambda::LifThenElse(cond, then_, else_) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(cond, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(then_, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(else_, false);
            }
            RawLambda::Lsequence(first, second) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(first, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    second, false,
                );
            }
            RawLambda::Lwhile(cond, body) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(cond, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
            }
            RawLambda::Lfor(_, start, finish, _, body) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(start, false);
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    finish, false,
                );
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
            }
            RawLambda::Lfor_of(_, iterable, body) | RawLambda::Lfor_await_of(_, iterable, body) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
                    iterable, false,
                );
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(body, false);
            }
            RawLambda::Lassign(_, value) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(value, false);
            }
            RawLambda::Lsend(_, obj, _) => {
                self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(obj, false);
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
        pat_act_list: Vec<(Pattern, RawLambda)>,
        partial: Partial,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::compile_matching(
            self.type_ctx,
            self.arena,
            handler_fun,
            arg,
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
        pat_act_list: Vec<(Pattern, RawLambda)>,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::for_trywith(
            self.type_ctx,
            self.arena,
            param,
            pat_act_list,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    fn for_multiple_match_with_synced_stamps(
        &mut self,
        loc: Location,
        paraml: Vec<RawLambda>,
        pat_act_list: Vec<(Pattern, RawLambda)>,
        partial: Partial,
    ) -> RawLambda {
        self.sync_matching_stamps();
        let lambda = full_matching::for_multiple_match(
            self.type_ctx,
            self.arena,
            loc,
            paraml,
            pat_act_list,
            partial,
            &mut self.next_static_raise,
        );
        self.sync_matching_stamps();
        lambda
    }

    #[inline]
    fn loc(&self, idx: LocIdx) -> Location {
        self.arena.to_location(idx)
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

    /// Convert typed tree cases to `(Pattern, RawLambda)` pairs for the full
    /// matching compiler. Guards are encoded as
    /// `if guard then body else staticraise(0, [])` per OCaml convention.
    fn cases_to_pat_act_list(&mut self, cases: &[Case]) -> Vec<(Pattern, RawLambda)> {
        cases
            .iter()
            .map(|case| {
                let body = self.convert_expr_raw(&case.c_rhs);
                let act = match &case.c_guard {
                    Some(guard) => {
                        let guard_lam = self.convert_expr_raw(guard);
                        RawLambda::LifThenElse(
                            Box::new(guard_lam),
                            Box::new(body),
                            Box::new(RawLambda::LstaticRaise(0, Vec::new())),
                        )
                    }
                    None => body,
                };
                (case.c_lhs.clone(), act)
            })
            .collect()
    }

    fn id_of_pattern(&mut self, pat: &Pattern) -> Option<Ident> {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => Some(id.clone()),
            PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => match &args[0].pat_desc {
                PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                    Some(id.rename(&self.id_gen))
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

    fn fresh_name_from_cases(&self, default: &str, cases: &[Case]) -> String {
        case_name_hint(default, cases).unwrap_or_else(|| default.to_string())
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
                                    let name = ld
                                        .ld_attributes
                                        .iter()
                                        .find(|a| a.attr_name.txt == "as")
                                        .and_then(|a| match &a.attr_payload {
                                            crate::types::decl::AttributePayload::Str(s) => {
                                                Some(s.clone())
                                            }
                                            _ => None,
                                        })
                                        .unwrap_or_else(|| ld.ld_id.name().to_string());
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
                                    let name = ld
                                        .ld_attributes
                                        .iter()
                                        .find(|a| a.attr_name.txt == "as")
                                        .and_then(|a| match &a.attr_payload {
                                            crate::types::decl::AttributePayload::Str(s) => {
                                                Some(s.clone())
                                            }
                                            _ => None,
                                        })
                                        .unwrap_or_else(|| ld.ld_id.name().to_string());
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
                if let Some(decl) = self.type_ctx.find_type_decl(&path.last()) {
                    if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind
                    {
                        return Some(
                            labels
                                .iter()
                                .enumerate()
                                .map(|(pos, ld)| {
                                    let name = ld
                                        .ld_attributes
                                        .iter()
                                        .find(|a| a.attr_name.txt == "as")
                                        .and_then(|a| match &a.attr_payload {
                                            crate::types::decl::AttributePayload::Str(s) => {
                                                Some(s.clone())
                                            }
                                            _ => None,
                                        })
                                        .unwrap_or_else(|| ld.ld_id.name().to_string());
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
                    }
                }
                SignatureItem::SigModule(id, md, _) => {
                    let module_path = md.md_path.clone().unwrap_or_else(|| {
                        prefix.map_or_else(
                            || crate::types::Path::pident(id.clone()),
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
                if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                    let (expr_idx, attrs) = &**eval_inner;
                    let expr = self.arena.get_expr(*expr_idx);
                    if attrs.is_empty()
                        && let ExpressionDesc::Pexp_ident(ident) = &*expr.pexp_desc
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
        use crate::parser::ast::{Constant, ExpressionDesc, Payload, StructureItemDesc};

        for (located_name, payload) in attrs.iter() {
            if arena.get_string(located_name.txt) != "directive" {
                continue;
            }
            let Payload::PStr(items) = payload else {
                continue;
            };
            let [item] = items.as_slice() else {
                continue;
            };
            let StructureItemDesc::Pstr_eval(eval_inner) = &*item.pstr_desc else {
                continue;
            };
            let (expr_idx, _attrs) = &**eval_inner;
            let expr = arena.get_expr(*expr_idx);
            let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc else {
                continue;
            };
            if let Constant::String(s, _) = &**c {
                return Some(s.to_string());
            }
        }
        None
    }

    /// OCaml's Lambda.make_key: normalize a RawLambda for structural comparison.
    /// - Alias lets are substituted (variable replaced by its definition)
    /// - Other let-bound variables get sequential normalized names
    /// - Locations are ignored
    /// This allows detecting structurally identical actions that differ only
    /// in the stamps of locally-bound variables.
    fn make_action_key(lam: &RawLambda) -> Option<String> {
        use crate::raw_lambda::print::RawLambdaPrinter;

        // Normalize by substituting alias lets and renaming other bound vars
        let mut counter = 0i32;
        let normalized = Self::normalize_for_key(lam, &HashMap::new(), &mut counter)?;
        Some(format!("{}", RawLambdaPrinter::new(&normalized)))
    }

    /// Recursively normalize a RawLambda, substituting alias lets and
    /// renaming other bound variables with sequential stamps.
    fn normalize_for_key(
        lam: &RawLambda,
        env: &HashMap<Ident, RawLambda>,
        counter: &mut i32,
    ) -> Option<RawLambda> {
        match lam {
            RawLambda::Lvar(id) => {
                if let Some(replacement) = env.get(id) {
                    Some(replacement.clone())
                } else {
                    Some(lam.clone())
                }
            }
            RawLambda::Lconst(_) => Some(lam.clone()),
            RawLambda::LglobalModule(_, _) => Some(lam.clone()),
            RawLambda::Llet(LetKind::Alias, id, ex, body) => {
                // Substitute alias lets: replace id with normalized ex in body
                let ex_norm = Self::normalize_for_key(ex, env, counter)?;
                let mut new_env = env.clone();
                new_env.insert(id.clone(), ex_norm);
                Self::normalize_for_key(body, &new_env, counter)
            }
            RawLambda::Llet(kind, id, ex, body) => {
                let ex_norm = Self::normalize_for_key(ex, env, counter)?;
                // Create a normalized variable name
                let norm_id = Ident::new(id.name(), *counter, IdentFlags::NONE);
                *counter += 1;
                let mut new_env = env.clone();
                new_env.insert(id.clone(), RawLambda::Lvar(norm_id.clone()));
                let body_norm = Self::normalize_for_key(body, &new_env, counter)?;
                Some(RawLambda::Llet(
                    *kind,
                    norm_id,
                    Box::new(ex_norm),
                    Box::new(body_norm),
                ))
            }
            RawLambda::Lprim(info) => {
                let mut args = Vec::with_capacity(info.args.len());
                for arg in &info.args {
                    args.push(Self::normalize_for_key(arg, env, counter)?);
                }
                Some(RawLambda::Lprim(crate::raw_lambda::RawPrimInfo {
                    primitive: info.primitive.clone(),
                    args,
                    loc: Location::none(),
                }))
            }
            RawLambda::LifThenElse(cond, then_, else_) => Some(RawLambda::LifThenElse(
                Box::new(Self::normalize_for_key(cond, env, counter)?),
                Box::new(Self::normalize_for_key(then_, env, counter)?),
                Box::new(Self::normalize_for_key(else_, env, counter)?),
            )),
            RawLambda::Lsequence(a, b) => Some(RawLambda::Lsequence(
                Box::new(Self::normalize_for_key(a, env, counter)?),
                Box::new(Self::normalize_for_key(b, env, counter)?),
            )),
            RawLambda::LstaticRaise(i, args) => {
                let mut norm_args = Vec::with_capacity(args.len());
                for arg in args {
                    norm_args.push(Self::normalize_for_key(arg, env, counter)?);
                }
                Some(RawLambda::LstaticRaise(*i, norm_args))
            }
            RawLambda::LstaticCatch(body, (i, params), handler) => {
                let body_norm = Self::normalize_for_key(body, env, counter)?;
                let handler_norm = Self::normalize_for_key(handler, env, counter)?;
                Some(RawLambda::LstaticCatch(
                    Box::new(body_norm),
                    (*i, params.clone()),
                    Box::new(handler_norm),
                ))
            }
            RawLambda::Lapply(ap) => {
                let func = Self::normalize_for_key(&ap.ap_func, env, counter)?;
                let mut args = Vec::with_capacity(ap.ap_args.len());
                for arg in &ap.ap_args {
                    args.push(Self::normalize_for_key(arg, env, counter)?);
                }
                Some(RawLambda::Lapply(crate::raw_lambda::RawApply {
                    ap_func: Box::new(func),
                    ap_args: args,
                    ap_info: crate::lambda::ApInfo {
                        loc: Location::none(),
                        ..ap.ap_info.clone()
                    },
                    ap_transformed_jsx: ap.ap_transformed_jsx,
                }))
            }
            // For complex constructs (functions, letrec, loops, etc.),
            // bail out to avoid complexity — OCaml does the same (Not_simple)
            RawLambda::Lfunction(_)
            | RawLambda::Lletrec(_, _)
            | RawLambda::Lwhile(_, _)
            | RawLambda::Lfor(_, _, _, _, _)
            | RawLambda::Lfor_of(_, _, _)
            | RawLambda::Lfor_await_of(_, _, _) => None,
            RawLambda::Lswitch(scrut, sw, loc) => {
                let scrut_norm = Self::normalize_for_key(scrut, env, counter)?;
                let mut consts = Vec::new();
                for (tag, act) in &sw.sw_consts {
                    consts.push((*tag, Self::normalize_for_key(act, env, counter)?));
                }
                let mut blocks = Vec::new();
                for (tag, act) in &sw.sw_blocks {
                    blocks.push((*tag, Self::normalize_for_key(act, env, counter)?));
                }
                let fail = match &sw.sw_failaction {
                    Some(f) => Some(Box::new(Self::normalize_for_key(f, env, counter)?)),
                    None => None,
                };
                Some(RawLambda::Lswitch(
                    Box::new(scrut_norm),
                    crate::raw_lambda::RawLambdaSwitch {
                        sw_numconsts: sw.sw_numconsts,
                        sw_consts_full: sw.sw_consts_full,
                        sw_consts: consts,
                        sw_numblocks: sw.sw_numblocks,
                        sw_blocks_full: sw.sw_blocks_full,
                        sw_blocks: blocks,
                        sw_failaction: fail,
                        sw_names: sw.sw_names.clone(),
                    },
                    loc.clone(),
                ))
            }
            RawLambda::LtryWith(body, id, handler) => {
                let body_norm = Self::normalize_for_key(body, env, counter)?;
                let handler_norm = Self::normalize_for_key(handler, env, counter)?;
                Some(RawLambda::LtryWith(
                    Box::new(body_norm),
                    id.clone(),
                    Box::new(handler_norm),
                ))
            }
            RawLambda::LstringSwitch(scrut, cases, default) => {
                let scrut_norm = Self::normalize_for_key(scrut, env, counter)?;
                let mut norm_cases = Vec::new();
                for (s, act) in cases {
                    norm_cases.push((s.clone(), Self::normalize_for_key(act, env, counter)?));
                }
                let norm_default = match default {
                    Some(d) => Some(Box::new(Self::normalize_for_key(d, env, counter)?)),
                    None => None,
                };
                Some(RawLambda::LstringSwitch(
                    Box::new(scrut_norm),
                    norm_cases,
                    norm_default,
                ))
            }
            RawLambda::Lassign(id, ex) => Some(RawLambda::Lassign(
                id.clone(),
                Box::new(Self::normalize_for_key(ex, env, counter)?),
            )),
            RawLambda::Lsend(method, obj, loc) => Some(RawLambda::Lsend(
                method.clone(),
                Box::new(Self::normalize_for_key(obj, env, counter)?),
                Location::none(),
            )),
            RawLambda::Lbreak => Some(RawLambda::Lbreak),
            RawLambda::Lcontinue => Some(RawLambda::Lcontinue),
        }
    }

    /// OCaml's share_actions_sw: deduplicate switch actions by wrapping shared
    /// actions in catch/exit. Only actions that appear >= 2 times are wrapped.
    /// Singleton actions are kept inline. Returns the list of catch handlers.
    fn share_actions_sw(
        &mut self,
        sw: &mut crate::raw_lambda::RawLambdaSwitch,
    ) -> Vec<(i32, RawLambda)> {
        use crate::raw_lambda::print::RawLambdaPrinter;

        // Map from action key (string repr) to (exit_id, original_action)
        let mut store: Vec<(String, i32, RawLambda)> = Vec::new();
        let mut handlers: Vec<(i32, RawLambda)> = Vec::new();

        // First pass: count occurrences of each action key
        // Use make_action_key for alpha-normalized comparison (like OCaml's Lambda.make_key)
        let mut key_counts: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        for (_, act) in sw.sw_consts.iter().chain(sw.sw_blocks.iter()) {
            if matches!(act, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                continue;
            }
            let key = Self::make_action_key(act)
                .unwrap_or_else(|| format!("{}", RawLambdaPrinter::new(act)));
            *key_counts.entry(key).or_insert(0) += 1;
        }

        // Second pass: wrap shared actions in catch/exit
        let mut exit_map: std::collections::HashMap<String, i32> = std::collections::HashMap::new();

        for (_tag, action) in sw.sw_consts.iter_mut() {
            if matches!(action, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                continue;
            }
            let key = Self::make_action_key(action)
                .unwrap_or_else(|| format!("{}", RawLambdaPrinter::new(action)));
            let count = key_counts.get(&key).copied().unwrap_or(0);
            if count >= 2 {
                let exit_id = if let Some(&eid) = exit_map.get(&key) {
                    eid
                } else {
                    let eid = self.next_raise_count();
                    exit_map.insert(key.clone(), eid);
                    // OCaml `share_actions_sw` stores the selected action once
                    // and rewrites switch arms through that store
                    // (compiler/ml/matching.ml:1761-1790). Rust owns the arm
                    // slot here, so move the first shared action into the
                    // handler instead of cloning the whole raw-lambda subtree.
                    let original =
                        std::mem::replace(action, RawLambda::LstaticRaise(eid, Vec::new()));
                    handlers.push((eid, original));
                    eid
                };
                if !matches!(action, RawLambda::LstaticRaise(i, args) if *i == exit_id && args.is_empty())
                {
                    *action = RawLambda::LstaticRaise(exit_id, Vec::new());
                }
            }
        }

        for (_tag, action) in sw.sw_blocks.iter_mut() {
            if matches!(action, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                continue;
            }
            let key = Self::make_action_key(action)
                .unwrap_or_else(|| format!("{}", RawLambdaPrinter::new(action)));
            let count = key_counts.get(&key).copied().unwrap_or(0);
            if count >= 2 {
                let exit_id = if let Some(&eid) = exit_map.get(&key) {
                    eid
                } else {
                    let eid = self.next_raise_count();
                    exit_map.insert(key.clone(), eid);
                    // See the const-arm comment above and OCaml
                    // `matching.ml:1761-1790`.
                    let original =
                        std::mem::replace(action, RawLambda::LstaticRaise(eid, Vec::new()));
                    handlers.push((eid, original));
                    eid
                };
                if !matches!(action, RawLambda::LstaticRaise(i, args) if *i == exit_id && args.is_empty())
                {
                    *action = RawLambda::LstaticRaise(exit_id, Vec::new());
                }
            }
        }

        handlers
    }

    /// OCaml's reintroduce_fail: when a switch has no failaction (switch*),
    /// if any static exit appears >= 3 times in the cases, extract it as failaction.
    fn reintroduce_fail(sw: &mut crate::raw_lambda::RawLambdaSwitch) {
        if sw.sw_failaction.is_some() {
            return;
        }

        fn as_simple_exit(lam: &RawLambda) -> Option<i32> {
            match lam {
                RawLambda::LstaticRaise(i, args) if args.is_empty() => Some(*i),
                RawLambda::Llet(LetKind::Alias, _, _, body) => as_simple_exit(body),
                _ => None,
            }
        }

        let mut counts: std::collections::HashMap<i32, i32> = std::collections::HashMap::new();
        for (_, lam) in sw.sw_consts.iter().chain(sw.sw_blocks.iter()) {
            if let Some(i) = as_simple_exit(lam) {
                *counts.entry(i).or_insert(0) += 1;
            }
        }

        let mut best_exit = -1i32;
        let mut best_count = -1i32;
        for (&exit_id, &count) in &counts {
            // Tie-break: choose the largest index (matches OCaml)
            if count > best_count || (count == best_count && exit_id > best_exit) {
                best_exit = exit_id;
                best_count = count;
            }
        }

        if best_count >= 3 {
            sw.sw_consts
                .retain(|(_, lam)| as_simple_exit(lam) != Some(best_exit));
            sw.sw_blocks
                .retain(|(_, lam)| as_simple_exit(lam) != Some(best_exit));
            sw.sw_failaction = Some(Box::new(RawLambda::LstaticRaise(best_exit, Vec::new())));
        }
    }

    /// Build a switch, wrapping the failaction in catch/exit to match OCaml's
    /// matching.ml behavior where default actions are shared through static catch.
    fn make_switch_with_catch(
        &mut self,
        scrut: RawLambda,
        mut const_cases: Vec<(i32, RawLambda)>,
        mut block_cases: Vec<(i32, RawLambda)>,
        failaction: Option<Box<RawLambda>>,
    ) -> RawLambda {
        self.make_switch_with_catch_exit(scrut, const_cases, block_cases, failaction, None)
    }

    fn make_switch_with_catch_exit(
        &mut self,
        scrut: RawLambda,
        mut const_cases: Vec<(i32, RawLambda)>,
        mut block_cases: Vec<(i32, RawLambda)>,
        failaction: Option<Box<RawLambda>>,
        pre_exit: Option<i32>,
    ) -> RawLambda {
        // OCaml's matching.ml sorts cases by tag via sort_int_lambda_list/split_cases
        const_cases.sort_by_key(|(tag, _)| *tag);
        block_cases.sort_by_key(|(tag, _)| *tag);
        match failaction {
            Some(default) => {
                let exit_id = pre_exit.unwrap_or_else(|| self.next_raise_count());
                let switch = RawLambda::Lswitch(
                    Box::new(scrut),
                    crate::raw_lambda::RawLambdaSwitch {
                        sw_numconsts: const_cases.len(),
                        sw_consts_full: false,
                        sw_consts: const_cases,
                        sw_numblocks: block_cases.len(),
                        sw_blocks_full: false,
                        sw_blocks: block_cases,
                        sw_failaction: Some(Box::new(RawLambda::LstaticRaise(exit_id, Vec::new()))),
                        sw_names: None,
                    },
                    Location::none(),
                );
                RawLambda::LstaticCatch(Box::new(switch), (exit_id, Vec::new()), default)
            }
            None => {
                let mut sw = crate::raw_lambda::RawLambdaSwitch {
                    sw_numconsts: const_cases.len(),
                    sw_consts_full: false,
                    sw_consts: const_cases,
                    sw_numblocks: block_cases.len(),
                    sw_blocks_full: false,
                    sw_blocks: block_cases,
                    sw_failaction: None,
                    sw_names: None,
                };
                // OCaml: share_actions_sw then reintroduce_fail
                let share_handlers = self.share_actions_sw(&mut sw);
                Self::reintroduce_fail(&mut sw);
                let mut result = RawLambda::Lswitch(Box::new(scrut), sw, Location::none());
                // Wrap with catch handlers from share_actions_sw.
                // OCaml's handle_shared composes handlers as h(ohs(x)),
                // so the first shared action is innermost. We iterate forward
                // to match: first handler becomes innermost catch.
                for (exit_id, handler) in share_handlers.into_iter() {
                    result = RawLambda::LstaticCatch(
                        Box::new(result),
                        (exit_id, Vec::new()),
                        Box::new(handler),
                    );
                }
                result
            }
        }
    }

    /// Apply inline attribute to a raw lambda expression, matching OCaml's
    /// Translattribute.add_inline_attribute. Walks through Lprim wrappers
    /// to find the inner Lfunction.
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
            RawLambda::Lprim(mut prim)
                if matches!(
                    prim.primitive,
                    Primitive::PjsFnMake(_) | Primitive::PjsFnMakeUnit
                ) && prim.args.len() == 1 =>
            {
                let inner = prim
                    .args
                    .pop()
                    .expect("checked single Pjs_fn_make argument");
                prim.args
                    .push(self.apply_inline_attribute_raw(inner, loc, inline));
                RawLambda::Lprim(prim)
            }
            other => {
                let name = match inline {
                    InlineAttribute::Always => "inline1",
                    InlineAttribute::Never => "inline2",
                    InlineAttribute::Default => return other,
                };
                self.report_warning(
                    loc,
                    Warning::MisplacedAttribute {
                        name: name.to_string(),
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
            crate::types::Path::papply(path.clone(), crate::types::Path::pident(param.clone()))
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
        let loc = self.loc(ext.ext_loc);
        match &ext.ext_kind {
            crate::types::typedtree::ExtensionConstructorKind::Text_decl(_, _) => {
                RawLambda::prim(Primitive::PcreateExtension(name), vec![], loc)
            }
            crate::types::typedtree::ExtensionConstructorKind::Text_rebind(path, _) => {
                self.translate_extension_path_raw(path, loc)
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
                    ext.ext_id.clone(),
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

    fn is_function_type(&self, ty: TypeExprRef) -> Option<(TypeExprRef, TypeExprRef)> {
        self.is_function_type_with_env(ty, self.env)
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

    /// Like is_function_type but only matches when the argument has no label (Nolabel).
    /// Matches OCaml's check: Tarrow ({lbl = Nolabel; typ}, ...)
    fn is_nolabel_function_type(&self, ty: TypeExprRef) -> Option<(TypeExprRef, TypeExprRef)> {
        self.is_nolabel_function_type_with_env(ty, self.env)
    }

    fn is_nolabel_function_type_with_env(
        &self,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
    ) -> Option<(TypeExprRef, TypeExprRef)> {
        let ty = self.type_ctx.repr(ty);
        if let Some((label, arg, ret)) =
            crate::types::ctype::split_arrow_with_label(self.type_ctx, ty)
        {
            return matches!(label, crate::types::asttypes::ArgLabel::Nolabel)
                .then_some((arg, ret));
        }
        match &*self.type_ctx.get_desc(ty) {
            TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => {
                self.is_nolabel_function_type_with_env(*next, env)
            }
            TypeDesc::Tconstr { .. } => {
                let expanded = crate::types::ctype::expand_head(self.type_ctx, env, ty);
                if expanded == ty {
                    None
                } else {
                    self.is_nolabel_function_type_with_env(expanded, env)
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

    fn is_immediate_type(&self, ty: TypeExprRef) -> bool {
        self.is_immediate_type_with_env(ty, self.env)
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
                    crate::raw_lambda::typeopt::find_type_decl_pub(self.type_ctx, env, path)
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

    fn raw_loc_constant(&self, kind: RawLocKind, loc: Location) -> RawLambda {
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
                tag: 0,
                tag_info: TagInfo::Tuple,
                elements: vec![
                    Constant::ImmString(file),
                    Constant::int(line),
                    Constant::int(start_col),
                    Constant::int(end_col),
                ],
            }),
        }
    }

    fn value_path_loc_constant(
        &self,
        path: &crate::types::Path,
        loc: Location,
    ) -> Option<RawLambda> {
        let crate::types::Path::Pdot(prefix, name, _) = path else {
            return None;
        };
        let crate::types::Path::Pident(id) = &**prefix else {
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

    fn failure_payload(&self, loc: Location) -> Constant {
        Constant::Block {
            tag: 0,
            tag_info: TagInfo::Tuple,
            elements: vec![
                Constant::string_with_delim(self.basename_for_loc(loc), StringDelim::Plain),
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

    fn raw_assert_failed(&self, loc: Location) -> RawLambda {
        RawLambda::from_lowered(self.raise_predef_exception(
            "Assert_failure",
            PREDEF_ASSERT_FAILURE_STAMP,
            loc,
        ))
    }

    fn raw_assert_false(&self, loc: Location) -> RawLambda {
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

    fn assert_failed_lambda(&self, loc: Location) -> Lambda {
        self.raise_predef_exception("Assert_failure", PREDEF_ASSERT_FAILURE_STAMP, loc)
    }

    fn assert_false_lambda(&self, loc: Location) -> Lambda {
        // Same branch as compiler/ml/translcore.ml:926-928.
        if self.no_assert_false {
            Lambda::const_(Constant::int_with_comment(0, PointerInfo::AssertFalse))
        } else {
            self.assert_failed_lambda(loc)
        }
    }

    fn has_only_expr_attr(&self, expr: &Expression, name: &str) -> bool {
        expr.exp_attributes.len() == 1
            && self.arena.get_string(expr.exp_attributes[0].0.txt) == name
    }

    fn wrap_raw_function_bindings(
        &self,
        expr: Expression,
        bindings: &[RawFunctionBinding],
    ) -> Expression {
        bindings.iter().fold(expr, |expr, binding| match binding {
            RawFunctionBinding::Value(binds) => {
                let mut wrapped = expr;
                let body = wrapped.clone();
                wrapped.exp_desc = ExpressionDesc::Texp_let(
                    crate::parser::ast::RecFlag::Nonrecursive,
                    binds.clone(),
                    Box::new(body),
                );
                wrapped
            }
            RawFunctionBinding::Module(id, name, mexpr) => {
                let mut wrapped = expr;
                let body = wrapped.clone();
                wrapped.exp_desc = ExpressionDesc::Texp_letmodule(
                    id.clone(),
                    name.clone(),
                    Box::new(mexpr.clone()),
                    Box::new(body),
                );
                wrapped
            }
        })
    }

    fn push_raw_function_binding_refs<'b>(
        bindings: &mut Vec<RawFunctionBindingRef<'b>>,
        pending: Vec<RawFunctionBindingRef<'b>>,
    ) {
        if pending.is_empty() {
            return;
        }
        let old = std::mem::take(bindings);
        bindings.reserve(pending.len() + old.len());
        bindings.extend(pending);
        bindings.extend(old);
    }

    fn strip_default_bindings_before_function<'b>(
        &self,
        mut rhs: &'b Expression,
    ) -> (&'b Expression, Vec<RawFunctionBindingRef<'b>>) {
        let mut bindings = Vec::new();
        loop {
            match &rhs.exp_desc {
                ExpressionDesc::Texp_let(
                    crate::parser::ast::RecFlag::Nonrecursive,
                    binds,
                    inner,
                ) if self.has_only_expr_attr(rhs, "#default")
                    && matches!(inner.exp_desc, ExpressionDesc::Texp_function { .. }) =>
                {
                    bindings.push(RawFunctionBindingRef::Value(binds));
                    rhs = inner;
                }
                ExpressionDesc::Texp_letmodule(_id, _name, _mexpr, inner)
                    if self.has_only_expr_attr(rhs, "#modulepat")
                        && matches!(inner.exp_desc, ExpressionDesc::Texp_function { .. }) =>
                {
                    if let ExpressionDesc::Texp_letmodule(id, _name, mexpr, _) = &rhs.exp_desc {
                        bindings.push(RawFunctionBindingRef::Module(id, mexpr));
                    }
                    rhs = inner;
                }
                _ => return (rhs, bindings),
            }
        }
    }

    fn wrap_raw_function_binding_refs(
        &mut self,
        mut body: RawLambda,
        bindings: &[RawFunctionBindingRef<'_>],
    ) -> RawLambda {
        for binding in bindings {
            body = match binding {
                RawFunctionBindingRef::Value(binds) => self.convert_let_with_body_raw(
                    crate::parser::ast::RecFlag::Nonrecursive,
                    binds,
                    body,
                ),
                RawFunctionBindingRef::Module(id, mexpr) => RawLambda::let_(
                    LetKind::Strict,
                    (*id).clone(),
                    self.convert_module_expr_raw(mexpr, &None),
                    body,
                ),
            };
        }
        body
    }

    fn push_defaults_case(&self, bindings: Vec<RawFunctionBinding>, case: &Case) -> Case {
        if case.c_guard.is_none() {
            match &case.c_rhs.exp_desc {
                ExpressionDesc::Texp_function {
                    params,
                    body,
                    partial,
                    arity,
                    async_,
                } => {
                    let pushed_body = body
                        .iter()
                        .map(|inner_case| self.push_defaults_case(bindings.clone(), inner_case))
                        .collect::<Vec<_>>();
                    let mut rhs = case.c_rhs.clone();
                    rhs.exp_desc = ExpressionDesc::Texp_function {
                        params: params.clone(),
                        body: pushed_body,
                        partial: *partial,
                        arity: *arity,
                        async_: *async_,
                    };
                    return Case {
                        c_lhs: case.c_lhs.clone(),
                        c_guard: None,
                        c_rhs: rhs,
                    };
                }
                ExpressionDesc::Texp_let(
                    crate::parser::ast::RecFlag::Nonrecursive,
                    binds,
                    inner,
                ) if self.has_only_expr_attr(&case.c_rhs, "#default")
                    && matches!(inner.exp_desc, ExpressionDesc::Texp_function { .. }) =>
                {
                    let mut next_bindings = Vec::with_capacity(bindings.len() + 1);
                    next_bindings.push(RawFunctionBinding::Value(binds.clone()));
                    next_bindings.extend(bindings);
                    let mut next_case = case.clone();
                    next_case.c_rhs = (**inner).clone();
                    return self.push_defaults_case(next_bindings, &next_case);
                }
                ExpressionDesc::Texp_letmodule(id, name, mexpr, inner)
                    if self.has_only_expr_attr(&case.c_rhs, "#modulepat")
                        && matches!(inner.exp_desc, ExpressionDesc::Texp_function { .. }) =>
                {
                    let mut next_bindings = Vec::with_capacity(bindings.len() + 1);
                    next_bindings.push(RawFunctionBinding::Module(
                        id.clone(),
                        name.clone(),
                        (**mexpr).clone(),
                    ));
                    next_bindings.extend(bindings);
                    let mut next_case = case.clone();
                    next_case.c_rhs = (**inner).clone();
                    return self.push_defaults_case(next_bindings, &next_case);
                }
                _ => {}
            }
        }

        Case {
            c_lhs: case.c_lhs.clone(),
            c_guard: case.c_guard.clone(),
            c_rhs: self.wrap_raw_function_bindings(case.c_rhs.clone(), &bindings),
        }
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

    fn specialize_comparison(&self, table: ComparisonSpecialization, ty: TypeExprRef) -> Primitive {
        self.specialize_comparison_in_env(table, ty, self.env)
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
        matches!(
            &expr.exp_desc,
            ExpressionDesc::Texp_construct(
                _,
                crate::types::ConstructorDescription {
                    cstr_tag: ConstructorTag::CstrConstant(_),
                    ..
                },
                _
            ) | ExpressionDesc::Texp_variant(_, None)
        )
    }

    fn find_raw_primitive(&self, prim_name: &str) -> Option<Primitive> {
        match prim_name {
            "%makeref" => Some(Primitive::Pmakeblock(
                0,
                TagInfo::ref_tag(),
                Mutable::Mutable,
            )),
            "%refset" => Some(Primitive::Psetfield(
                0,
                crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet("contents".to_string()),
            )),
            "%refget" => Some(Primitive::Pfield(
                0,
                FieldDbgInfo::Record {
                    name: "contents".to_string(),
                    mutable_flag: ParserMutableFlag::Mutable,
                },
            )),
            "%incr" => Some(Primitive::Poffsetref(1)),
            "%decr" => Some(Primitive::Poffsetref(-1)),
            "%identity" => Some(Primitive::Pidentity),
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
            "%succint" => Some(Primitive::Poffsetint(1)),
            "%predint" => Some(Primitive::Poffsetint(-1)),
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
            "%import" => Some(Primitive::Pimport),
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
            "%wrap_exn" => Some(Primitive::PwrapExn),
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
            "#raw_expr" => Some(Primitive::PrawJsCode(
                crate::lambda::lam_primitive::JsRawInfo {
                    code: String::new(),
                    is_stmt: false,
                },
            )),
            "#raw_stmt" => Some(Primitive::PrawJsCode(
                crate::lambda::lam_primitive::JsRawInfo {
                    code: String::new(),
                    is_stmt: true,
                },
            )),
            "#null" => Some(Primitive::Pnull),
            "#undefined" => Some(Primitive::Pundefined),
            "#typeof" => Some(Primitive::Ptypeof),
            "#is_nullable" => Some(Primitive::PisNullUndefined),
            "#null_to_opt" => Some(Primitive::PnullToOpt),
            "#nullable_to_opt" => Some(Primitive::PnullUndefinedToOpt),
            "#import" => Some(Primitive::Pimport),
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

    /// Port of OCaml's Translcore.transl_primitive.
    /// Creates a lambda wrapper for a primitive operation, used when a primitive
    /// value needs to be coerced to a regular value (e.g., in module inclusion).
    fn transl_primitive_raw(
        &mut self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        loc: Location,
    ) -> RawLambda {
        let raw_name = Self::raw_primitive_name(&prim.prim_name).to_string();
        let resolved = self.specialize_primitive_raw(prim, ty).unwrap_or_else(|| {
            self.report_unknown_builtin_primitive(loc.clone(), &raw_name);
            Primitive::PjsCall {
                prim_name: raw_name,
                arg_types: decoded_external_arg_types(
                    &prim.prim_native_name,
                    prim.prim_arity.max(0) as usize,
                ),
                ffi: self.ffi_spec_for_primitive(
                    prim,
                    self.applied_result_is_builtin_object(ty, prim.prim_arity.max(0) as usize),
                    self.applied_result_is_unit(ty, prim.prim_arity.max(0) as usize),
                ),
                dynamic_import: false,
                transformed_jsx: false,
            }
        });

        let prim_arity = prim.prim_arity;

        // OCaml: if p.prim_from_constructor || prim_arity = 0 then Lprim (prim, [], loc)
        if prim.prim_from_constructor || prim_arity == 0 {
            return RawLambda::prim(resolved, vec![], loc);
        }

        // Create parameter idents matching OCaml's naming
        let params: Vec<Ident> = if prim_arity == 1 {
            vec![self.fresh_ident("prim")]
        } else {
            (0..prim_arity)
                .map(|i| self.fresh_ident(&format!("prim{}", i)))
                .collect()
        };

        let args: Vec<RawLambda> = params.iter().map(|id| RawLambda::var(id.clone())).collect();

        RawLambda::function_(
            prim_arity,
            params,
            RawLambda::prim(resolved, args, loc.clone()),
            FunctionAttribute::default(),
        )
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

    fn translate_primitive_application_raw(
        &mut self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        args: &[&Expression],
        transformed_jsx: bool,
        loc: Location,
    ) -> Primitive {
        let prim_name = Self::raw_primitive_name(&prim.prim_name).to_string();

        if let [arg1] | [arg1, _] = args {
            if let Some(primitive) = self.translate_unified_ops_primitive(&prim_name, arg1.exp_type)
            {
                return primitive;
            }
        }

        if let [arg1, _] = args {
            if let Some(table) = Self::comparison_specialization(&prim_name) {
                if self.is_base_type(arg1.exp_type, "bool") {
                    return table.boolcomp;
                }
                if args
                    .iter()
                    .any(|arg| Self::has_constant_constructor_arg(arg))
                    && table.simplify_constant_constructor
                {
                    return table.intcomp;
                }
                // Use arg's type directly for specialization, matching OCaml's
                // transl_prim_2 which checks the arg's exp_type via its env.
                // specialize_primitive_raw falls back to funct.exp_type with self.env
                // which may not have local type definitions, causing incorrect expansion.
                return self.specialize_comparison_with_env(table, arg1);
            }
        }

        if let Some(primitive) = self.specialize_primitive_raw(prim, ty) {
            primitive
        } else {
            self.report_unknown_builtin_primitive(loc, &prim_name);
            Primitive::PjsCall {
                prim_name,
                arg_types: decoded_external_arg_types(
                    &prim.prim_native_name,
                    prim.prim_arity.max(0) as usize,
                ),
                ffi: self.ffi_spec_for_primitive(
                    prim,
                    self.applied_result_is_builtin_object(ty, args.len()),
                    self.applied_result_is_unit(ty, args.len()),
                ),
                dynamic_import: false,
                transformed_jsx,
            }
        }
    }

    fn raw_lambda_is_nullish_constant(lam: &RawLambda) -> bool {
        matches!(
            lam,
            RawLambda::Lconst(Constant::JsNull | Constant::JsUndefined { .. })
                | RawLambda::Lprim(crate::raw_lambda::RawPrimInfo {
                    primitive: Primitive::Pnull | Primitive::Pundefined,
                    ..
                })
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
            {
                return;
            }
            Primitive::Pobjcomp(_)
            | Primitive::Pobjorder
            | Primitive::Pobjmin
            | Primitive::Pobjmax => {
                self.report_warning(loc, Warning::BsPolymorphicComparison);
            }
            _ => {}
        }
    }

    fn ffi_spec_for_primitive(
        &self,
        prim: &crate::types::PrimitiveDescription,
        object_result: bool,
        returns_unit: bool,
    ) -> ExternalFfiSpec {
        let ffi_marshaled = decode_marshaled_ffi_type(&prim.prim_native_name);
        let kind = if !is_bs_primitive(&prim.prim_native_name) {
            ExternalFfiKind::Normal
        } else if object_result
            || ffi_marshaled
                .as_ref()
                .is_some_and(ffi_marshaled_is_obj_create)
        {
            ExternalFfiKind::ObjCreate
        } else {
            ExternalFfiKind::Default
        };
        let return_wrapper = ffi_marshaled
            .as_ref()
            .and_then(ffi_marshaled_return_wrapper)
            .unwrap_or_else(|| {
                if returns_unit {
                    ExternalReturnWrapper::ReplacedWithUnit
                } else {
                    ExternalReturnWrapper::Identity
                }
            });
        ExternalFfiSpec {
            kind,
            spec: ffi_marshaled.as_ref().and_then(ffi_marshaled_external_spec),
            obj_params: ffi_marshaled.as_ref().and_then(ffi_marshaled_obj_params),
            return_wrapper,
            inline_constant: ffi_marshaled
                .as_ref()
                .and_then(ffi_marshaled_inline_constant),
        }
    }

    fn applied_result_is_builtin_object(&self, ty: TypeExprRef, applied_args: usize) -> bool {
        let mut current = ty;
        for _ in 0..applied_args {
            let expanded = crate::types::ctype::expand_head(self.type_ctx, self.env, current);
            let repr = self.type_ctx.repr(expanded);
            let desc = self.type_ctx.get_desc(repr);
            let next = match &*desc {
                TypeDesc::Tarrow { ret, .. } => Some(*ret),
                TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => Some(*next),
                _ => None,
            };
            drop(desc);
            let Some(next) = next else {
                return false;
            };
            current = next;
        }
        type_is_builtin_object(self.type_ctx, self.env, current)
    }

    fn applied_result_is_unit(&self, ty: TypeExprRef, applied_args: usize) -> bool {
        let mut current = ty;
        for _ in 0..applied_args {
            let expanded = crate::types::ctype::expand_head(self.type_ctx, self.env, current);
            let repr = self.type_ctx.repr(expanded);
            let desc = self.type_ctx.get_desc(repr);
            let next = match &*desc {
                TypeDesc::Tarrow { ret, .. } => Some(*ret),
                TypeDesc::Tlink(next) | TypeDesc::Tsubst(next) => Some(*next),
                _ => None,
            };
            drop(desc);
            let Some(next) = next else {
                return false;
            };
            current = next;
        }
        self.is_base_type(current, "unit")
    }

    fn extract_constant_raw(lam: &RawLambda) -> Option<Constant> {
        match lam {
            RawLambda::Lconst(c) => Some(c.clone()),
            _ => None,
        }
    }

    fn raw_block_or_prim(
        &self,
        tag: i32,
        tag_info: TagInfo,
        elems: Vec<RawLambda>,
        loc: Location,
    ) -> RawLambda {
        if let Some(constants) = elems
            .iter()
            .map(Self::extract_constant_raw)
            .collect::<Option<Vec<_>>>()
        {
            RawLambda::const_(Constant::Block {
                tag,
                tag_info,
                elements: constants,
            })
        } else {
            RawLambda::prim(
                Primitive::Pmakeblock(tag, tag_info, Mutable::Immutable),
                elems,
                loc,
            )
        }
    }

    fn raw_constructor_tag_info(
        &self,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
        fallback_env: EnvRef,
    ) -> TagInfo {
        match &cstr.cstr_tag {
            ConstructorTag::CstrBlock(_) if constructor_has_optional_shape(cstr) => match args {
                [arg] => {
                    let arg_env_skip = self.type_ctx.get_typed_env(arg.exp_env).map(|env| {
                        type_cannot_contain_undefined(self.type_ctx, env.as_ref(), arg.exp_type)
                    });
                    let fallback_env_skip = self.type_ctx.get_typed_env(fallback_env).map(|env| {
                        type_cannot_contain_undefined(self.type_ctx, env.as_ref(), arg.exp_type)
                    });
                    let no_env_skip =
                        type_cannot_contain_undefined_no_env(self.type_ctx, arg.exp_type);
                    let can_skip = arg_env_skip.unwrap_or(false)
                        || fallback_env_skip.unwrap_or(false)
                        || no_env_skip;
                    if can_skip {
                        TagInfo::SomeNotNested
                    } else {
                        TagInfo::Some
                    }
                }
                _ => TagInfo::Some,
            },
            ConstructorTag::CstrBlock(tag) => TagInfo::Constructor {
                name: cstr.cstr_name.clone(),
                num_nonconst: cstr.cstr_nonconsts,
                tag: *tag,
                attrs: lower_tag_info_attributes(&cstr.cstr_attributes),
            },
            _ => TagInfo::Constructor {
                name: cstr.cstr_name.clone(),
                num_nonconst: cstr.cstr_nonconsts,
                tag: 0,
                attrs: lower_tag_info_attributes(&cstr.cstr_attributes),
            },
        }
    }

    fn convert_construct_raw(
        &mut self,
        loc: Location,
        fallback_env: EnvRef,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
    ) -> RawLambda {
        if cstr.cstr_inlined.is_some() {
            return match args {
                [arg] => match &arg.exp_desc {
                    ExpressionDesc::Texp_record {
                        fields,
                        extended_expression,
                    } => self.convert_record_raw(
                        self.loc(arg.exp_loc),
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
                            self.loc(arg.exp_loc),
                            &record_fields,
                            None,
                            inlined_record_representation(cstr),
                            logical_field_count,
                        )
                    }
                    _ => self.convert_expr_raw(arg),
                },
                [] if matches!(cstr.cstr_tag, ConstructorTag::CstrUnboxed) => {
                    RawLambda::const_(raw_constructor_constant(cstr, 0))
                }
                _ => RawLambda::unit(),
            };
        }

        match &cstr.cstr_tag {
            ConstructorTag::CstrConstant(tag) => match cstr.cstr_name.as_str() {
                "true" => RawLambda::const_(Constant::JsTrue),
                "false" => RawLambda::const_(Constant::JsFalse),
                _ => RawLambda::const_(raw_constructor_constant(cstr, *tag)),
            },
            ConstructorTag::CstrUnboxed => match args {
                [arg] => self.convert_expr_raw(arg),
                [] => RawLambda::const_(raw_constructor_constant(cstr, 0)),
                _ => RawLambda::unit(),
            },
            ConstructorTag::CstrBlock(tag) => {
                let elems = args.iter().map(|arg| self.convert_expr_raw(arg)).collect();
                let tag_info = self.raw_constructor_tag_info(cstr, args, fallback_env);
                self.raw_block_or_prim(*tag, tag_info, elems, loc)
            }
            ConstructorTag::CstrExtension(path) => {
                let mut args_lam = Vec::with_capacity(args.len() + 1);
                args_lam.push(self.translate_extension_path_raw(path, loc));
                args_lam.extend(args.iter().map(|arg| self.convert_expr_raw(arg)));
                RawLambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
                    args_lam,
                    loc,
                )
            }
        }
    }

    fn convert_record_raw(
        &mut self,
        loc: Location,
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
            // OCaml wraps the init expression in a let binding when there's a
            // base expression, so field accesses use Lvar(init_id) not the expr.
            let init_id = base_lam.as_ref().map(|_| self.fresh_ident("init"));
            let init_var = init_id.as_ref().map(|id| RawLambda::var(id.clone()));

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
                                self.loc(lid.loc),
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
                                0,
                                TagInfo::Record {
                                    fields: fields_info,
                                    logical_field_count,
                                    mutable_flag,
                                },
                                Mutable::Mutable,
                            ),
                            elems,
                            loc,
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
                    [value] => {
                        // OCaml: uncurried encoding - if label starts with 'I',
                        // extract arity and wrap with #fn_mk(arity)
                        let first_lbl_name = &fields[0].1.lbl_name;
                        if first_lbl_name.starts_with('I') {
                            if let Ok(arity) = first_lbl_name[1..].parse::<i32>() {
                                RawLambda::prim(
                                    Primitive::PjsFnMake(arity),
                                    vec![value.clone()],
                                    loc,
                                )
                            } else {
                                value.clone()
                            }
                        } else {
                            value.clone()
                        }
                    }
                    _ => RawLambda::unit(),
                },
                RecordRepresentation::RecordInlined {
                    tag,
                    name,
                    num_nonconsts,
                    attrs,
                } => {
                    let tag_info = TagInfo::RecordInlined {
                        name,
                        num_nonconst: num_nonconsts,
                        tag,
                        fields: fields_info,
                        logical_field_count,
                        mutable_flag,
                        attrs: lower_tag_info_attributes(&attrs),
                    };
                    // OCaml: if mut = Mutable then raise Not_constant
                    if matches!(mutable_flag, ParserMutableFlag::Mutable) {
                        RawLambda::prim(
                            Primitive::Pmakeblock(tag, tag_info, Mutable::Mutable),
                            elems,
                            loc,
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
                            0,
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
                        loc,
                    )
                }
            };
            // Wrap with let init = base_expr when there's a base expression
            return match (init_id, base_lam) {
                (Some(id), Some(base_expr)) => {
                    RawLambda::let_(LetKind::Strict, id, base_expr, result)
                }
                _ => result,
            };
        }

        let Some(init_expr) = base_lam else {
            return RawLambda::unit();
        };

        let copy_id = self.fresh_ident("newrecord");
        let mut body = RawLambda::var(copy_id.clone());
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
                vec![RawLambda::var(copy_id.clone()), self.convert_expr_raw(expr)],
                loc,
            );
            body = RawLambda::seq(update, body);
        }

        RawLambda::let_(
            LetKind::Strict,
            copy_id,
            RawLambda::prim(Primitive::Pduprecord, vec![init_expr], loc),
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
            .map(|(lid, _, _, _)| lid.clone())
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
                    label_lid.clone(),
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
        loc: Location,
    ) -> RawLambda {
        ids.iter().rev().fold(body, |acc, (id, pos)| {
            RawLambda::let_(
                LetKind::Alias,
                id.clone(),
                RawLambda::prim(
                    Primitive::Pfield(
                        *pos as i32,
                        FieldDbgInfo::Module {
                            name: id.name().to_string(),
                        },
                    ),
                    vec![RawLambda::var(mid.clone())],
                    loc,
                ),
                acc,
            )
        })
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
        let mut fields = Vec::new();
        let result = self.convert_structure_items_raw(
            &mut fields,
            &structure.str_items,
            true,
            &self.global_path(),
            cc,
            Location::none(),
        );
        result
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
                let body = f(self, id.clone());
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
        loc: Location,
    ) -> RawLambda {
        match path {
            crate::types::Path::Pident(id) => {
                if id.is_global() {
                    RawLambda::global_module(id.clone(), false)
                } else {
                    RawLambda::var(id.clone())
                }
            }
            crate::types::Path::Pdot(prefix, name, pos) => {
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
                    Primitive::Pfield(resolved_pos, FieldDbgInfo::Module { name: name.clone() }),
                    vec![prefix_lam],
                    loc,
                )
            }
            crate::types::Path::Papply(_, _) => RawLambda::unit(),
        }
    }

    fn translate_normal_path_raw(&mut self, path: &crate::types::Path, loc: Location) -> RawLambda {
        self.translate_normal_path_raw_in_env(self.env, path, loc)
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
                    ModuleType::MtySignature(sig) => sig.into_iter().find_map(|item| match item {
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
                    if let crate::types::Path::Pdot(prefix, name, _) = module_path {
                        // OCaml compiler/ml/env.ml:903-913 normalizes dotted
                        // paths through find_module; recover the same nested
                        // module type from the parent signature when this env
                        // has not stored the dotted path as a direct binding.
                        let parent_mty = module_type_for_path(this, env, prefix)?;
                        return submodule_type_from_module_type(
                            this, env, prefix, parent_mty, name, 0,
                        );
                    }
                    if let crate::types::Path::Pident(id) = module_path
                        && (id.is_persistent() || id.is_global())
                    {
                        let sig = this
                            .persistent_env
                            .as_mut()?
                            .read_raw_sig(id.name(), this.type_ctx)?;
                        Some(ModuleType::MtySignature(sig))
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

        match path {
            crate::types::Path::Pident(id) if id.is_persistent() || id.is_global() => self
                .persistent_env
                .as_mut()
                .and_then(|pers| pers.find_pers_struct(id.name(), self.type_ctx))
                .is_some(),
            _ => false,
        }
    }

    fn module_declaration_for_path_normalization<'e>(
        env: &'e crate::types::env::Env,
        path: &crate::types::Path,
    ) -> Option<&'e crate::types::decl::ModuleDeclaration> {
        match path {
            // OCaml Env.find_module resolves Pident through IdTbl.find_same
            // (compiler/ml/env.ml:865-875). Do not let an opened same-name
            // component answer for an already-selected persistent root.
            crate::types::Path::Pident(id) => env.find_module_same(id).ok(),
            crate::types::Path::Pdot(..) => env.lookup_module(path).ok(),
            crate::types::Path::Papply(..) => None,
        }
    }

    fn normalize_module_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        let path = match path {
            crate::types::Path::Pdot(prefix, name, pos) => crate::types::Path::Pdot(
                std::sync::Arc::new(self.normalize_module_path_in_env(env, prefix)),
                name.clone(),
                *pos,
            ),
            crate::types::Path::Papply(left, right) => crate::types::Path::Papply(
                std::sync::Arc::new(self.normalize_module_path_in_env(env, left)),
                std::sync::Arc::new(self.normalize_module_path_in_env(env, right)),
            ),
            crate::types::Path::Pident(_) => path.clone(),
        };

        if matches!(&path, crate::types::Path::Pdot(..))
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
            return self.normalize_module_path_in_env(env, &alias_target);
        }

        if let Some(md) = Self::module_declaration_for_path_normalization(env, &path) {
            match &md.md_type {
                crate::types::decl::ModuleType::MtyAlias(_, alias_path) => {
                    if !alias_path.same(&path) {
                        return self.normalize_module_path_in_env(env, alias_path);
                    }
                }
                crate::types::decl::ModuleType::MtyIdent(alias_path)
                    if Self::path_may_follow_mty_ident(&path)
                        && !alias_path.same(&path)
                        && self.module_path_resolves_to_runtime_module(env, alias_path) =>
                {
                    return self.normalize_module_path_in_env(env, alias_path);
                }
                _ => {}
            }
        }

        if matches!(&path, crate::types::Path::Pdot(..)) || Self::path_may_follow_mty_ident(&path) {
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
                    return self.normalize_module_path_in_env(env, &alias_target);
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
                    return self.normalize_module_path_in_env(env, &alias_target);
                }
            }
        }
        path
    }

    fn normalize_value_prefix_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        let path = match path {
            crate::types::Path::Pdot(prefix, name, pos) => crate::types::Path::Pdot(
                std::sync::Arc::new(self.normalize_value_prefix_path_in_env(env, prefix)),
                name.clone(),
                *pos,
            ),
            crate::types::Path::Papply(left, right) => crate::types::Path::Papply(
                std::sync::Arc::new(self.normalize_value_prefix_path_in_env(env, left)),
                std::sync::Arc::new(self.normalize_value_prefix_path_in_env(env, right)),
            ),
            crate::types::Path::Pident(_) => path.clone(),
        };

        if matches!(&path, crate::types::Path::Pdot(..))
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

        if matches!(&path, crate::types::Path::Pdot(..)) || Self::path_may_follow_mty_ident(&path) {
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
        match path {
            crate::types::Path::Pdot(prefix, name, pos) => crate::types::Path::Pdot(
                std::sync::Arc::new(self.normalize_value_prefix_path_in_env(env, prefix)),
                name.clone(),
                *pos,
            ),
            crate::types::Path::Pident(_) => path.clone(),
            crate::types::Path::Papply(_, _) => path.clone(),
        }
    }

    fn translate_module_path_raw(&mut self, path: &crate::types::Path, loc: Location) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(self.env, path);
        self.translate_normal_path_raw_in_env(self.env, &normalized, loc)
    }

    fn translate_module_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: Location,
    ) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(env, path);
        self.translate_normal_path_raw_in_env(env, &normalized, loc)
    }

    fn translate_value_path_raw(&mut self, path: &crate::types::Path, loc: Location) -> RawLambda {
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
        loc: Location,
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
        loc: Location,
    ) -> RawLambda {
        self.translate_value_path_raw(path, loc)
    }

    fn note_possible_required_modules_from_module_expr(
        &mut self,
        module_expr: &ModuleExpr,
        dynamic_import: bool,
    ) {
        fn note_from_path(
            this: &mut RawLambdaConverter<'_>,
            env: &crate::types::env::Env,
            path: &crate::types::Path,
            dynamic_import: bool,
        ) {
            let normalized = this.normalize_module_path_in_env(env, path);
            if let Some(alias_target) = crate::types::typecore::alias_target_for_module_path(
                &normalized,
                env,
                &mut this.persistent_env,
                this.type_ctx,
            ) {
                if !alias_target.same(&normalized) {
                    note_from_path(this, env, &alias_target, dynamic_import);
                }
            }
            if let Ok(md) = env.lookup_module(&normalized) {
                if let Some(md_path) = md.md_path.as_ref() {
                    if !md_path.same(&normalized) {
                        note_from_path(this, env, md_path, dynamic_import);
                    }
                }
            }

            match normalized {
                crate::types::Path::Pident(id) => {
                    if id.is_global() || id.is_persistent() {
                        this.note_possible_required_module(&id, dynamic_import);
                    }
                }
                crate::types::Path::Pdot(prefix, _, _) => {
                    note_from_path(this, env, prefix.as_ref(), dynamic_import);
                }
                crate::types::Path::Papply(left, right) => {
                    note_from_path(this, env, left.as_ref(), dynamic_import);
                    note_from_path(this, env, right.as_ref(), dynamic_import);
                }
            }
        }

        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => {
                self.note_possible_required_modules_from_module_expr(inner, dynamic_import);
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                if let Some(env) = self.env_for_module_expr(module_expr) {
                    note_from_path(self, env.as_ref(), path, dynamic_import);
                } else {
                    note_from_path(self, self.env, path, dynamic_import);
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
            ModuleExprDesc::Tmod_ident(crate::types::Path::Pident(id), _) => {
                if let Some(env) = self.env_for_module_expr(module_expr) {
                    if env
                        .lookup_module(&crate::types::Path::Pident(id.clone()))
                        .is_err()
                    {
                        self.note_possible_required_module(id, false);
                        return;
                    }
                } else if self
                    .env
                    .lookup_module(&crate::types::Path::Pident(id.clone()))
                    .is_err()
                {
                    self.note_possible_required_module(id, false);
                    return;
                }
                self.note_possible_required_modules_from_module_expr(module_expr, false);
            }
            _ => self.note_possible_required_modules_from_module_expr(module_expr, false),
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
                            id.clone(),
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
        loc: Location,
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
                let value = self.apply_coercion_raw(loc.clone(), LetKind::Alias, coercion, field);
                lam = RawLambda::let_(LetKind::Alias, rebound.clone(), value, lam);
                subst.insert(id.clone(), rebound);
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
        loc: Location,
        strict: LetKind,
        funct: RawLambda,
        param: Ident,
        arg: RawLambda,
        cc_res: &ModuleCoercion,
    ) -> RawLambda {
        self.name_lambda_raw(strict, funct, |this, id| {
            let body = this.apply_coercion_raw(
                loc.clone(),
                LetKind::Strict,
                cc_res,
                RawLambda::Lapply(crate::raw_lambda::RawApply {
                    ap_func: Box::new(RawLambda::var(id)),
                    ap_args: vec![arg],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
            );
            RawLambda::function_(
                1,
                vec![param],
                body,
                FunctionAttribute {
                    is_a_functor: true,
                    ..FunctionAttribute::default()
                },
            )
        })
    }

    fn apply_coercion_raw(
        &mut self,
        loc: Location,
        strict: LetKind,
        coercion: &ModuleCoercion,
        arg: RawLambda,
    ) -> RawLambda {
        self.apply_coercion_raw_with_dynamic_import(loc, strict, coercion, arg, false)
    }

    fn apply_coercion_raw_with_dynamic_import(
        &mut self,
        loc: Location,
        strict: LetKind,
        coercion: &ModuleCoercion,
        arg: RawLambda,
        dynamic_import_scope: bool,
    ) -> RawLambda {
        self.note_possible_required_modules_in_raw_lambda_with_dynamic_import(
            &arg,
            dynamic_import_scope,
        );
        match coercion {
            ModuleCoercion::Tcoerce_none => arg,
            ModuleCoercion::Tcoerce_structure(positions, id_pos_list, runtime_fields) => {
                debug_assert_eq!(positions.len(), runtime_fields.len());
                self.name_lambda_raw(strict, arg, |this, id| {
                    let named = RawLambda::var(id.clone());
                    let lam = RawLambda::prim(
                        Primitive::Pmakeblock(
                            0,
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
                                    loc.clone(),
                                );
                                this.apply_coercion_raw(loc.clone(), LetKind::Alias, cc, field)
                            })
                            .collect(),
                        loc.clone(),
                    );
                    this.wrap_id_pos_list_raw(
                        loc.clone(),
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
                                loc.clone(),
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
                let carg = self.apply_coercion_raw(
                    loc.clone(),
                    LetKind::Alias,
                    cc_arg,
                    RawLambda::var(param.clone()),
                );
                self.apply_coercion_result_raw(loc, strict, arg, param, carg, cc_res)
            }
            ModuleCoercion::Tcoerce_primitive(pc) => {
                self.transl_primitive_raw(&pc.pc_desc, pc.pc_type, pc.pc_loc)
            }
            ModuleCoercion::Tcoerce_alias(env_ref, path, inner) => {
                self.name_lambda_raw(strict, arg, |this, _| {
                    let translated = if let Some(env) = this.type_ctx.get_typed_env(*env_ref) {
                        this.translate_normal_path_raw_in_env(env.as_ref(), path, loc.clone())
                    } else {
                        let env = this.env;
                        this.translate_normal_path_raw_in_env(env, path, loc.clone())
                    };
                    this.apply_coercion_raw(loc.clone(), LetKind::Alias, inner, translated)
                })
            }
        }
    }

    fn make_module_block_raw(
        &mut self,
        fields: &[Ident],
        is_top_level: bool,
        cc: &ModuleCoercion,
        loc: Location,
    ) -> RawLambda {
        match cc {
            ModuleCoercion::Tcoerce_none => {
                // Deduplicate fields by name, keeping only the LAST occurrence.
                // This matches OCaml's simplify_signature behavior: when a structure
                // has duplicate value names (e.g., from %%private with shadowing),
                // OCaml wraps in Tmod_constraint with Tcoerce_structure that selects
                // only the final binding. Since Rust doesn't compute that coercion,
                // we achieve the same result by deduplicating here.
                let deduped_fields = {
                    let mut seen = AHashSet::with_capacity(fields.len());
                    let mut indices = Vec::new();
                    // Walk from the end to find which indices to keep
                    for i in (0..fields.len()).rev() {
                        if seen.insert(fields[i].name()) {
                            indices.push(i);
                        }
                    }
                    indices.reverse();
                    indices
                        .iter()
                        .map(|&i| fields[i].clone())
                        .collect::<Vec<_>>()
                };
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
                    Primitive::Pmakeblock(0, tag, Mutable::Immutable),
                    block_fields,
                    loc,
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
                                export_ids.push(pc.pc_id.clone());
                            }
                            block_fields.push(self.transl_primitive_raw(
                                &pc.pc_desc,
                                pc.pc_type,
                                pc.pc_loc.clone(),
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
                                    export_ids.push(id.clone());
                                }
                                block_fields.push(self.apply_coercion_raw(
                                    loc.clone(),
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
                    Primitive::Pmakeblock(0, tag, Mutable::Immutable),
                    block_fields,
                    loc.clone(),
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
                    .map(|id| {
                        self.apply_coercion_raw(loc.clone(), LetKind::Alias, cc, RawLambda::var(id))
                    })
                    .collect();
                let tag = if is_top_level {
                    TagInfo::ModuleExport(fields.to_vec())
                } else {
                    TagInfo::Module(fields.iter().map(|id| id.name().to_string()).collect())
                };
                RawLambda::prim(
                    Primitive::Pmakeblock(0, tag, Mutable::Immutable),
                    block_fields,
                    loc,
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
                self.loc(module_expr.mod_loc),
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
                    self.loc(module_expr.mod_loc),
                )
            }
            ModuleExprDesc::Tmod_constraint(inner, _, _, inner_cc) => {
                let composed = Self::compose_coercions_raw(cc, inner_cc);
                self.convert_module_expr_raw_with_coercion(inner, rootpath, &composed)
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                let loc = self.loc(module_expr.mod_loc);
                let arg = if let Some(env) = self.env_for_module_expr(module_expr) {
                    self.translate_module_path_raw_in_env(env.as_ref(), path, loc.clone())
                } else {
                    self.translate_module_path_raw(path, loc.clone())
                };
                self.apply_coercion_raw(loc, LetKind::Strict, cc, arg)
            }
            ModuleExprDesc::Tmod_unpack(expr, _) => {
                let loc = self.loc(module_expr.mod_loc);
                let arg = self.convert_expr_raw(expr);
                self.apply_coercion_raw(loc, LetKind::Strict, cc, arg)
            }
            ModuleExprDesc::Tmod_functor(param, _, _, body) => {
                let loc = self.loc(module_expr.mod_loc);
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
                let renamed_param = param.rename(&self.id_gen);
                let arg = self.apply_coercion_raw(
                    loc.clone(),
                    LetKind::Alias,
                    arg_coercion,
                    RawLambda::var(renamed_param.clone()),
                );
                let body = RawLambda::let_(
                    LetKind::Alias,
                    param.clone(),
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
                )
            }
            ModuleExprDesc::Tmod_apply(funct, arg, ccarg) => {
                let loc = self.loc(module_expr.mod_loc);
                let inlined = self.get_inlined_attribute_from(&funct.mod_attributes);
                let funct_lam = self.with_inlined_attribute_check_suppressed(|this| {
                    this.convert_module_expr_raw_with_coercion(
                        funct,
                        &None,
                        &ModuleCoercion::Tcoerce_none,
                    )
                });
                let apply = RawLambda::Lapply(crate::raw_lambda::RawApply {
                    ap_func: Box::new(funct_lam),
                    ap_args: vec![self.convert_module_expr_raw_with_coercion(arg, &None, ccarg)],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                });
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
        self.convert_module_expr_for_pack_raw_with_dynamic_import(module_expr, false)
    }

    fn convert_module_expr_for_pack_raw_with_dynamic_import(
        &mut self,
        module_expr: &ModuleExpr,
        dynamic_import: bool,
    ) -> RawLambda {
        self.convert_module_expr_for_pack_inner(
            module_expr,
            &ModuleCoercion::Tcoerce_none,
            dynamic_import,
        )
    }

    fn convert_module_expr_for_pack_inner(
        &mut self,
        module_expr: &ModuleExpr,
        cc: &ModuleCoercion,
        dynamic_import: bool,
    ) -> RawLambda {
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
                    self.note_possible_required_modules_from_module_expr(inner, dynamic_import);
                    return self.apply_coercion_raw(
                        self.loc(inner.mod_loc),
                        LetKind::Alias,
                        &composed,
                        RawLambda::const_(Constant::ModuleAlias),
                    );
                }
                self.convert_module_expr_for_pack_inner(inner, &composed, dynamic_import)
            }
            ModuleExprDesc::Tmod_ident(path, _) => {
                // Check if this ident is an alias with Tcoerce_alias coercion.
                if matches!(cc, ModuleCoercion::Tcoerce_alias(..))
                    && matches!(
                        module_expr.mod_type,
                        crate::types::decl::ModuleType::MtyAlias(_, _)
                    )
                {
                    self.note_possible_required_modules_from_module_expr(
                        module_expr,
                        dynamic_import,
                    );
                    return self.apply_coercion_raw_with_dynamic_import(
                        self.loc(module_expr.mod_loc),
                        LetKind::Alias,
                        cc,
                        RawLambda::const_(Constant::ModuleAlias),
                        dynamic_import,
                    );
                }
                let loc = self.loc(module_expr.mod_loc);
                let arg = if let Some(env) = self.env_for_module_expr(module_expr) {
                    self.translate_module_path_raw_in_env(env.as_ref(), path, loc.clone())
                } else {
                    self.translate_module_path_raw(path, loc.clone())
                };
                self.apply_coercion_raw_with_dynamic_import(
                    loc,
                    LetKind::Strict,
                    cc,
                    arg,
                    dynamic_import,
                )
            }
            // For other module expression kinds, fall back to the normal conversion
            _ => self.convert_module_expr_raw_with_coercion(module_expr, &None, cc),
        }
    }

    fn convert_expr_raw_with_dynamic_import(
        &mut self,
        expr: &Expression,
        dynamic_import: bool,
    ) -> RawLambda {
        match &expr.exp_desc {
            ExpressionDesc::Texp_pack(modl) if dynamic_import => {
                self.convert_module_expr_for_pack_raw_with_dynamic_import(modl, true)
            }
            _ => self.convert_expr_raw(expr),
        }
    }

    // ---- Recursive module compilation (Transl_recmodule) ----

    /// Create the location constant for `#init_mod`.
    /// Produces `Const_block(Blk_tuple, [filename, line, char])`.
    fn undefined_location(&self, loc_idx: LocIdx) -> RawLambda {
        let loc = self.loc(loc_idx);
        let fname = self.basename_for_loc(loc);
        RawLambda::Lconst(Constant::Block {
            tag: 0,
            tag_info: TagInfo::Tuple,
            elements: vec![
                Constant::string_with_delim(fname, StringDelim::Plain),
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
        // First try converting the typedtree mod_type directly.
        // If that fails (e.g., Tmty_placeholder), try extracting from
        // Tmod_constraint wrapper or looking up in the env.
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
                    structure.str_type.clone(),
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
                    tag: 1, // value tag
                    tag_info: TagInfo::Constructor {
                        name: "value".to_string(),
                        num_nonconst: 2,
                        tag: 1,
                        attrs: vec![],
                    },
                    elements: vec![Constant::ModuleAlias],
                })
            }
            ModuleType::MtySignature(sg) => {
                let struct_shape = self.init_shape_struct(env, sg)?;
                Some(Constant::Block {
                    tag: 0, // Module tag
                    tag_info: TagInfo::Constructor {
                        name: "Module".to_string(),
                        num_nonconst: 2,
                        tag: 0,
                        attrs: vec![],
                    },
                    elements: vec![Constant::Block {
                        tag: 0,
                        tag_info: TagInfo::Tuple,
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
                                &*self.type_ctx.get_desc(expanded),
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
                                tag: 0,
                                tag_info: TagInfo::Tuple,
                                elements: vec![
                                    init_v,
                                    Constant::string_with_delim(id.name(), StringDelim::Plain),
                                ],
                            });
                        }
                    }
                }
                DeclSigItem::SigType(id, tdecl, _) => {
                    env.add_type(id.clone(), tdecl.clone());
                }
                DeclSigItem::SigTypext(_, _, _) => {
                    return None; // type extensions can't be initialized
                }
                DeclSigItem::SigModule(id, md, _) => {
                    let sub_shape = self.init_shape_mod(&env, &md.md_type)?;
                    // add_name: wrap with (shape, name) tuple
                    result.push(Constant::Block {
                        tag: 0,
                        tag_info: TagInfo::Tuple,
                        elements: vec![
                            sub_shape,
                            Constant::string_with_delim(id.name(), StringDelim::Plain),
                        ],
                    });
                    env.add_module(id.clone(), md.clone());
                }
                DeclSigItem::SigModtype(id, minfo) => {
                    env.add_modtype(id.clone(), minfo.clone());
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
            RawLambda::Lprim(info) if matches!(info.primitive, Primitive::Pmakeblock(_, _, _)) => {
                info.args.iter().all(|arg| match arg {
                    RawLambda::Lvar(id) => acc.contains(id),
                    RawLambda::Lfunction(_) | RawLambda::Lconst(_) => true,
                    _ => false,
                })
            }
            RawLambda::Llet(_, id, value, cont) => {
                if matches!(value.as_ref(), RawLambda::Lfunction(_)) {
                    let mut new_acc = acc.clone();
                    new_acc.insert(id.clone());
                    Self::is_function_or_const_block(cont, &new_acc)
                } else if matches!(value.as_ref(), RawLambda::Lconst(_)) {
                    Self::is_function_or_const_block(cont, acc)
                } else if let RawLambda::Lvar(id2) = value.as_ref() {
                    if acc.contains(id2) {
                        let mut new_acc = acc.clone();
                        new_acc.insert(id.clone());
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
                    new_acc.insert(id.clone());
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
        let locs: Vec<Location> = bindings.iter().map(|binding| binding.loc.clone()).collect();

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
                Status::Defined => return,
                Status::Inprogress => {
                    if diagnostic.is_none() {
                        *diagnostic = Some((
                            locs[i].clone(),
                            format!(
                                "Cannot safely evaluate the definition of the recursively-defined module {}",
                                ids[i].name()
                            ),
                        ));
                    }
                    return;
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
            return RawLambda::Lletrec(rec_bindings, Box::new(cont));
        }

        // Phase 3: patch_forwards - update_mod for each shaped binding
        let mut result = cont;
        for binding in bindings.iter().rev() {
            if let Some((_loc, shape)) = &binding.init {
                result = RawLambda::seq(
                    RawLambda::prim(
                        Primitive::PupdateMod,
                        vec![
                            shape.clone(),
                            RawLambda::Lvar(binding.id.clone()),
                            binding.rhs.clone(),
                        ],
                        Location::none(),
                    ),
                    result,
                );
            }
        }

        // Phase 2: bind_strict - let bindings for modules without shapes
        for binding in bindings.iter().rev() {
            if binding.init.is_none() {
                result = RawLambda::let_(
                    LetKind::Strict,
                    binding.id.clone(),
                    binding.rhs.clone(),
                    result,
                );
            }
        }

        // Phase 1: bind_inits - init_mod for modules with shapes
        for binding in bindings.iter().rev() {
            if let Some((loc, shape)) = &binding.init {
                result = RawLambda::let_(
                    LetKind::Strict,
                    binding.id.clone(),
                    RawLambda::prim(
                        Primitive::PinitMod,
                        vec![loc.clone(), shape.clone()],
                        Location::none(),
                    ),
                    result,
                );
            }
        }

        result
    }

    /// Compile recursive module bindings.
    /// Mirrors OCaml's `Transl_recmodule.compile_recmodule`.
    fn compile_recmodule(
        &mut self,
        bindings: &[crate::types::typedtree::ModuleBinding],
        cont: RawLambda,
    ) -> RawLambda {
        // Collect (id, init_shape, rhs) for each binding
        let collected: Vec<RecModuleBinding> = bindings
            .iter()
            .map(|mb| {
                let id = mb.mb_id.clone();
                let loc = self.loc(mb.mb_expr.mod_loc);
                let shape = self.init_shape(&mb.mb_expr);
                let rhs = self.convert_module_expr_raw(&mb.mb_expr, &None);
                RecModuleBinding {
                    id,
                    loc,
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
        loc: Location,
    ) -> RawLambda {
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
                            _ if !Self::is_irrefutable_pattern(&binding.vb_pat) => {
                                self.report_diagnostic(
                                    self.loc(binding.vb_pat.pat_loc),
                                    "Such fragile pattern not allowed in the toplevel".to_string(),
                                );
                            }
                            _ => {}
                        }
                    }
                }
                self.convert_let_with_body_raw(*rec_flag, bindings, body)
            }
            StructureItemDesc::Tstr_module(binding) => {
                let old_len = fields.len();
                // OCaml always skips @internal.local modules from the field list,
                // regardless of coercion type. Hidden modules don't get position
                // indices in the runtime field layout.
                let is_hidden = self.rescript_hide_attributes(&binding.mb_attributes);
                if !is_hidden {
                    fields.push(binding.mb_id.clone());
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
                let result = RawLambda::let_(
                    Self::pure_module(&binding.mb_expr),
                    binding.mb_id.clone(),
                    module_body,
                    body,
                );
                result
            }
            StructureItemDesc::Tstr_typext(tyext) => {
                let old_len = fields.len();
                fields.extend(
                    tyext
                        .tyext_constructors
                        .iter()
                        .map(|ext| ext.ext_id.clone()),
                );
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                self.transl_type_extension_raw(rootpath, tyext, body)
            }
            StructureItemDesc::Tstr_exception(ext) => {
                let old_len = fields.len();
                fields.push(ext.ext_id.clone());
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                RawLambda::let_(
                    LetKind::Strict,
                    ext.ext_id.clone(),
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
                fields.extend(ids.iter().map(|(id, _)| id.clone()));
                let mid = self.fresh_ident("include");
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                let body =
                    self.rebind_included_idents_raw(&mid, &ids, body, self.loc(incl.incl_loc));
                let result = RawLambda::let_(
                    Self::pure_module(&incl.incl_mod),
                    mid,
                    self.convert_module_expr_raw(&incl.incl_mod, &None),
                    body,
                );
                result
            }
            StructureItemDesc::Tstr_recmodule(bindings) => {
                // OCaml: add all recursive module idents to fields, then generate letrec
                let old_len = fields.len();
                for mb in bindings.iter() {
                    fields.push(mb.mb_id.clone());
                }
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);

                self.compile_recmodule(bindings, body)
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

    fn translate_module_path(&self, path: &crate::types::Path, loc: Location) -> Lambda {
        match path {
            crate::types::Path::Pident(id) => {
                if id.is_global() {
                    Lambda::global_module(id.clone(), false)
                } else {
                    Lambda::var(id.clone())
                }
            }
            crate::types::Path::Pdot(prefix, name, _) => {
                let prefix_lam = self.translate_module_path(prefix, loc.clone());
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Module { name: name.clone() }),
                    vec![prefix_lam],
                    loc,
                )
            }
            crate::types::Path::Papply(_, _) => Lambda::unit(),
        }
    }

    fn convert_module_expr(&mut self, module_expr: &ModuleExpr) -> Lambda {
        match &module_expr.mod_desc {
            ModuleExprDesc::Tmod_structure(structure) => {
                let mut fields = Vec::new();
                self.convert_structure_items(&mut fields, &structure.str_items, false)
            }
            ModuleExprDesc::Tmod_constraint(inner, _, _, _) => self.convert_module_expr(inner),
            ModuleExprDesc::Tmod_ident(path, _) => {
                self.translate_module_path(path, self.loc(module_expr.mod_loc))
            }
            ModuleExprDesc::Tmod_unpack(expr, _) => self.convert_expr(expr),
            ModuleExprDesc::Tmod_apply(_, _, _) | ModuleExprDesc::Tmod_functor(_, _, _, _) => {
                Lambda::unit()
            }
        }
    }

    fn convert_structure_items(
        &mut self,
        fields: &mut Vec<Ident>,
        items: &[StructureItem],
        is_top_level: bool,
    ) -> Lambda {
        let Some((item, rem)) = items.split_first() else {
            let block_fields = fields.iter().cloned().map(Lambda::var).collect();
            let tag = if is_top_level {
                TagInfo::ModuleExport(fields.clone())
            } else {
                TagInfo::Module(fields.iter().map(|id| id.name().to_string()).collect())
            };
            return Lambda::prim(
                Primitive::Pmakeblock(0, tag, Mutable::Immutable),
                block_fields,
                Location::none(),
            );
        };

        match &item.str_desc {
            StructureItemDesc::Tstr_eval(expr, _) => Lambda::seq(
                self.convert_expr(expr),
                self.convert_structure_items(fields, rem, is_top_level),
            ),
            StructureItemDesc::Tstr_value(rec_flag, bindings) => {
                let old_len = fields.len();
                fields.extend(let_bound_idents(bindings));
                let body = self.convert_structure_items(fields, rem, is_top_level);
                fields.truncate(old_len);
                self.convert_let_with_body(*rec_flag, bindings, body)
            }
            StructureItemDesc::Tstr_module(binding) => {
                let old_len = fields.len();
                if !self.rescript_hide_attributes(&binding.mb_attributes) {
                    fields.push(binding.mb_id.clone());
                }
                let body = self.convert_structure_items(fields, rem, is_top_level);
                fields.truncate(old_len);
                let module_body = self.convert_module_expr(&binding.mb_expr);
                Lambda::let_(
                    Self::pure_module(&binding.mb_expr),
                    binding.mb_id.clone(),
                    module_body,
                    body,
                )
            }
            StructureItemDesc::Tstr_primitive(_)
            | StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_typext(_)
            | StructureItemDesc::Tstr_exception(_)
            | StructureItemDesc::Tstr_recmodule(_)
            | StructureItemDesc::Tstr_modtype(_)
            | StructureItemDesc::Tstr_open(_)
            | StructureItemDesc::Tstr_include(_)
            | StructureItemDesc::Tstr_attribute(_) => {
                self.convert_structure_items(fields, rem, is_top_level)
            }
        }
    }

    fn convert_expr_raw(&mut self, expr: &Expression) -> RawLambda {
        self.check_expr_attribute(expr);
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => {
                    if let Some(env) = self.env_for_expr(expr) {
                        self.translate_primitive_raw_in_env(
                            self.loc(expr.exp_loc),
                            prim,
                            expr.exp_type,
                            env.as_ref(),
                        )
                    } else {
                        self.translate_primitive_raw(self.loc(expr.exp_loc), prim, expr.exp_type)
                    }
                }
                ValueKind::ValReg => {
                    if let Some(env) = self.env_for_expr(expr) {
                        self.translate_value_path_raw_in_env(
                            env.as_ref(),
                            path,
                            self.loc(expr.exp_loc),
                        )
                    } else {
                        self.translate_value_path_raw(path, self.loc(expr.exp_loc))
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
                partial,
                arity,
                async_,
            } => {
                let directive =
                    Self::get_directive_attribute_from(&expr.exp_attributes, self.arena);
                let inline = self.get_inline_attribute_from(&expr.exp_attributes);
                if body.len() == 1 {
                    if let Some(lambda) = self.convert_single_case_function_raw_borrowed(
                        params,
                        &body[0],
                        *partial,
                        *arity,
                        expr.exp_type,
                        *async_,
                        directive.clone(),
                        inline,
                        self.loc(expr.exp_loc),
                    ) {
                        return lambda;
                    }
                }
                let pushed_body = body
                    .iter()
                    .map(|case| self.push_defaults_case(Vec::new(), case))
                    .collect::<Vec<_>>();
                self.convert_function_raw(
                    params,
                    &pushed_body,
                    *partial,
                    *arity,
                    expr.exp_type,
                    *async_,
                    directive,
                    inline,
                    self.loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => self.convert_apply_raw(
                expr.exp_loc,
                self.loc(expr.exp_loc),
                funct,
                args,
                *partial,
                *transformed_jsx,
            ),
            ExpressionDesc::Texp_match(scrut, cases, exn_cases, partial) => {
                if !exn_cases.is_empty() {
                    // Match with exception cases: wrap in try-with + static catch.
                    // Matches OCaml's transl_match logic from translcore.ml.
                    let loc = self.loc(expr.exp_loc);
                    let partial = *partial;
                    self.compile_match_with_exceptions_raw(
                        loc, scrut, cases, exn_cases, partial, expr,
                    )
                } else {
                    // For single-case matches with unboxed constructor patterns,
                    // use the irrefutable path which correctly handles transparent field access.
                    if cases.len() == 1 && cases[0].c_guard.is_none() {
                        if let PatternDesc::Tpat_construct(_, cstr, _) = &cases[0].c_lhs.pat_desc {
                            if matches!(cstr.cstr_tag, ConstructorTag::CstrUnboxed) {
                                if let Some(result) =
                                    self.compile_irrefutable_match_raw(scrut, cases)
                                {
                                    return result;
                                }
                            }
                        }
                    }
                    let partial = *partial;
                    let loc = self.loc(expr.exp_loc);
                    // Use full matching compiler (ported from OCaml's matching.ml)
                    self.compile_full_matching(loc, scrut, cases, partial, expr)
                }
            }
            ExpressionDesc::Texp_try(body, cases) => {
                let loc = self.loc(expr.exp_loc);
                let exn_id = self.name_pattern_ident("exn", cases);
                let handler = self.compile_trywith_handler_raw(&exn_id, cases);
                let body_lam = self.convert_expr_raw(body);
                RawLambda::LtryWith(Box::new(body_lam), exn_id, Box::new(handler))
            }
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items
                    .iter()
                    .map(|item| self.convert_expr_raw(item))
                    .collect::<Vec<_>>();
                self.raw_block_or_prim(0, TagInfo::Tuple, elems, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => {
                self.convert_construct_raw(self.loc(expr.exp_loc), expr.exp_env, cstr, args)
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
                        self.loc(expr.exp_loc),
                    )
                }
            },
            ExpressionDesc::Texp_ifthenelse(cond, then_, else_) => {
                let else_lam = else_
                    .as_ref()
                    .map(|e| self.convert_expr_raw(e))
                    .unwrap_or_else(RawLambda::unit);
                RawLambda::LifThenElse(
                    Box::new(self.convert_expr_raw(cond)),
                    Box::new(self.convert_expr_raw(then_)),
                    Box::new(else_lam),
                )
            }
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
            } => self.convert_record_raw(
                self.loc(expr.exp_loc),
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
                    self.loc(expr.exp_loc),
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
                        self.loc(expr.exp_loc),
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
                        self.loc(expr.exp_loc),
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
                RawLambda::prim(Primitive::Pmakearray, elems, self.loc(expr.exp_loc))
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
                    var.clone(),
                    Box::new(self.convert_expr_raw(start)),
                    Box::new(self.convert_expr_raw(end)),
                    dir,
                    Box::new(self.convert_expr_raw(body)),
                )
            }
            // Upstream #7887: typed for-of / for-await-of -> raw lambda.
            ExpressionDesc::Texp_for_of(var, _pat, iterable, body) => RawLambda::Lfor_of(
                var.clone(),
                Box::new(self.convert_expr_raw(iterable)),
                Box::new(self.convert_expr_raw(body)),
            ),
            ExpressionDesc::Texp_for_await_of(var, _pat, iterable, body) => {
                RawLambda::Lfor_await_of(
                    var.clone(),
                    Box::new(self.convert_expr_raw(iterable)),
                    Box::new(self.convert_expr_raw(body)),
                )
            }
            ExpressionDesc::Texp_send(obj_expr, MethKind::Tmeth_name(name), _) => RawLambda::Lsend(
                name.clone(),
                Box::new(self.convert_expr_raw(obj_expr)),
                self.loc(expr.exp_loc),
            ),
            ExpressionDesc::Texp_send(_, MethKind::Tmeth_val(_), _) => RawLambda::unit(),
            ExpressionDesc::Texp_letmodule(id, _, modl, body) => RawLambda::let_(
                LetKind::Strict,
                id.clone(),
                self.convert_module_expr_raw(modl, &None),
                self.convert_expr_raw(body),
            ),
            ExpressionDesc::Texp_letexception(ext, body) => RawLambda::let_(
                LetKind::Strict,
                ext.ext_id.clone(),
                self.transl_extension_constructor_raw(None, ext),
                self.convert_expr_raw(body),
            ),
            ExpressionDesc::Texp_extension_constructor(_, path) => {
                self.translate_extension_path_raw(path, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_pack(modl) => self.convert_module_expr_for_pack_raw(modl),
            ExpressionDesc::Texp_assert(inner_expr) => {
                if matches!(
                    inner_expr.exp_desc,
                    ExpressionDesc::Texp_construct(_, ref cstr, ref args)
                        if cstr.cstr_name == "false" && args.is_empty()
                ) {
                    self.raw_assert_false(self.loc(expr.exp_loc))
                } else if self.noassert {
                    // OCaml translcore.ml:926-931 handles `assert false`
                    // first, then lowers ordinary assertions to unit under
                    // Clflags.noassert.
                    RawLambda::unit()
                } else {
                    let failure = self.raw_assert_failed(self.loc(expr.exp_loc));
                    RawLambda::LifThenElse(
                        Box::new(self.convert_expr_raw(inner_expr)),
                        Box::new(RawLambda::unit()),
                        Box::new(failure),
                    )
                }
            }
        }
    }

    fn convert_expr(&mut self, expr: &Expression) -> Lambda {
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => self.translate_primitive(self.loc(expr.exp_loc), prim),
                ValueKind::ValReg => self.translate_value_path(expr.exp_loc, path),
            },
            ExpressionDesc::Texp_constant(cst) => Lambda::const_(self.convert_constant(cst)),
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
            ExpressionDesc::Texp_match(scrut, cases, exn_cases, partial)
                if exn_cases.is_empty() =>
            {
                self.compile_irrefutable_match(scrut, cases)
                    .or_else(|| {
                        self.compile_simple_tuple_match(
                            self.loc(expr.exp_loc),
                            scrut,
                            cases,
                            *partial,
                        )
                    })
                    .or_else(|| {
                        self.compile_simple_constructor_match(
                            self.loc(expr.exp_loc),
                            scrut,
                            cases,
                            *partial,
                        )
                    })
                    .unwrap_or_else(|| {
                        trace_raw_match_fallback(&self.loc(expr.exp_loc), scrut, cases);
                        let raw = self.compile_full_matching(
                            self.loc(expr.exp_loc),
                            scrut,
                            cases,
                            *partial,
                            expr,
                        );
                        let start_stamp = self.current_stamp();
                        crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(raw, start_stamp)
                    })
            }
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items.iter().map(|e| self.convert_expr(e)).collect();
                Lambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                    elems,
                    self.loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(_) | ConstructorTag::CstrUnboxed => {
                    self.convert_construct(self.loc(expr.exp_loc), cstr, args)
                }
                _ => {
                    let raw = self.convert_construct_raw(
                        self.loc(expr.exp_loc),
                        expr.exp_env,
                        cstr,
                        args,
                    );
                    let start_stamp = self.current_stamp();
                    crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(raw, start_stamp)
                }
            },
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
                        name: label_runtime_name(lbl),
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
                    crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet(label_runtime_name(lbl)),
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
            // OCaml `Translcore.transl_exp0` after #8348:
            // `Texp_break -> Lbreak | Texp_continue -> Lcontinue`.
            ExpressionDesc::Texp_break => Lambda::break_(),
            ExpressionDesc::Texp_continue => Lambda::continue_(),
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
                    crate::parser::ast::DirectionFlag::Upto => crate::lambda::DirectionFlag::Upto,
                    crate::parser::ast::DirectionFlag::Downto => {
                        crate::lambda::DirectionFlag::Downto
                    }
                };
                Lambda::for_(var.clone(), start_lam, end_lam, dir, body_lam)
            }
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
            ExpressionDesc::Texp_letmodule(_, _, _, body) => self.convert_expr(body),
            ExpressionDesc::Texp_letexception(_, body) => self.convert_expr(body),
            ExpressionDesc::Texp_assert(inner_expr) => {
                if matches!(
                    inner_expr.exp_desc,
                    ExpressionDesc::Texp_construct(_, ref cstr, ref args)
                        if cstr.cstr_name == "false" && args.is_empty()
                ) {
                    self.assert_false_lambda(self.loc(expr.exp_loc))
                } else if self.noassert {
                    // Same branch order as compiler/ml/translcore.ml:926-931.
                    Lambda::unit()
                } else {
                    let cond = self.convert_expr(inner_expr);
                    let failure = self.assert_failed_lambda(self.loc(expr.exp_loc));
                    Lambda::if_(cond, Lambda::unit(), failure)
                }
            }
            _ => {
                trace_raw_fallback(Self::expr_desc_name(&expr.exp_desc));
                let raw = self.convert_expr_raw(expr);
                let start_stamp = self.current_stamp();
                crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(raw, start_stamp)
            }
        }
    }

    fn expr_desc_name(desc: &ExpressionDesc) -> &'static str {
        match desc {
            ExpressionDesc::Texp_ident(_, _, _) => "Texp_ident",
            ExpressionDesc::Texp_constant(_) => "Texp_constant",
            ExpressionDesc::Texp_let(_, _, _) => "Texp_let",
            ExpressionDesc::Texp_function { .. } => "Texp_function",
            ExpressionDesc::Texp_apply { .. } => "Texp_apply",
            ExpressionDesc::Texp_match(_, _, _, _) => "Texp_match",
            ExpressionDesc::Texp_try(_, _) => "Texp_try",
            ExpressionDesc::Texp_tuple(_) => "Texp_tuple",
            ExpressionDesc::Texp_construct(_, _, _) => "Texp_construct",
            ExpressionDesc::Texp_variant(_, _) => "Texp_variant",
            ExpressionDesc::Texp_record { .. } => "Texp_record",
            ExpressionDesc::Texp_record_sparse { .. } => "Texp_record_sparse",
            ExpressionDesc::Texp_field(_, _, _) => "Texp_field",
            ExpressionDesc::Texp_setfield(_, _, _, _) => "Texp_setfield",
            ExpressionDesc::Texp_array(_) => "Texp_array",
            ExpressionDesc::Texp_ifthenelse(_, _, _) => "Texp_ifthenelse",
            ExpressionDesc::Texp_sequence(_, _) => "Texp_sequence",
            ExpressionDesc::Texp_break => "Texp_break",
            ExpressionDesc::Texp_continue => "Texp_continue",
            ExpressionDesc::Texp_while(_, _) => "Texp_while",
            ExpressionDesc::Texp_for(_, _, _, _, _, _) => "Texp_for",
            ExpressionDesc::Texp_for_of(_, _, _, _) => "Texp_for_of",
            ExpressionDesc::Texp_for_await_of(_, _, _, _) => "Texp_for_await_of",
            ExpressionDesc::Texp_send(_, _, _) => "Texp_send",
            ExpressionDesc::Texp_letmodule(_, _, _, _) => "Texp_letmodule",
            ExpressionDesc::Texp_letexception(_, _) => "Texp_letexception",
            ExpressionDesc::Texp_assert(_) => "Texp_assert",
            ExpressionDesc::Texp_pack(_) => "Texp_pack",
            ExpressionDesc::Texp_extension_constructor(_, _) => "Texp_extension_constructor",
        }
    }

    fn pattern_desc_name(pat: &Pattern) -> &'static str {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => "Tpat_any",
            PatternDesc::Tpat_var(_, _) => "Tpat_var",
            PatternDesc::Tpat_alias(_, _, _) => "Tpat_alias",
            PatternDesc::Tpat_constant(_) => "Tpat_constant",
            PatternDesc::Tpat_tuple(_) => "Tpat_tuple",
            PatternDesc::Tpat_construct(_, _, _) => "Tpat_construct",
            PatternDesc::Tpat_variant(_, _, _) => "Tpat_variant",
            PatternDesc::Tpat_record(_, _) => "Tpat_record",
            PatternDesc::Tpat_array(_) => "Tpat_array",
            PatternDesc::Tpat_or(_, _, _) => "Tpat_or",
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
            TConstant::BigInt(positive, v) => Constant::BigInt {
                negative: !*positive,
                value: v.clone(),
            },
        }
    }

    fn match_failure(&mut self, loc: Location) -> Lambda {
        self.raise_predef_exception("Match_failure", PREDEF_MATCH_FAILURE_STAMP, loc)
    }

    fn compile_simple_constructor_match(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<Lambda> {
        #[derive(Clone)]
        enum DefaultCase {
            Any(Lambda),
            Bind(Ident, Lambda),
        }

        let mut seen_const_tags = std::collections::BTreeSet::new();
        let mut seen_block_tags = std::collections::BTreeSet::new();
        let mut default_case = None;

        for case in cases {
            if case.c_guard.is_some() {
                return None;
            }

            let (pat, _) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                    ConstructorTag::CstrConstant(tag) => {
                        if !args.is_empty() || !seen_const_tags.insert(*tag) {
                            return None;
                        }
                    }
                    ConstructorTag::CstrBlock(tag) => {
                        if !seen_block_tags.insert(*tag)
                            || !args.iter().all(Self::is_irrefutable_pattern)
                        {
                            return None;
                        }
                    }
                    ConstructorTag::CstrUnboxed | ConstructorTag::CstrExtension(_) => return None,
                },
                PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                    if !seen_const_tags.insert(*i as i32) {
                        return None;
                    }
                }
                PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                    if !seen_const_tags.insert(*c as i32) {
                        return None;
                    }
                }
                PatternDesc::Tpat_any => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Any(self.convert_expr(&case.c_rhs)));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(
                        id.clone(),
                        self.convert_expr(&case.c_rhs),
                    ));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(
                        id.clone(),
                        self.convert_expr(&case.c_rhs),
                    ));
                }
                _ => return None,
            }
        }

        if seen_const_tags.is_empty() && seen_block_tags.is_empty() {
            return None;
        }

        let scrut_lam = self.convert_expr(scrut);
        let (scrut_id, scrut_var, wrap_let) = match &scrut_lam {
            Lambda::Lvar(id) => (id.clone(), Lambda::var(id.clone()), None),
            _ => {
                let scrut_id = self.fresh_ident("match");
                (
                    scrut_id.clone(),
                    Lambda::var(scrut_id.clone()),
                    Some((scrut_id, scrut_lam)),
                )
            }
        };

        let mut const_cases = Vec::new();
        let mut block_cases = Vec::new();
        for case in cases {
            let body = self.convert_expr(&case.c_rhs);
            let (pat, aliases) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                    ConstructorTag::CstrConstant(tag) => const_cases.push((
                        *tag,
                        wrap_aliases(&aliases, Lambda::var(scrut_id.clone()), body),
                    )),
                    ConstructorTag::CstrBlock(tag) => block_cases.push((
                        *tag,
                        wrap_aliases(
                            &aliases,
                            Lambda::var(scrut_id.clone()),
                            self.bind_constructor_args_irrefutably(
                                &scrut_id, pat, cstr, args, body,
                            ),
                        ),
                    )),
                    ConstructorTag::CstrUnboxed | ConstructorTag::CstrExtension(_) => {}
                },
                PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                    const_cases.push((
                        *i as i32,
                        wrap_aliases(&aliases, Lambda::var(scrut_id.clone()), body),
                    ));
                }
                PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                    const_cases.push((
                        *c as i32,
                        wrap_aliases(&aliases, Lambda::var(scrut_id.clone()), body),
                    ));
                }
                _ => {}
            }
        }

        let failaction = match default_case {
            Some(DefaultCase::Any(body)) => Some(Box::new(body)),
            Some(DefaultCase::Bind(id, body)) => Some(Box::new(Lambda::let_(
                LetKind::Alias,
                id,
                Lambda::var(scrut_id.clone()),
                body,
            ))),
            None => match partial {
                Partial::Partial => Some(Box::new(self.match_failure(loc.clone()))),
                Partial::Total => None,
            },
        };

        let sw = Lambda::Lswitch(
            Box::new(scrut_var),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: const_cases,
                sw_blocks_full: false,
                sw_blocks: block_cases,
                sw_failaction: failaction,
                sw_names: None,
            },
        );

        Some(match wrap_let {
            Some((id, value)) => Lambda::let_(LetKind::Strict, id, value, sw),
            None => sw,
        })
    }

    fn compile_simple_string_match(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        #[derive(Clone)]
        enum DefaultCase {
            Any(RawLambda),
            Bind(Ident, RawLambda),
        }

        let mut seen = BTreeSet::new();
        let mut default_case = None;
        for case in cases {
            if case.c_guard.is_some() {
                return None;
            }

            if let Some(arms) = collect_string_pattern_arms(&case.c_lhs) {
                for (s, _) in arms {
                    if !seen.insert(s) {
                        return None;
                    }
                }
                continue;
            }

            let (pat, _) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_any => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Any(self.convert_expr_raw(&case.c_rhs)));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(
                        id.clone(),
                        self.convert_expr_raw(&case.c_rhs),
                    ));
                }
                _ => return None,
            }
        }

        if seen.is_empty() {
            return None;
        }

        let scrut_lam = self.convert_expr_raw(scrut);
        let scrut_name = self.fresh_name_from_cases("match", cases);
        let (scrut_id, scrut_var, wrap_let) = match &scrut_lam {
            RawLambda::Lvar(id) => (id.clone(), RawLambda::var(id.clone()), None),
            _ => {
                let scrut_id = self.fresh_ident(&scrut_name);
                (
                    scrut_id.clone(),
                    RawLambda::var(scrut_id.clone()),
                    Some((scrut_id, scrut_lam)),
                )
            }
        };

        let mut string_cases = Vec::new();
        for case in cases {
            let body = self.convert_expr_raw(&case.c_rhs);
            if let Some(arms) = collect_string_pattern_arms(&case.c_lhs) {
                for (s, aliases) in arms {
                    string_cases.push((
                        s,
                        wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), body.clone()),
                    ));
                }
            }
        }
        string_cases.sort_by(|(left, _), (right, _)| left.cmp(right));

        let failaction = match default_case {
            Some(DefaultCase::Any(body)) => Some(body),
            Some(DefaultCase::Bind(id, body)) => Some(RawLambda::let_(
                LetKind::Alias,
                id,
                RawLambda::var(scrut_id.clone()),
                body,
            )),
            None => match partial {
                Partial::Partial => Some(RawLambda::from_lowered(self.match_failure(loc))),
                Partial::Total => None,
            },
        };

        let mut key_counts = Vec::<(String, usize)>::new();
        for (_, act) in &string_cases {
            let key = self.raw_lambda_key(act);
            if let Some((_, count)) = key_counts.iter_mut().find(|(entry, _)| *entry == key) {
                *count += 1;
            } else {
                key_counts.push((key, 1));
            }
        }

        let mut shared_actions = Vec::<(String, RawLambda)>::new();
        if let Some(default) = &failaction {
            shared_actions.push((self.raw_lambda_key(default), default.clone()));
        }
        for (_, act) in &string_cases {
            let key = self.raw_lambda_key(act);
            let repeated = key_counts
                .iter()
                .find(|(entry, _)| *entry == key)
                .is_some_and(|(_, count)| *count > 1);
            if (repeated
                || failaction
                    .as_ref()
                    .is_some_and(|default| self.raw_lambda_key(default) == key))
                && !shared_actions.iter().any(|(entry, _)| *entry == key)
            {
                shared_actions.push((key, act.clone()));
            }
        }

        let mut shared_ids = Vec::<(String, i32)>::new();
        for (key, _) in shared_actions.iter().rev() {
            shared_ids.push((key.clone(), self.next_raise_count()));
        }

        let mut cases_with_exits = Vec::new();
        for (s, act) in string_cases {
            if let Some((_, exit_id)) = shared_ids
                .iter()
                .find(|(key, _)| *key == self.raw_lambda_key(&act))
            {
                cases_with_exits.push((s, RawLambda::LstaticRaise(*exit_id, Vec::new())));
            } else {
                cases_with_exits.push((s, act));
            }
        }

        let default = failaction.map(|act| {
            if let Some((_, exit_id)) = shared_ids
                .iter()
                .find(|(key, _)| *key == self.raw_lambda_key(&act))
            {
                Box::new(RawLambda::LstaticRaise(*exit_id, Vec::new()))
            } else {
                Box::new(act)
            }
        });

        let mut result = RawLambda::LstringSwitch(Box::new(scrut_var), cases_with_exits, default);
        for (key, handler) in shared_actions {
            let exit_id = shared_ids
                .iter()
                .find(|(entry, _)| *entry == key)
                .map(|(_, id)| *id)
                .expect("shared action exit");
            result =
                RawLambda::LstaticCatch(Box::new(result), (exit_id, Vec::new()), Box::new(handler));
        }

        Some(match wrap_let {
            Some((id, value)) => RawLambda::let_(LetKind::Strict, id, value, result),
            None => result,
        })
    }

    /// Use the full matching compiler (matching.rs) for patterns that
    /// the simple matchers can't handle. Falls back to Lambda lowering
    /// if the matching compiler panics.
    fn compile_full_matching(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
        expr: &Expression,
    ) -> RawLambda {
        // Reset raise count — the simple matchers may have consumed one
        // for the partial default, but the full matching compiler manages
        // its own raise counts.
        let pat_act_list = self.cases_to_pat_act_list(cases);

        // OCaml optimization: when the scrutinee is a tuple, decompose into
        // individual arguments and use for_multiple_match, which can flatten
        // the tuple pattern matching without allocating a tuple.
        // (See OCaml's translcore.ml lines 1259-1260)
        if !crate::debug_flags::skip_for_multiple_match()
            && let ExpressionDesc::Texp_tuple(argl) = &scrut.exp_desc
        {
            let paraml: Vec<RawLambda> = argl.iter().map(|a| self.convert_expr_raw(a)).collect();
            return self.for_multiple_match_with_synced_stamps(loc, paraml, pat_act_list, partial);
        }

        let scrut_lam = self.convert_expr_raw(scrut);

        let loc_for_handler = loc.clone();
        let fname = self.basename_for_loc(loc_for_handler.clone());
        let handler_fun = || {
            let line = loc_for_handler.loc_start.line;
            let char_pos = loc_for_handler.loc_start.column();
            let match_failure_ident =
                predef_exception_ident("Match_failure", PREDEF_MATCH_FAILURE_STAMP);
            let exn = RawLambda::LglobalModule(match_failure_ident, false);
            let payload = RawLambda::Lconst(Constant::Block {
                tag: 0,
                tag_info: TagInfo::Tuple,
                elements: vec![
                    Constant::string_with_delim(fname.clone(), StringDelim::Plain),
                    Constant::int(line),
                    Constant::int(char_pos),
                ],
            });
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Praise,
                args: vec![RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
                    args: vec![exn, payload],
                    loc: loc_for_handler.clone(),
                })],
                loc: loc_for_handler,
            })
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
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        exn_cases: &[Case],
        partial: Partial,
        expr: &Expression,
    ) -> RawLambda {
        let exn_id = self.name_pattern_ident("exn", exn_cases);
        let val_id = self.name_pattern_ident("val", cases);

        // Compile the exception handler: matching on the exception
        let exn_handler = self.compile_trywith_handler_raw(&exn_id, exn_cases);

        // Compile the normal handler: matching on the scrutinee value
        let scrut_lam = self.convert_expr_raw(scrut);

        // Compile normal cases with val_id as the scrutinee
        let normal_handler = {
            // Note: do NOT allocate a raise_count here for Partial matches.
            // compile_matching allocates its own raise_num internally.
            let pat_act_list = self.cases_to_pat_act_list(cases);
            let loc_for_handler = loc.clone();
            let fname = self.basename_for_loc(loc_for_handler.clone());
            let handler_fun = || {
                let line = loc_for_handler.loc_start.line;
                let char_pos = loc_for_handler.loc_start.column();
                let match_failure_ident =
                    predef_exception_ident("Match_failure", PREDEF_MATCH_FAILURE_STAMP);
                let exn = RawLambda::LglobalModule(match_failure_ident, false);
                let payload = RawLambda::Lconst(Constant::Block {
                    tag: 0,
                    tag_info: TagInfo::Tuple,
                    elements: vec![
                        Constant::string_with_delim(fname.clone(), StringDelim::Plain),
                        Constant::int(line),
                        Constant::int(char_pos),
                    ],
                });
                RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Praise,
                    args: vec![RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
                        args: vec![exn, payload],
                        loc: loc_for_handler.clone(),
                    })],
                    loc: loc_for_handler,
                })
            };
            self.compile_matching_with_synced_stamps(
                handler_fun,
                RawLambda::var(val_id.clone()),
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
        self.for_trywith_with_synced_stamps(RawLambda::var(exn_id.clone()), pat_act_list)
    }

    fn compile_irrefutable_match_raw(
        &mut self,
        scrut: &Expression,
        cases: &[Case],
    ) -> Option<RawLambda> {
        if cases.len() != 1 || cases[0].c_guard.is_some() {
            return None;
        }

        if !Self::is_irrefutable_pattern(&cases[0].c_lhs) {
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
                    RawLambda::Lvar(match_id.clone()),
                    body,
                );
                Some(RawLambda::let_(LetKind::Strict, match_id, scrut_lam, bound))
            }
        }
    }

    fn compile_simple_trywith_raw(
        &mut self,
        loc: Location,
        body: &Expression,
        cases: &[Case],
    ) -> Option<RawLambda> {
        let exn_id = self.name_pattern_ident("exn", cases);
        let handler = self
            .compile_simple_trywith_extension_handler_raw(loc.clone(), &exn_id, cases)
            .or_else(|| {
                self.compile_simple_constructor_match_raw_from_scrut(
                    loc.clone(),
                    RawLambda::var(exn_id.clone()),
                    cases,
                    Partial::Partial,
                )
            })?;
        Some(RawLambda::LtryWith(
            Box::new(self.convert_expr_raw(body)),
            exn_id,
            Box::new(handler),
        ))
    }

    fn bind_match_arg_pattern_raw(
        &mut self,
        pat: &Pattern,
        arg: RawLambda,
        body: RawLambda,
    ) -> RawLambda {
        match arg {
            RawLambda::Lvar(_) => self.bind_irrefutable_pattern_raw(pat, arg, body),
            _ => {
                let id = self
                    .id_of_pattern(pat)
                    .unwrap_or_else(|| self.fresh_ident("match"));
                let bound =
                    self.bind_irrefutable_pattern_raw(pat, RawLambda::var(id.clone()), body);
                RawLambda::let_(LetKind::Alias, id, arg, bound)
            }
        }
    }

    fn bind_extension_args_trywith_raw(
        &mut self,
        scrut_id: &Ident,
        args: &[Pattern],
        body: RawLambda,
        loc: Location,
    ) -> RawLambda {
        // OCaml extracts extension fields from last to first (high position first)
        // matching make_field_args order in matching.ml
        let mut result = body;
        for (idx, arg_pat) in args.iter().enumerate() {
            let field = RawLambda::prim(
                Primitive::Pfield(idx as i32 + 1, FieldDbgInfo::Extension),
                vec![RawLambda::var(scrut_id.clone())],
                loc,
            );
            result = self.bind_match_arg_pattern_raw(arg_pat, field, result);
        }
        result
    }

    fn compile_simple_trywith_extension_handler_raw(
        &mut self,
        loc: Location,
        exn_id: &Ident,
        cases: &[Case],
    ) -> Option<RawLambda> {
        #[derive(Clone)]
        enum DefaultCase {
            Any(RawLambda),
            Bind(Ident, RawLambda),
        }

        let mut extension_cases = Vec::<(crate::types::Path, RawLambda)>::new();
        let mut default_case = None;

        for case in cases {
            if case.c_guard.is_some() {
                return None;
            }

            let body = self.convert_expr_raw(&case.c_rhs);
            let (pat, aliases) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_construct(_, cstr, args) => {
                    let ConstructorTag::CstrExtension(path) = &cstr.cstr_tag else {
                        return None;
                    };
                    if !args.iter().all(Self::is_irrefutable_pattern) {
                        return None;
                    }
                    let inner = if cstr.cstr_inlined.is_some() {
                        // Inline record extension: fields accessed directly from exception
                        match args.as_slice() {
                            [arg_pat] => self.bind_irrefutable_pattern_raw(
                                arg_pat,
                                RawLambda::var(exn_id.clone()),
                                body,
                            ),
                            _ => self.bind_extension_args_trywith_raw(
                                exn_id,
                                args,
                                body,
                                self.loc(pat.pat_loc),
                            ),
                        }
                    } else {
                        self.bind_extension_args_trywith_raw(
                            exn_id,
                            args,
                            body,
                            self.loc(pat.pat_loc),
                        )
                    };
                    let act = wrap_aliases_raw(&aliases, RawLambda::var(exn_id.clone()), inner);
                    extension_cases.push((path.clone(), act));
                }
                PatternDesc::Tpat_any => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Any(body));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(id.clone(), body));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(id.clone(), body));
                }
                _ => return None,
            }
        }

        if extension_cases.is_empty() {
            return None;
        }

        let reraise = RawLambda::prim(Primitive::Praise, vec![RawLambda::var(exn_id.clone())], loc);

        // Build the default action and the catch handler for the outermost wrap.
        // When there's an explicit catch-all (Some), we use a static raise as
        // the default in the chain and catch it with the real body. When there's
        // no catch-all (None), we use static raise caught by reraise.
        let (default, catch_handler) = match default_case {
            Some(DefaultCase::Any(body)) => {
                let exit_id = self.next_raise_count();
                (
                    RawLambda::LstaticRaise(exit_id, Vec::new()),
                    Some((exit_id, body)),
                )
            }
            Some(DefaultCase::Bind(id, body)) => {
                let exit_id = self.next_raise_count();
                let real_body =
                    RawLambda::let_(LetKind::Alias, id, RawLambda::var(exn_id.clone()), body);
                (
                    RawLambda::LstaticRaise(exit_id, Vec::new()),
                    Some((exit_id, real_body)),
                )
            }
            None => {
                let exit_id = self.next_raise_count();
                (RawLambda::LstaticRaise(exit_id, Vec::new()), None)
            }
        };

        let exit_id = match &default {
            RawLambda::LstaticRaise(id, args) if args.is_empty() => Some(*id),
            _ => None,
        };

        let tests =
            self.build_simple_trywith_extension_chain_raw(loc, exn_id, extension_cases, default);

        Some(match (exit_id, catch_handler) {
            // Explicit catch-all: catch the static raise with the real body
            (Some(exit_id), Some((_, body))) => {
                RawLambda::LstaticCatch(Box::new(tests), (exit_id, Vec::new()), Box::new(body))
            }
            // No catch-all: catch with reraise
            (Some(exit_id), None) => {
                RawLambda::LstaticCatch(Box::new(tests), (exit_id, Vec::new()), Box::new(reraise))
            }
            _ => tests,
        })
    }

    fn build_simple_trywith_extension_chain_raw(
        &mut self,
        loc: Location,
        exn_id: &Ident,
        extension_cases: Vec<(crate::types::Path, RawLambda)>,
        default: RawLambda,
    ) -> RawLambda {
        let mut extension_cases = extension_cases.into_iter();
        let (last_path, last_act) = extension_cases
            .next_back()
            .expect("extension handler requires at least one case");

        let mut tests =
            self.build_simple_trywith_extension_case_raw(loc, exn_id, last_path, last_act, default);

        for (path, act) in extension_cases.rev() {
            let exit_id = self.next_raise_count();
            let body = self.build_simple_trywith_extension_case_raw(
                loc,
                exn_id,
                path,
                act,
                RawLambda::LstaticRaise(exit_id, Vec::new()),
            );
            tests = RawLambda::LstaticCatch(Box::new(body), (exit_id, Vec::new()), Box::new(tests));
        }

        tests
    }

    fn build_simple_trywith_extension_case_raw(
        &mut self,
        loc: Location,
        exn_id: &Ident,
        path: crate::types::Path,
        act: RawLambda,
        fallback: RawLambda,
    ) -> RawLambda {
        let tag_id = self.fresh_ident("tag");
        let cond = RawLambda::prim(
            Primitive::PextensionSlotEq,
            vec![
                RawLambda::var(tag_id.clone()),
                self.translate_extension_path_raw(&path, loc),
            ],
            loc,
        );
        RawLambda::let_(
            LetKind::Alias,
            tag_id,
            RawLambda::var(exn_id.clone()),
            RawLambda::LifThenElse(Box::new(cond), Box::new(act), Box::new(fallback)),
        )
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
                [arg_pat] => self.bind_irrefutable_pattern_raw(
                    arg_pat,
                    RawLambda::var(scrut_id.clone()),
                    body,
                ),
                [] => body,
                _ => RawLambda::unit(),
            };
        }

        let pat_loc = self.loc(pat.pat_loc);
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
                let payload =
                    RawLambda::prim(from_option, vec![RawLambda::var(scrut_id.clone())], pat_loc);
                // For Tpat_any, OCaml's matching.ml still creates a binding
                if matches!(arg_pat.pat_desc, PatternDesc::Tpat_any) {
                    let match_id = self.fresh_ident("match");
                    result = RawLambda::let_(LetKind::Alias, match_id, payload, result);
                } else {
                    // OCaml's matching.ml (line 2433): eliminates
                    // `let *sth* = val_from_option(x) in *sth*`
                    // for optional parameter bindings where the body
                    // is just the bound variable.
                    if let PatternDesc::Tpat_var(id, _) = &arg_pat.pat_desc {
                        if id.name() == "*sth*" {
                            if let RawLambda::Lvar(body_id) = &result {
                                if body_id.same(id) {
                                    return payload;
                                }
                            }
                        }
                    }
                    result = self.bind_irrefutable_pattern_raw(arg_pat, payload, result);
                }
                return result;
            }
        }

        for (idx, arg_pat) in args.iter().enumerate() {
            let field = match &cstr.cstr_tag {
                ConstructorTag::CstrBlock(_) => RawLambda::prim(
                    Primitive::Pfield(
                        idx as i32,
                        if cstr.cstr_name == "::" {
                            FieldDbgInfo::Cons
                        } else {
                            FieldDbgInfo::Variant
                        },
                    ),
                    vec![RawLambda::var(scrut_id.clone())],
                    pat_loc,
                ),
                ConstructorTag::CstrExtension(_) => RawLambda::prim(
                    Primitive::Pfield(idx as i32 + 1, FieldDbgInfo::Extension),
                    vec![RawLambda::var(scrut_id.clone())],
                    pat_loc,
                ),
                ConstructorTag::CstrUnboxed => RawLambda::var(scrut_id.clone()),
                ConstructorTag::CstrConstant(_) => {
                    unreachable!(
                        "constructor payload binding only applies to non-constant constructors"
                    )
                }
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

    fn compile_simple_variant_match_raw(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        let scrut_lam = self.convert_expr_raw(scrut);
        self.compile_simple_variant_match_raw_from_scrut(loc, scrut_lam, cases, partial)
    }

    fn compile_simple_variant_match_raw_from_scrut(
        &mut self,
        loc: Location,
        scrut_lam: RawLambda,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        #[derive(Clone)]
        enum DefaultCase {
            Any(RawLambda),
            Bind(Ident, RawLambda),
        }

        let mut seen_tags = std::collections::BTreeSet::new();
        let mut const_cases = Vec::<(String, RawLambda)>::new();
        let mut default_case = None;
        let mut variant_pat_type = None;

        for case in cases {
            if case.c_guard.is_some() {
                return None;
            }

            let body = self.convert_expr_raw(&case.c_rhs);
            let (pat, aliases) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_variant(label, None, _) => {
                    let tag = crate::types::btype::hash_variant(label);
                    if !seen_tags.insert(tag) {
                        return None;
                    }
                    if variant_pat_type.is_none() {
                        variant_pat_type = Some(pat.pat_type);
                    }
                    const_cases.push((
                        label.to_string(),
                        wrap_aliases_raw(&aliases, raw_polyvariant_const(label), body),
                    ));
                }
                PatternDesc::Tpat_any => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Any(body));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(id.clone(), body));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(id.clone(), body));
                }
                _ => return None,
            }
        }

        if const_cases.is_empty() {
            return None;
        }

        let row_complete = variant_pat_type.is_some_and(|pat_type| {
            let expanded = crate::types::ctype::expand_head(self.type_ctx, self.env, pat_type);
            let repr = self.type_ctx.repr(expanded);
            let desc = self.type_ctx.get_desc(repr);
            let row_complete = match &*desc {
                TypeDesc::Tvariant(row) => {
                    let row = crate::types::btype::row_repr(self.type_ctx, row);
                    row.row_closed
                        && row
                            .row_fields
                            .iter()
                            .filter(|(_, field)| {
                                !matches!(
                                    crate::types::btype::row_field_repr(self.type_ctx, field),
                                    crate::types::type_expr::RowField::Rabsent
                                )
                            })
                            .count()
                            == const_cases.len()
                }
                _ => false,
            };
            drop(desc);
            row_complete
        });

        let failaction = match default_case {
            Some(DefaultCase::Any(body)) => Some(body),
            Some(DefaultCase::Bind(id, body)) => {
                Some(RawLambda::let_(LetKind::Alias, id, scrut_lam.clone(), body))
            }
            None if row_complete || matches!(partial, Partial::Total) => None,
            None => Some(RawLambda::from_lowered(self.match_failure(loc))),
        };

        let result = if failaction.is_none() && const_cases.len() == 1 {
            const_cases.into_iter().next()?.1
        } else {
            let cases_to_test = if let Some(default) = failaction {
                (const_cases, default)
            } else {
                let mut iter = const_cases.into_iter();
                let (_, first_body) = iter.next()?;
                (iter.collect(), first_body)
            };
            cases_to_test
                .0
                .into_iter()
                .rev()
                .fold(cases_to_test.1, |else_, (label, body)| {
                    RawLambda::LifThenElse(
                        Box::new(raw_polyvariant_compare(scrut_lam.clone(), &label, loc)),
                        Box::new(body),
                        Box::new(else_),
                    )
                })
        };

        Some(result)
    }

    fn compile_simple_constructor_match_raw(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        let scrut_lam = self.convert_expr_raw(scrut);
        self.compile_simple_constructor_match_raw_from_scrut(loc, scrut_lam, cases, partial)
    }

    /// Check if a single leaf pattern (after peeling aliases and flattening or-patterns)
    /// is valid for simple constructor matching. Returns false if we should bail out.
    fn check_simple_constructor_leaf(
        pat: &Pattern,
        seen_const_tags: &mut std::collections::BTreeSet<i32>,
        seen_block_tags: &mut std::collections::BTreeSet<i32>,
        seen_extensions: &mut std::collections::BTreeSet<String>,
        repr_cstr: &mut Option<crate::types::ConstructorDescription>,
        has_non_ctor_constants: &mut bool,
    ) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_construct(_, cstr, args) => {
                if repr_cstr.is_none() {
                    *repr_cstr = Some(cstr.clone());
                }
                match &cstr.cstr_tag {
                    ConstructorTag::CstrConstant(tag) => {
                        args.is_empty() && seen_const_tags.insert(*tag)
                    }
                    ConstructorTag::CstrBlock(tag) => {
                        seen_block_tags.insert(*tag);
                        true
                    }
                    ConstructorTag::CstrExtension(path) => {
                        args.iter().all(Self::is_irrefutable_pattern)
                            && seen_extensions.insert(path.name())
                    }
                    ConstructorTag::CstrUnboxed => false,
                }
            }
            PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                *has_non_ctor_constants = true;
                seen_const_tags.insert(*i as i32)
            }
            PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                *has_non_ctor_constants = true;
                seen_const_tags.insert(*c as i32)
            }
            _ => false,
        }
    }

    /// Recursively check all leaves of an or-pattern for simple constructor matching.
    fn check_or_pattern_leaves(
        pat: &Pattern,
        seen_const_tags: &mut std::collections::BTreeSet<i32>,
        seen_block_tags: &mut std::collections::BTreeSet<i32>,
        seen_extensions: &mut std::collections::BTreeSet<String>,
        repr_cstr: &mut Option<crate::types::ConstructorDescription>,
        has_non_ctor_constants: &mut bool,
    ) -> bool {
        let (inner, _) = peel_aliases(pat);
        match &inner.pat_desc {
            PatternDesc::Tpat_or(left, right, _) => {
                Self::check_or_pattern_leaves(
                    left,
                    seen_const_tags,
                    seen_block_tags,
                    seen_extensions,
                    repr_cstr,
                    has_non_ctor_constants,
                ) && Self::check_or_pattern_leaves(
                    right,
                    seen_const_tags,
                    seen_block_tags,
                    seen_extensions,
                    repr_cstr,
                    has_non_ctor_constants,
                )
            }
            _ => {
                // For or-pattern block leaves, allow refutable sub-patterns.
                // collect_or_pattern_cases skips field binding for LstaticRaise actions,
                // so the sub-pattern info is lost but the tag dispatch still works.
                // The sub-pattern matching happens through the block_sub_groups mechanism.
                Self::check_simple_constructor_leaf(
                    inner,
                    seen_const_tags,
                    seen_block_tags,
                    seen_extensions,
                    repr_cstr,
                    has_non_ctor_constants,
                )
            }
        }
    }

    /// Recursively collect leaf patterns from or-patterns, adding each to const/block cases.
    fn collect_or_pattern_cases(
        &mut self,
        pat: &Pattern,
        scrut_id: &Ident,
        action: &RawLambda,
        const_cases: &mut Vec<(i32, RawLambda)>,
        block_cases: &mut Vec<(i32, RawLambda)>,
    ) {
        let (inner, aliases) = peel_aliases(pat);
        match &inner.pat_desc {
            PatternDesc::Tpat_or(left, right, _) => {
                self.collect_or_pattern_cases(left, scrut_id, action, const_cases, block_cases);
                self.collect_or_pattern_cases(right, scrut_id, action, const_cases, block_cases);
            }
            PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(tag) => const_cases.push((
                    *tag,
                    wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), action.clone()),
                )),
                ConstructorTag::CstrBlock(tag) => {
                    // Skip field bindings when action is a static raise (or-pattern shared exit)
                    // since the bound variables won't be used in the exit handler
                    let is_exit = matches!(action, RawLambda::LstaticRaise(_, _));
                    let act = if is_exit {
                        action.clone()
                    } else {
                        self.bind_constructor_args_irrefutably_raw(
                            scrut_id,
                            inner,
                            cstr,
                            args,
                            action.clone(),
                        )
                    };
                    block_cases.push((
                        *tag,
                        wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), act),
                    ));
                }
                _ => {}
            },
            PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                const_cases.push((
                    *i as i32,
                    wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), action.clone()),
                ));
            }
            PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                const_cases.push((
                    *c as i32,
                    wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), action.clone()),
                ));
            }
            _ => {}
        }
    }

    fn compile_simple_constructor_match_raw_from_scrut(
        &mut self,
        loc: Location,
        scrut_lam: RawLambda,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        #[derive(Clone)]
        enum DefaultCase {
            Any(RawLambda),
            Bind(Ident, RawLambda),
        }

        let mut seen_const_tags = std::collections::BTreeSet::new();
        let mut seen_block_tags = std::collections::BTreeSet::new();
        let mut seen_extensions = std::collections::BTreeSet::new();
        let mut default_case = None;
        let mut repr_cstr = None::<crate::types::ConstructorDescription>;
        let mut has_non_ctor_constants = false;
        // Track which cases use or-patterns (need shared body via catch/exit)
        let mut or_case_indices = std::collections::BTreeSet::new();

        let mut has_guards = false;
        for (case_idx, case) in cases.iter().enumerate() {
            if case.c_guard.is_some() {
                has_guards = true;
            }

            let (pat, _) = peel_aliases(&case.c_lhs);
            match &pat.pat_desc {
                PatternDesc::Tpat_or(_, _, _) => {
                    // Flatten or-pattern and validate each leaf
                    if !Self::check_or_pattern_leaves(
                        &case.c_lhs,
                        &mut seen_const_tags,
                        &mut seen_block_tags,
                        &mut seen_extensions,
                        &mut repr_cstr,
                        &mut has_non_ctor_constants,
                    ) {
                        return None;
                    }
                    or_case_indices.insert(case_idx);
                }
                PatternDesc::Tpat_construct(_, cstr, args) => {
                    if !Self::check_simple_constructor_leaf(
                        pat,
                        &mut seen_const_tags,
                        &mut seen_block_tags,
                        &mut seen_extensions,
                        &mut repr_cstr,
                        &mut has_non_ctor_constants,
                    ) {
                        return None;
                    }
                    // Ensure repr_cstr is set (check_simple_constructor_leaf does this)
                    let _ = (cstr, args);
                }
                PatternDesc::Tpat_constant(TConstant::Int(_))
                | PatternDesc::Tpat_constant(TConstant::Char(_)) => {
                    if !Self::check_simple_constructor_leaf(
                        pat,
                        &mut seen_const_tags,
                        &mut seen_block_tags,
                        &mut seen_extensions,
                        &mut repr_cstr,
                        &mut has_non_ctor_constants,
                    ) {
                        return None;
                    }
                }
                PatternDesc::Tpat_any => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Any(self.convert_expr_raw(&case.c_rhs)));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(
                        id.clone(),
                        self.convert_expr_raw(&case.c_rhs),
                    ));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(
                        id.clone(),
                        self.convert_expr_raw(&case.c_rhs),
                    ));
                }
                _ => return None,
            }
        }

        if seen_const_tags.is_empty() && seen_block_tags.is_empty() && seen_extensions.is_empty() {
            return None;
        }

        let scrut_name = self.fresh_name_from_cases("match", cases);
        let (scrut_id, scrut_var, wrap_let) = match &scrut_lam {
            RawLambda::Lvar(id) => (id.clone(), RawLambda::var(id.clone()), None),
            _ => {
                let scrut_id = self.fresh_ident(&scrut_name);
                (
                    scrut_id.clone(),
                    RawLambda::var(scrut_id.clone()),
                    Some((scrut_id, scrut_lam)),
                )
            }
        };

        if !seen_extensions.is_empty() {
            let mut extension_cases = Vec::<(crate::types::Path, RawLambda)>::new();
            for case in cases {
                let body = self.convert_expr_raw(&case.c_rhs);
                let (pat, aliases) = peel_aliases(&case.c_lhs);
                if let PatternDesc::Tpat_construct(_, cstr, args) = &pat.pat_desc {
                    if let ConstructorTag::CstrExtension(path) = &cstr.cstr_tag {
                        let act = wrap_aliases_raw(
                            &aliases,
                            RawLambda::var(scrut_id.clone()),
                            self.bind_constructor_args_irrefutably_raw(
                                &scrut_id, pat, cstr, args, body,
                            ),
                        );
                        extension_cases.push((path.clone(), act));
                    }
                }
            }

            let failaction = match default_case {
                Some(DefaultCase::Any(body)) => Some(body),
                Some(DefaultCase::Bind(id, body)) => Some(RawLambda::let_(
                    LetKind::Alias,
                    id,
                    RawLambda::var(scrut_id.clone()),
                    body,
                )),
                None => None,
            };

            let (default, remaining_cases) = match failaction {
                Some(fail) => (fail, extension_cases),
                None => {
                    let mut iter = extension_cases.into_iter();
                    let (_, default) = iter.next()?;
                    (default, iter.collect())
                }
            };

            let tests = remaining_cases
                .into_iter()
                .rev()
                .fold(default, |rem, (path, act)| {
                    RawLambda::LifThenElse(
                        Box::new(RawLambda::prim(
                            Primitive::PextensionSlotEq,
                            vec![
                                RawLambda::var(scrut_id.clone()),
                                self.translate_extension_path_raw(&path, loc),
                            ],
                            loc,
                        )),
                        Box::new(act),
                        Box::new(rem),
                    )
                });

            return Some(match wrap_let {
                Some((id, value)) => RawLambda::let_(LetKind::Alias, id, value, tests),
                None => tests,
            });
        }

        let mut const_cases = Vec::new();
        let mut block_cases = Vec::new();
        // Shared bodies from or-patterns: (exit_id, body)
        let mut shared_bodies: Vec<(i32, RawLambda)> = Vec::new();

        // Pre-scan: determine which block tags need sub-pattern grouping.
        // A tag needs grouping if it appears multiple times OR has refutable sub-patterns.
        let mut block_tag_counts: std::collections::BTreeMap<i32, usize> =
            std::collections::BTreeMap::new();
        let mut block_tags_needing_grouping: std::collections::BTreeSet<i32> =
            std::collections::BTreeSet::new();
        for case in cases.iter() {
            if case.c_guard.is_some() {
                // Skip guard cases in pre-scan (they don't affect tag grouping)
            }
            let (pat, _) = peel_aliases(&case.c_lhs);
            if let PatternDesc::Tpat_construct(_, cstr, args) = &pat.pat_desc {
                if let ConstructorTag::CstrBlock(tag) = &cstr.cstr_tag {
                    let count = block_tag_counts.entry(*tag).or_insert(0);
                    *count += 1;
                    if *count > 1 || !args.iter().all(Self::is_irrefutable_pattern) {
                        block_tags_needing_grouping.insert(*tag);
                    }
                }
            }
        }

        // Block sub-cases grouped by tag for sub-pattern matching
        // Each entry: (sub_patterns, body_with_aliases)
        let mut block_sub_groups: std::collections::BTreeMap<i32, Vec<(Vec<&Pattern>, RawLambda)>> =
            std::collections::BTreeMap::new();
        // Track constructor info per block tag
        let mut block_tag_info: std::collections::BTreeMap<
            i32,
            (&crate::types::ConstructorDescription, &Pattern),
        > = std::collections::BTreeMap::new();

        // Pre-allocate a fail exit for guard failures when guards are present.
        // This exit will be the same one used by make_switch_with_catch for the failaction.
        let guard_fail_exit = if has_guards {
            Some(self.next_raise_count())
        } else {
            None
        };

        for (case_idx, case) in cases.iter().enumerate() {
            let mut body = self.convert_expr_raw(&case.c_rhs);

            // Wrap body with guard check: if guard then body else (exit fail)
            if let (Some(guard), Some(fail_id)) = (&case.c_guard, guard_fail_exit) {
                let guard_lam = self.convert_expr_raw(guard);
                body = RawLambda::LifThenElse(
                    Box::new(guard_lam),
                    Box::new(body),
                    Box::new(RawLambda::LstaticRaise(fail_id, Vec::new())),
                );
            }

            if or_case_indices.contains(&case_idx) {
                // Or-pattern: share body via catch/exit
                let exit_id = self.next_raise_count();
                shared_bodies.push((exit_id, body));
                let action = RawLambda::LstaticRaise(exit_id, Vec::new());
                self.collect_or_pattern_cases(
                    &case.c_lhs,
                    &scrut_id,
                    &action,
                    &mut const_cases,
                    &mut block_cases,
                );
            } else {
                let (pat, aliases) = peel_aliases(&case.c_lhs);
                match &pat.pat_desc {
                    PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                        ConstructorTag::CstrConstant(tag) => const_cases.push((
                            *tag,
                            wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), body),
                        )),
                        ConstructorTag::CstrBlock(tag) => {
                            if block_tags_needing_grouping.contains(tag) {
                                // Tag needs sub-pattern grouping: collect for later
                                block_tag_info.entry(*tag).or_insert((cstr, pat));
                                let body_with_aliases = wrap_aliases_raw(
                                    &aliases,
                                    RawLambda::var(scrut_id.clone()),
                                    body,
                                );
                                block_sub_groups
                                    .entry(*tag)
                                    .or_default()
                                    .push((args.iter().collect(), body_with_aliases));
                            } else {
                                // Single case with irrefutable args: existing behavior
                                let all_wildcards = args
                                    .iter()
                                    .all(|a| matches!(a.pat_desc, PatternDesc::Tpat_any));
                                let block_body = if case.c_guard.is_some() && all_wildcards {
                                    body
                                } else {
                                    self.bind_constructor_args_irrefutably_raw(
                                        &scrut_id, pat, cstr, args, body,
                                    )
                                };
                                block_cases.push((
                                    *tag,
                                    wrap_aliases_raw(
                                        &aliases,
                                        RawLambda::var(scrut_id.clone()),
                                        block_body,
                                    ),
                                ));
                            }
                        }
                        ConstructorTag::CstrUnboxed | ConstructorTag::CstrExtension(_) => {}
                    },
                    PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                        const_cases.push((
                            *i as i32,
                            wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), body),
                        ));
                    }
                    PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                        const_cases.push((
                            *c as i32,
                            wrap_aliases_raw(&aliases, RawLambda::var(scrut_id.clone()), body),
                        ));
                    }
                    _ => {}
                }
            }
        }

        // Process block sub-groups: compile sub-matches for grouped block cases
        for (tag, sub_cases) in block_sub_groups {
            let (cstr, pat) = block_tag_info[&tag];
            let pat_loc = self.loc(pat.pat_loc);
            let block_body = self.compile_block_sub_match(&scrut_id, cstr, sub_cases, pat_loc);
            block_cases.push((tag, block_body));
        }

        // OCaml's combine_constructor: when sig_complete (all constructor tags covered),
        // fail_opt = None (no failaction). The wildcard/default fills missing tags explicitly.
        let failaction = match default_case {
            Some(default) => {
                let default_body = match default {
                    DefaultCase::Any(body) => body,
                    DefaultCase::Bind(id, body) => {
                        RawLambda::let_(LetKind::Alias, id, RawLambda::var(scrut_id.clone()), body)
                    }
                };

                // OCaml's combine_constructor: when we have a regular constructor type
                // (not extensions), a default/wildcard pattern makes the signature complete.
                // Fill missing tags explicitly and drop the failaction.
                let sig_complete = if let Some(cstr) = &repr_cstr {
                    cstr.cstr_consts >= 0
                } else {
                    false
                };

                if sig_complete && !has_guards {
                    // OCaml's mk_failaction_pos: fill missing tags with exit to default,
                    // wrap default body in catch handler (like mk_failaction_pos does).
                    let has_missing = if let Some(cstr) = &repr_cstr {
                        (0..cstr.cstr_consts).any(|t| !seen_const_tags.contains(&t))
                            || (0..cstr.cstr_nonconsts).any(|t| !seen_block_tags.contains(&t))
                    } else {
                        false
                    };

                    if has_missing {
                        let default_exit = self.next_raise_count();
                        let default_raise = RawLambda::LstaticRaise(default_exit, Vec::new());
                        if let Some(cstr) = &repr_cstr {
                            for tag in 0..cstr.cstr_consts {
                                if !seen_const_tags.contains(&tag) {
                                    const_cases.push((tag, default_raise.clone()));
                                }
                            }
                            for tag in 0..cstr.cstr_nonconsts {
                                if !seen_block_tags.contains(&tag) {
                                    block_cases.push((tag, default_raise.clone()));
                                }
                            }
                        }
                        // Store the catch handler to wrap later
                        shared_bodies.push((default_exit, default_body));
                    } else {
                        // All tags already covered by explicit patterns, default is dead code
                    }
                    None
                } else {
                    Some(Box::new(default_body))
                }
            }
            None => match partial {
                Partial::Partial => Some(Box::new(RawLambda::from_lowered(
                    self.match_failure(loc.clone()),
                ))),
                Partial::Total => None,
            },
        };

        // Detect if any case pattern is an int constant (not char/variant).
        // For int constants, OCaml uses low=min_int creating fail intervals
        // at both ends, making isout optimal. For char/variant, fail is only
        // at the top when starting from 0, making >= optimal.
        let has_int_constants_detected = cases.iter().any(|case| {
            fn has_int_in_pat(pat: &Pattern) -> bool {
                match &pat.pat_desc {
                    PatternDesc::Tpat_constant(TConstant::Int(_)) => true,
                    PatternDesc::Tpat_or(l, r, _) => has_int_in_pat(l) || has_int_in_pat(r),
                    PatternDesc::Tpat_alias(inner, _, _) => has_int_in_pat(inner),
                    _ => false,
                }
            }
            has_int_in_pat(&case.c_lhs)
        });

        let dense_const_partial = if block_cases.is_empty() {
            failaction.as_ref().and_then(|default| {
                let mut sorted_consts = const_cases.clone();
                sorted_consts.sort_by_key(|(tag, _)| *tag);
                let first = sorted_consts.first()?.0;
                let last = sorted_consts.last()?.0;
                let is_dense = sorted_consts
                    .iter()
                    .enumerate()
                    .all(|(idx, (tag, _))| *tag == first + idx as i32);
                if !is_dense {
                    return None;
                }

                // Single-case optimization: use direct comparison instead of isout+switch
                if sorted_consts.len() == 1 {
                    let (tag, action) = sorted_consts.into_iter().next()?;
                    let exit_id = self.next_raise_count();
                    let cond = RawLambda::prim(
                        Primitive::Pjscomp(Comparison::Neq),
                        vec![scrut_var.clone(), RawLambda::const_(Constant::int(tag))],
                        loc,
                    );
                    return Some(RawLambda::LstaticCatch(
                        Box::new(RawLambda::LifThenElse(
                            Box::new(cond),
                            Box::new(RawLambda::LstaticRaise(exit_id, Vec::new())),
                            Box::new(action),
                        )),
                        (exit_id, Vec::new()),
                        Box::new((**default).clone()),
                    ));
                }

                let exit_id = self.next_raise_count();
                // For char constants and variant constructors starting at 0,
                // OCaml's Switch module picks Sep optimization: >= (last+1).
                // For int constants, OCaml uses low=min_int which creates
                // fail intervals at both ends, making Inter (isout) optimal.
                let is_out = if first == 0 && !has_int_constants_detected {
                    RawLambda::prim(
                        Primitive::Pintcomp(Comparison::Ge),
                        vec![
                            scrut_var.clone(),
                            RawLambda::const_(Constant::int(last + 1)),
                        ],
                        loc,
                    )
                } else {
                    let offset_arg = if first == 0 {
                        scrut_var.clone()
                    } else {
                        RawLambda::prim(Primitive::Poffsetint(-first), vec![scrut_var.clone()], loc)
                    };
                    RawLambda::prim(Primitive::Pisout(last - first), vec![offset_arg], loc)
                };

                // If all cases map to the same static raise, use it directly
                // instead of generating a switch (matches OCaml's share_actions)
                let all_same_exit = sorted_consts.iter().all(|(_, act)| {
                    matches!(act, RawLambda::LstaticRaise(id, args) if args.is_empty()
                    && *id == match &sorted_consts[0].1 {
                        RawLambda::LstaticRaise(id0, _) => *id0,
                        _ => return false,
                    })
                });

                let in_range_action = if all_same_exit {
                    sorted_consts[0].1.clone()
                } else {
                    RawLambda::Lswitch(
                        Box::new(scrut_var.clone()),
                        crate::raw_lambda::RawLambdaSwitch {
                            sw_numconsts: sorted_consts.len(),
                            sw_consts_full: false,
                            sw_consts: sorted_consts,
                            sw_numblocks: 0,
                            sw_blocks_full: false,
                            sw_blocks: Vec::new(),
                            sw_failaction: None,
                            sw_names: None,
                        },
                        Location::none(),
                    )
                };

                Some(RawLambda::LstaticCatch(
                    Box::new(RawLambda::LifThenElse(
                        Box::new(is_out),
                        Box::new(RawLambda::LstaticRaise(exit_id, Vec::new())),
                        Box::new(in_range_action),
                    )),
                    (exit_id, Vec::new()),
                    Box::new((**default).clone()),
                ))
            })
        } else {
            None
        };

        let mut result = if let Some(result) = dense_const_partial {
            result
        } else if !has_non_ctor_constants {
            if let Some(cstr) = repr_cstr.as_ref() {
                match (
                    cstr.cstr_consts,
                    cstr.cstr_nonconsts,
                    const_cases.as_slice(),
                    block_cases.as_slice(),
                    failaction.as_ref(),
                ) {
                    (1, 1, [(0, act1)], [(0, act2)], _)
                        if cstr.cstr_name == "::"
                            || cstr.cstr_name == "[]"
                            || constructor_has_optional_shape(cstr) =>
                    {
                        let cond = if constructor_has_optional_shape(cstr) {
                            RawLambda::prim(Primitive::PisNotNone, vec![scrut_var.clone()], loc)
                        } else {
                            RawLambda::prim(
                                Primitive::Pjscomp(Comparison::Neq),
                                vec![scrut_var.clone(), RawLambda::const_(Constant::int(0))],
                                loc,
                            )
                        };
                        RawLambda::LifThenElse(
                            Box::new(cond),
                            Box::new(act2.clone()),
                            Box::new(act1.clone()),
                        )
                    }
                    (2, 0, [(i1, act1), (_, act2)], [], None)
                        if cstr.cstr_name == "true" || cstr.cstr_name == "false" =>
                    {
                        if *i1 == 0 {
                            RawLambda::LifThenElse(
                                Box::new(scrut_var.clone()),
                                Box::new(act2.clone()),
                                Box::new(act1.clone()),
                            )
                        } else {
                            RawLambda::LifThenElse(
                                Box::new(scrut_var.clone()),
                                Box::new(act1.clone()),
                                Box::new(act2.clone()),
                            )
                        }
                    }
                    // Single-constructor block type: no switch needed
                    (0, _, [], [(_, act)], None) => act.clone(),
                    _ => self.make_switch_with_catch_exit(
                        scrut_var.clone(),
                        const_cases,
                        block_cases,
                        failaction,
                        guard_fail_exit,
                    ),
                }
            } else {
                self.make_switch_with_catch_exit(
                    scrut_var.clone(),
                    const_cases,
                    block_cases,
                    failaction,
                    guard_fail_exit,
                )
            }
        } else {
            self.make_switch_with_catch_exit(
                scrut_var.clone(),
                const_cases,
                block_cases,
                failaction,
                guard_fail_exit,
            )
        };

        // Wrap in catch handlers for shared or-pattern bodies
        for (exit_id, handler) in shared_bodies.into_iter().rev() {
            result =
                RawLambda::LstaticCatch(Box::new(result), (exit_id, Vec::new()), Box::new(handler));
        }

        Some(match wrap_let {
            Some((id, value)) => RawLambda::let_(LetKind::Strict, id, value, result),
            None => result,
        })
    }

    fn compile_irrefutable_match(&mut self, scrut: &Expression, cases: &[Case]) -> Option<Lambda> {
        if cases.len() != 1 || cases[0].c_guard.is_some() {
            return None;
        }

        if !Self::is_irrefutable_pattern(&cases[0].c_lhs) {
            return None;
        }

        let body = self.convert_expr(&cases[0].c_rhs);
        let scrut_lam = self.convert_expr(scrut);
        Some(self.bind_irrefutable_pattern(&cases[0].c_lhs, scrut_lam, body))
    }

    fn bind_constructor_args_irrefutably(
        &mut self,
        scrut_id: &Ident,
        pat: &Pattern,
        cstr: &crate::types::ConstructorDescription,
        args: &[Pattern],
        body: Lambda,
    ) -> Lambda {
        let pat_loc = self.loc(pat.pat_loc);
        let tmp = self.fresh_ident("ctor");
        let mut result = body;

        for (idx, arg_pat) in args.iter().enumerate().rev() {
            let field = match &cstr.cstr_tag {
                ConstructorTag::CstrBlock(_) => Lambda::prim(
                    Primitive::Pfield(
                        idx as i32,
                        if cstr.cstr_name == "::" {
                            FieldDbgInfo::Cons
                        } else {
                            FieldDbgInfo::Variant
                        },
                    ),
                    vec![Lambda::var(tmp.clone())],
                    pat_loc.clone(),
                ),
                ConstructorTag::CstrUnboxed => Lambda::var(tmp.clone()),
                ConstructorTag::CstrConstant(_) | ConstructorTag::CstrExtension(_) => {
                    unreachable!(
                        "constructor payload binding only applies to non-constant constructors"
                    )
                }
            };
            result = self.bind_irrefutable_pattern(arg_pat, field, result);
        }

        Lambda::let_(LetKind::Alias, tmp, Lambda::var(scrut_id.clone()), result)
    }

    /// Compile a nested sub-match for block constructor cases that share the same tag
    /// but have different (potentially refutable) sub-patterns.
    ///
    /// This implements OCaml's matching.ml behavior for constructor sub-matrix compilation:
    /// extract fields, then recursively match on the extracted field values.
    fn compile_block_sub_match(
        &mut self,
        scrut_id: &Ident,
        cstr: &crate::types::ConstructorDescription,
        sub_cases: Vec<(Vec<&Pattern>, RawLambda)>,
        loc: Location,
    ) -> RawLambda {
        let arity = cstr.cstr_arity as usize;

        // Handle optional shape (Some(...) with refutable inner pattern)
        if constructor_has_optional_shape(cstr) && arity == 1 {
            return self.compile_optional_block_sub_match(scrut_id, cstr, sub_cases, loc);
        }

        // Determine field variable names using OCaml's name_pattern convention:
        // use the first variable name found across all cases for each field position
        let field_ids: Vec<Ident> = (0..arity)
            .map(|i| {
                sub_cases
                    .iter()
                    .find_map(|(pats, _)| {
                        pats.get(i).and_then(|p| {
                            let (inner, _) = peel_aliases(p);
                            match &inner.pat_desc {
                                PatternDesc::Tpat_var(id, _) => Some(id.clone()),
                                _ => None,
                            }
                        })
                    })
                    .unwrap_or_else(|| self.fresh_ident("match"))
            })
            .collect();

        let field_info = if cstr.cstr_name == "::" {
            FieldDbgInfo::Cons
        } else {
            FieldDbgInfo::Variant
        };

        // For arity 1: try to build a specialized sub-match (string switch, etc.)
        if arity == 1 {
            let field_id = &field_ids[0];
            let field_read = RawLambda::prim(
                Primitive::Pfield(0, field_info),
                vec![RawLambda::var(scrut_id.clone())],
                loc,
            );

            let inner = self.compile_single_field_sub_match(field_id, &sub_cases, loc);

            return RawLambda::let_(LetKind::Alias, field_id.clone(), field_read, inner);
        }

        // For multi-field: use sequential catch/exit approach
        // Each row (case) is tried in order; if its sub-pattern test fails, exit to the next row.
        self.compile_multi_field_sub_match(scrut_id, cstr, &field_ids, &field_info, sub_cases, loc)
    }

    /// Compile a sub-match for a single-field constructor.
    /// Analyzes sub-pattern types and generates the appropriate match structure.
    fn compile_single_field_sub_match(
        &mut self,
        field_id: &Ident,
        sub_cases: &[(Vec<&Pattern>, RawLambda)],
        loc: Location,
    ) -> RawLambda {
        // Categorize sub-patterns
        let mut string_cases: Vec<(String, RawLambda)> = Vec::new();
        let mut int_cases: Vec<(i32, RawLambda)> = Vec::new();
        let mut ctor_cases: Vec<(Vec<&Pattern>, RawLambda)> = Vec::new();
        let mut default_body: Option<RawLambda> = None;
        let mut has_complex = false;
        let mut ctor_info: Option<&crate::types::ConstructorDescription> = None;

        for (pats, body) in sub_cases {
            let (pat, _aliases) = peel_aliases(pats[0]);
            match &pat.pat_desc {
                PatternDesc::Tpat_constant(TConstant::String(s, _)) => {
                    string_cases.push((s.clone(), body.clone()));
                }
                PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                    int_cases.push((*i as i32, body.clone()));
                }
                PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                    int_cases.push((*c as i32, body.clone()));
                }
                PatternDesc::Tpat_construct(_, cstr, args) => {
                    // Constructor sub-pattern: collect for nested switch
                    if ctor_info.is_none() {
                        ctor_info = Some(cstr);
                    }
                    ctor_cases.push((args.iter().collect(), body.clone()));
                }
                PatternDesc::Tpat_var(id, _) => {
                    if id == field_id {
                        default_body = Some(body.clone());
                    } else {
                        default_body = Some(RawLambda::let_(
                            LetKind::Alias,
                            id.clone(),
                            RawLambda::var(field_id.clone()),
                            body.clone(),
                        ));
                    }
                }
                PatternDesc::Tpat_any => {
                    default_body = Some(body.clone());
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    default_body = Some(RawLambda::let_(
                        LetKind::Alias,
                        id.clone(),
                        RawLambda::var(field_id.clone()),
                        body.clone(),
                    ));
                }
                _ => {
                    has_complex = true;
                }
            }
        }

        // String switch
        if !string_cases.is_empty() && !has_complex && int_cases.is_empty() {
            string_cases.sort_by(|(a, _), (b, _)| a.cmp(b));
            if let Some(default) = default_body {
                let fail_exit = self.next_raise_count();
                let sw = RawLambda::LstringSwitch(
                    Box::new(RawLambda::var(field_id.clone())),
                    string_cases,
                    Some(Box::new(RawLambda::LstaticRaise(fail_exit, Vec::new()))),
                );
                return RawLambda::LstaticCatch(
                    Box::new(sw),
                    (fail_exit, Vec::new()),
                    Box::new(default),
                );
            } else {
                // No default - string switch without catch
                return RawLambda::LstringSwitch(
                    Box::new(RawLambda::var(field_id.clone())),
                    string_cases,
                    None,
                );
            }
        }

        // Int constant tests with catch/exit (OCaml's != comparison pattern)
        if !int_cases.is_empty() && !has_complex && string_cases.is_empty() && ctor_cases.is_empty()
        {
            return self.compile_int_test_chain(field_id, &int_cases, default_body, loc);
        }

        // Constructor sub-patterns: generate nested switch on the field var
        if !ctor_cases.is_empty() && !has_complex && string_cases.is_empty() && int_cases.is_empty()
        {
            // Re-scan the original sub_cases to build a nested constructor switch
            // using the inner constructor tags
            let mut inner_const_cases: Vec<(i32, RawLambda)> = Vec::new();
            let mut inner_block_groups: std::collections::BTreeMap<
                i32,
                Vec<(Vec<&Pattern>, RawLambda)>,
            > = std::collections::BTreeMap::new();
            let mut inner_repr_cstr: Option<&crate::types::ConstructorDescription> = None;

            for (pats, body) in sub_cases {
                let (pat, _) = peel_aliases(pats[0]);
                if let PatternDesc::Tpat_construct(_, cstr, args) = &pat.pat_desc {
                    if inner_repr_cstr.is_none() {
                        inner_repr_cstr = Some(cstr);
                    }
                    match &cstr.cstr_tag {
                        ConstructorTag::CstrConstant(tag) => {
                            inner_const_cases.push((*tag, body.clone()));
                        }
                        ConstructorTag::CstrBlock(tag) => {
                            if args.iter().all(Self::is_irrefutable_pattern) {
                                let inner_body = self.bind_constructor_args_irrefutably_raw(
                                    field_id,
                                    pat,
                                    cstr,
                                    args,
                                    body.clone(),
                                );
                                inner_block_groups
                                    .entry(*tag)
                                    .or_default()
                                    .push((args.iter().collect(), inner_body));
                            } else {
                                // Recursively handle inner refutable sub-patterns
                                inner_block_groups
                                    .entry(*tag)
                                    .or_default()
                                    .push((args.iter().collect(), body.clone()));
                            }
                        }
                        _ => {}
                    }
                }
            }

            // Build the inner switch
            let mut final_block_cases: Vec<(i32, RawLambda)> = Vec::new();
            for (tag, group) in inner_block_groups {
                if group.len() == 1 {
                    final_block_cases.push((tag, group.into_iter().next().unwrap().1));
                } else {
                    // Multiple cases for same inner tag: recursive sub-match
                    if let Some(cstr) = inner_repr_cstr {
                        let body = self.compile_block_sub_match(field_id, cstr, group, loc);
                        final_block_cases.push((tag, body));
                    }
                }
            }

            inner_const_cases.sort_by_key(|(t, _)| *t);
            final_block_cases.sort_by_key(|(t, _)| *t);

            let failaction = default_body.map(Box::new);

            return self.make_switch_with_catch_exit(
                RawLambda::var(field_id.clone()),
                inner_const_cases,
                final_block_cases,
                failaction,
                None,
            );
        }

        // Fallback: sequential catch/exit for complex sub-patterns
        self.compile_sequential_single_field(field_id, sub_cases, loc)
    }

    /// Compile int constant test chain matching OCaml's != comparison pattern:
    /// (catch (if (!= x val0) (exit N) body0) with (N) ...)
    fn compile_int_test_chain(
        &mut self,
        field_id: &Ident,
        int_cases: &[(i32, RawLambda)],
        default_body: Option<RawLambda>,
        loc: Location,
    ) -> RawLambda {
        let fail_exit = self.next_raise_count();
        let fail_raise = RawLambda::LstaticRaise(fail_exit, Vec::new());

        // Build nested if-chain: if (!= x val0) (exit N) body0
        // For the last case with no default, don't add exit check
        let mut inner = fail_raise;
        for (val, body) in int_cases.iter().rev() {
            let cond = RawLambda::prim(
                Primitive::Pjscomp(Comparison::Neq),
                vec![
                    RawLambda::var(field_id.clone()),
                    RawLambda::const_(Constant::int(*val)),
                ],
                loc,
            );
            inner = RawLambda::LifThenElse(
                Box::new(cond),
                Box::new(inner.clone()),
                Box::new(body.clone()),
            );
        }

        if let Some(default) = default_body {
            RawLambda::LstaticCatch(Box::new(inner), (fail_exit, Vec::new()), Box::new(default))
        } else {
            inner
        }
    }

    /// Fallback: sequential single-field sub-match with catch/exit chains
    fn compile_sequential_single_field(
        &mut self,
        field_id: &Ident,
        sub_cases: &[(Vec<&Pattern>, RawLambda)],
        loc: Location,
    ) -> RawLambda {
        // Process cases in reverse, building catch/exit chains
        let mut result: Option<RawLambda> = None;

        for (pats, body) in sub_cases.iter().rev() {
            let (pat, _) = peel_aliases(pats[0]);
            match result {
                None => {
                    // Last case: bind the pattern and run
                    result = Some(self.bind_sub_pattern_raw(field_id, pat, body.clone()));
                }
                Some(rest) => {
                    let exit_id = self.next_raise_count();
                    let test = self.test_sub_pattern_raw(field_id, pat, body.clone(), exit_id, loc);
                    result = Some(RawLambda::LstaticCatch(
                        Box::new(test),
                        (exit_id, Vec::new()),
                        Box::new(rest),
                    ));
                }
            }
        }

        result.unwrap_or(RawLambda::unit())
    }

    /// Bind a sub-pattern variable to the field value (for the last/default case)
    fn bind_sub_pattern_raw(&self, field_id: &Ident, pat: &Pattern, body: RawLambda) -> RawLambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) => {
                if id == field_id {
                    body
                } else {
                    RawLambda::let_(
                        LetKind::Alias,
                        id.clone(),
                        RawLambda::var(field_id.clone()),
                        body,
                    )
                }
            }
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner_body = self.bind_sub_pattern_raw(field_id, inner, body);
                RawLambda::let_(
                    LetKind::Alias,
                    id.clone(),
                    RawLambda::var(field_id.clone()),
                    inner_body,
                )
            }
            _ => body, // Constants/constructors in last position are unusual
        }
    }

    /// Test a sub-pattern against the field value, with exit on failure
    fn test_sub_pattern_raw(
        &mut self,
        field_id: &Ident,
        pat: &Pattern,
        body: RawLambda,
        fail_exit: i32,
        loc: Location,
    ) -> RawLambda {
        let fail_raise = RawLambda::LstaticRaise(fail_exit, Vec::new());
        match &pat.pat_desc {
            PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                let cond = RawLambda::prim(
                    Primitive::Pjscomp(Comparison::Neq),
                    vec![
                        RawLambda::var(field_id.clone()),
                        RawLambda::const_(Constant::int(*i as i32)),
                    ],
                    loc,
                );
                RawLambda::LifThenElse(Box::new(cond), Box::new(fail_raise), Box::new(body))
            }
            PatternDesc::Tpat_constant(TConstant::String(s, _)) => {
                let cond = RawLambda::prim(
                    Primitive::Pjscomp(Comparison::Neq),
                    vec![
                        RawLambda::var(field_id.clone()),
                        RawLambda::const_(Constant::string(s.clone())),
                    ],
                    loc,
                );
                RawLambda::LifThenElse(Box::new(cond), Box::new(fail_raise), Box::new(body))
            }
            PatternDesc::Tpat_var(id, _) => {
                if id == field_id {
                    body
                } else {
                    RawLambda::let_(
                        LetKind::Alias,
                        id.clone(),
                        RawLambda::var(field_id.clone()),
                        body,
                    )
                }
            }
            PatternDesc::Tpat_any => body,
            _ => {
                // For other patterns, fall through (exit to next case)
                fail_raise
            }
        }
    }

    /// Compile sub-match for optional-shape constructors (Some(...) with refutable inner)
    fn compile_optional_block_sub_match(
        &mut self,
        scrut_id: &Ident,
        cstr: &crate::types::ConstructorDescription,
        sub_cases: Vec<(Vec<&Pattern>, RawLambda)>,
        loc: Location,
    ) -> RawLambda {
        // Extract the option payload using val_from_option
        let field_id = sub_cases
            .iter()
            .find_map(|(pats, _)| {
                pats.first().and_then(|p| {
                    let (inner, _) = peel_aliases(p);
                    match &inner.pat_desc {
                        PatternDesc::Tpat_var(id, _) => Some(id.clone()),
                        _ => None,
                    }
                })
            })
            .unwrap_or_else(|| self.fresh_ident("match"));

        let from_option = sub_cases
            .first()
            .and_then(|(pats, _)| pats.first())
            .map(|p| {
                let env_ref = self.type_ctx.get_typed_env(p.pat_env);
                if env_ref
                    .as_ref()
                    .map(|e| type_cannot_contain_undefined(self.type_ctx, e.as_ref(), p.pat_type))
                    .unwrap_or_else(|| {
                        type_cannot_contain_undefined_no_env(self.type_ctx, p.pat_type)
                    })
                {
                    Primitive::PvalFromOptionNotNest
                } else {
                    Primitive::PvalFromOption
                }
            })
            .unwrap_or(Primitive::PvalFromOption);

        let payload = RawLambda::prim(from_option, vec![RawLambda::var(scrut_id.clone())], loc);

        let inner = self.compile_single_field_sub_match(&field_id, &sub_cases, loc);

        RawLambda::let_(LetKind::Alias, field_id, payload, inner)
    }

    /// Compile multi-field sub-match using sequential catch/exit approach.
    /// Matches OCaml's column-by-column pattern testing with lazy field extraction.
    fn compile_multi_field_sub_match(
        &mut self,
        scrut_id: &Ident,
        _cstr: &crate::types::ConstructorDescription,
        field_ids: &[Ident],
        field_info: &FieldDbgInfo,
        sub_cases: Vec<(Vec<&Pattern>, RawLambda)>,
        loc: Location,
    ) -> RawLambda {
        if sub_cases.is_empty() {
            return RawLambda::unit();
        }
        if sub_cases.len() == 1 {
            // Single case: bind all fields
            let (pats, body) = &sub_cases[0];
            return self.bind_multi_field_patterns(
                scrut_id,
                field_ids,
                field_info,
                pats,
                body.clone(),
                loc,
            );
        }

        // Multiple cases: try each row with catch/exit
        let mut result: Option<RawLambda> = None;

        for (pats, body) in sub_cases.iter().rev() {
            match result {
                None => {
                    // Last case: bind all fields and run
                    result = Some(self.bind_multi_field_patterns(
                        scrut_id,
                        field_ids,
                        field_info,
                        pats,
                        body.clone(),
                        loc,
                    ));
                }
                Some(rest) => {
                    let exit_id = self.next_raise_count();
                    // Test this row's patterns with exit on failure
                    let test = self.test_multi_field_row(
                        scrut_id,
                        field_ids,
                        field_info,
                        pats,
                        body.clone(),
                        exit_id,
                        loc,
                    );
                    result = Some(RawLambda::LstaticCatch(
                        Box::new(test),
                        (exit_id, Vec::new()),
                        Box::new(rest),
                    ));
                }
            }
        }

        result.unwrap_or(RawLambda::unit())
    }

    /// Bind all fields from a multi-field constructor pattern (for the default/last case)
    fn bind_multi_field_patterns(
        &mut self,
        scrut_id: &Ident,
        field_ids: &[Ident],
        field_info: &FieldDbgInfo,
        pats: &[&Pattern],
        body: RawLambda,
        loc: Location,
    ) -> RawLambda {
        let mut result = body;
        // Bind fields in reverse order for correct scoping
        for (i, (pat, field_id)) in pats.iter().zip(field_ids.iter()).enumerate().rev() {
            let (inner, _) = peel_aliases(pat);
            let field_read = RawLambda::prim(
                Primitive::Pfield(i as i32, field_info.clone()),
                vec![RawLambda::var(scrut_id.clone())],
                loc,
            );
            match &inner.pat_desc {
                PatternDesc::Tpat_var(id, _) => {
                    result = RawLambda::let_(LetKind::Alias, id.clone(), field_read, result);
                }
                PatternDesc::Tpat_any => {
                    // OCaml's make_constr_matching still creates a binding for wildcards
                    let match_id = self.fresh_ident("match");
                    result = RawLambda::let_(LetKind::Alias, match_id, field_read, result);
                }
                _ => {
                    // For constants etc. in last row, bind with field_id name
                    result = RawLambda::let_(LetKind::Alias, field_id.clone(), field_read, result);
                }
            }
        }
        result
    }

    /// Test a row of multi-field patterns, with lazy field extraction.
    /// Matches OCaml's approach of extracting and testing fields sequentially.
    fn test_multi_field_row(
        &mut self,
        scrut_id: &Ident,
        field_ids: &[Ident],
        field_info: &FieldDbgInfo,
        pats: &[&Pattern],
        body: RawLambda,
        fail_exit: i32,
        loc: Location,
    ) -> RawLambda {
        let fail_raise = RawLambda::LstaticRaise(fail_exit, Vec::new());
        let mut result = body;

        // Process fields in reverse order, building up the test chain
        for (i, (pat, field_id)) in pats.iter().zip(field_ids.iter()).enumerate().rev() {
            let (inner, _) = peel_aliases(pat);
            let field_read = RawLambda::prim(
                Primitive::Pfield(i as i32, field_info.clone()),
                vec![RawLambda::var(scrut_id.clone())],
                loc,
            );

            match &inner.pat_desc {
                PatternDesc::Tpat_constant(TConstant::Int(val)) => {
                    let cond = RawLambda::prim(
                        Primitive::Pjscomp(Comparison::Neq),
                        vec![
                            RawLambda::var(field_id.clone()),
                            RawLambda::const_(Constant::int(*val as i32)),
                        ],
                        loc,
                    );
                    result = RawLambda::let_(
                        LetKind::Alias,
                        field_id.clone(),
                        field_read,
                        RawLambda::LifThenElse(
                            Box::new(cond),
                            Box::new(fail_raise.clone()),
                            Box::new(result),
                        ),
                    );
                }
                PatternDesc::Tpat_var(id, _) => {
                    // Variable: just bind, no test needed
                    result = RawLambda::let_(LetKind::Alias, id.clone(), field_read, result);
                }
                PatternDesc::Tpat_any => {
                    // Wildcard: no binding or test needed in test path
                    // (OCaml skips unused field reads in test rows)
                }
                _ => {
                    // Unknown pattern in test row - exit (can't match)
                    result = fail_raise.clone();
                }
            }
        }

        result
    }

    fn is_irrefutable_pattern(pat: &Pattern) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
            PatternDesc::Tpat_alias(inner, _, _) => Self::is_irrefutable_pattern(inner),
            PatternDesc::Tpat_tuple(items) | PatternDesc::Tpat_array(items) => {
                items.iter().all(Self::is_irrefutable_pattern)
            }
            PatternDesc::Tpat_record(fields, _) => fields
                .iter()
                .all(|(_, _, pat, _)| Self::is_irrefutable_pattern(pat)),
            PatternDesc::Tpat_construct(_, cstr, args) => match cstr.cstr_tag {
                ConstructorTag::CstrUnboxed => args.iter().all(Self::is_irrefutable_pattern),
                ConstructorTag::CstrConstant(_) => {
                    args.is_empty() && cstr.cstr_consts == 1 && cstr.cstr_nonconsts == 0
                }
                ConstructorTag::CstrBlock(_) => {
                    cstr.cstr_consts == 0
                        && cstr.cstr_nonconsts == 1
                        && args.iter().all(Self::is_irrefutable_pattern)
                }
                ConstructorTag::CstrExtension(_) => false,
            },
            PatternDesc::Tpat_variant(_, Some(inner), _) => Self::is_irrefutable_pattern(inner),
            PatternDesc::Tpat_variant(_, None, _) => false,
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_or(_, _, _) => false,
        }
    }

    fn bind_irrefutable_pattern(&mut self, pat: &Pattern, scrut: Lambda, body: Lambda) -> Lambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_var(id, _) => Lambda::let_(LetKind::Alias, id.clone(), scrut, body),
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner = self.bind_irrefutable_pattern(inner, scrut.clone(), body);
                Lambda::let_(LetKind::Alias, id.clone(), scrut, inner)
            }
            PatternDesc::Tpat_tuple(items) => {
                let tmp = self.fresh_ident("tuple");
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate().rev() {
                    let field = Lambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![Lambda::var(tmp.clone())],
                        pat_loc.clone(),
                    );
                    result = self.bind_irrefutable_pattern(item, field, result);
                }
                Lambda::let_(LetKind::Alias, tmp, scrut, result)
            }
            PatternDesc::Tpat_record(fields, _) => {
                let tmp = self.fresh_ident("match");
                let mut result = body;
                for (lid, lbl, inner_pat, _) in fields.iter().rev() {
                    let field = Lambda::prim(
                        Primitive::Pfield(
                            lbl.lbl_pos,
                            FieldDbgInfo::Record {
                                name: label_runtime_name(lbl),
                                mutable_flag: to_parser_mutable(lbl.lbl_mut),
                            },
                        ),
                        vec![Lambda::var(tmp.clone())],
                        self.loc(lid.loc),
                    );
                    result = self.bind_irrefutable_pattern(inner_pat, field, result);
                }
                Lambda::let_(LetKind::Alias, tmp, scrut, result)
            }
            PatternDesc::Tpat_array(items) => {
                let tmp = self.fresh_ident("array");
                let pat_loc = self.loc(pat.pat_loc);
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
                    result = self.bind_irrefutable_pattern(item, field, result);
                }
                Lambda::let_(LetKind::Alias, tmp, scrut, result)
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(cstr.cstr_tag, ConstructorTag::CstrUnboxed) =>
            {
                if let Some(arg) = args.first() {
                    self.bind_irrefutable_pattern(arg, scrut, body)
                } else {
                    body
                }
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(cstr.cstr_tag, ConstructorTag::CstrConstant(_))
                    && args.is_empty()
                    && cstr.cstr_consts == 1
                    && cstr.cstr_nonconsts == 0 =>
            {
                body
            }
            PatternDesc::Tpat_variant(_, Some(inner), _) => {
                let payload = Lambda::prim(
                    Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                    vec![scrut],
                    self.loc(pat.pat_loc),
                );
                self.bind_irrefutable_pattern(inner, payload, body)
            }
            _ => unreachable!("expected irrefutable pattern"),
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
                RawLambda::let_(LetKind::Alias, id.clone(), scrut, body)
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner = self.bind_irrefutable_pattern_raw(inner, scrut.clone(), body);
                // OCaml's bind_check: skip binding when scrut is already the same variable
                if let RawLambda::Lvar(v) = &scrut {
                    if v.same(id) {
                        return inner;
                    }
                }
                RawLambda::let_(LetKind::Alias, id.clone(), scrut, inner)
            }
            PatternDesc::Tpat_tuple(items) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.fresh_ident("match");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate() {
                    let field = RawLambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![RawLambda::var(tmp.clone())],
                        pat_loc,
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
            PatternDesc::Tpat_record(fields, _) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.fresh_ident("match");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let mut result = body;

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
                                let field = RawLambda::var(tmp.clone());
                                if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                                    result =
                                        RawLambda::let_(LetKind::Alias, id.clone(), field, result);
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
                                RecordRepresentation::RecordRegular => FieldDbgInfo::Record {
                                    name: name.clone(),
                                    mutable_flag: if matches!(mutflag, TypeMutableFlag::Mutable) {
                                        crate::parser::ast::MutableFlag::Mutable
                                    } else {
                                        crate::parser::ast::MutableFlag::Immutable
                                    },
                                },
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
                                self.loc(lid.loc)
                            } else {
                                self.loc(pat_loc_idx)
                            };

                            let field = RawLambda::prim(
                                Primitive::Pfield(field_pos, info),
                                vec![RawLambda::var(tmp.clone())],
                                loc,
                            );

                            if let Some((_, _, inner_pat)) = mentioned.get(pos) {
                                // Mentioned in pattern: bind using the pattern's variable
                                if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                                    result =
                                        RawLambda::let_(field_let_kind, id.clone(), field, result);
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
                            RecordRepresentation::RecordUnboxed(_) => RawLambda::var(tmp.clone()),
                            _ => {
                                let Some((pos, info)) = raw_record_field_access(lbl) else {
                                    continue;
                                };
                                RawLambda::prim(
                                    Primitive::Pfield(pos, info),
                                    vec![RawLambda::var(tmp.clone())],
                                    self.loc(lid.loc),
                                )
                            }
                        };
                        let field_let_kind = if matches!(lbl.lbl_mut, TypeMutableFlag::Mutable) {
                            LetKind::StrictOpt
                        } else {
                            LetKind::Alias
                        };
                        if let PatternDesc::Tpat_var(id, _) = &inner_pat.pat_desc {
                            result = RawLambda::let_(field_let_kind, id.clone(), field, result);
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
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate() {
                    let field = RawLambda::prim(
                        Primitive::Parrayrefs,
                        vec![
                            RawLambda::var(tmp.clone()),
                            RawLambda::const_(Constant::int(idx as i32)),
                        ],
                        pat_loc,
                    );
                    result = self.bind_irrefutable_pattern_raw(item, field, result);
                }
                match wrap_tmp {
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(cstr.cstr_tag, ConstructorTag::CstrUnboxed) =>
            {
                if let Some(arg) = args.first() {
                    // OCaml compiler/ml/matching.ml:1249-1271 passes
                    // Cstr_unboxed payloads through as `(arg, Alias)`;
                    // record payload patterns are then decomposed by normal
                    // record matching at compiler/ml/matching.ml:1439-1454.
                    self.bind_irrefutable_pattern_raw(arg, scrut, body)
                } else {
                    body
                }
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(cstr.cstr_tag, ConstructorTag::CstrConstant(_))
                    && args.is_empty()
                    && cstr.cstr_consts == 1
                    && cstr.cstr_nonconsts == 0 =>
            {
                body
            }
            PatternDesc::Tpat_construct(_, cstr, args)
                if matches!(cstr.cstr_tag, ConstructorTag::CstrBlock(_))
                    && cstr.cstr_consts == 0
                    && cstr.cstr_nonconsts == 1 =>
            {
                // Single-constructor block type: bind fields directly from scrutinee
                let (scrut_id, wrap_let) = match &scrut {
                    RawLambda::Lvar(id) => (id.clone(), None),
                    _ => {
                        let id = self.fresh_ident("match");
                        (id.clone(), Some((id, scrut)))
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
                    self.loc(pat.pat_loc),
                );
                self.bind_irrefutable_pattern_raw(inner, payload, body)
            }
            _ => unreachable!("expected irrefutable pattern"),
        }
    }

    fn raw_simple_for_let(
        &mut self,
        pat: &Pattern,
        param: RawLambda,
        body: RawLambda,
    ) -> RawLambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => RawLambda::seq(param, body),
            PatternDesc::Tpat_var(id, _) => {
                RawLambda::let_(LetKind::Strict, id.clone(), param, body)
            }
            _ => match param {
                RawLambda::Lvar(_) => self.bind_irrefutable_pattern_raw(pat, param, body),
                _ => {
                    let match_id = self.fresh_ident("match");
                    let body = self.bind_irrefutable_pattern_raw(
                        pat,
                        RawLambda::var(match_id.clone()),
                        body,
                    );
                    RawLambda::let_(LetKind::Strict, match_id, param, body)
                }
            },
        }
    }

    fn bind_selected_tuple_pattern_raw(
        &mut self,
        scrut_id: &Ident,
        pat: &Pattern,
        body: RawLambda,
    ) -> Option<RawLambda> {
        let (inner, aliases) = peel_aliases(pat);
        let scrut = RawLambda::var(scrut_id.clone());
        let body = match &inner.pat_desc {
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_var(_, _)
            | PatternDesc::Tpat_tuple(_)
            | PatternDesc::Tpat_record(_, _)
            | PatternDesc::Tpat_array(_)
            | PatternDesc::Tpat_variant(_, Some(_), _) => {
                self.bind_irrefutable_pattern_raw(inner, scrut.clone(), body)
            }
            PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(_) if args.is_empty() => body,
                ConstructorTag::CstrBlock(_) if args.iter().all(Self::is_irrefutable_pattern) => {
                    self.bind_constructor_args_irrefutably_raw(scrut_id, inner, cstr, args, body)
                }
                ConstructorTag::CstrUnboxed => {
                    self.bind_irrefutable_pattern_raw(inner, scrut.clone(), body)
                }
                ConstructorTag::CstrExtension(_) => body,
                _ => return None,
            },
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_variant(_, None, _) => body,
            PatternDesc::Tpat_alias(_, _, _) | PatternDesc::Tpat_or(_, _, _) => return None,
        };
        Some(wrap_aliases_raw(&aliases, scrut, body))
    }

    fn raw_lambda_key(&self, lam: &RawLambda) -> String {
        format!("{}", crate::raw_lambda::print::RawLambdaPrinter::new(lam))
    }

    fn compile_simple_tuple_match(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<Lambda> {
        let expanded = Self::expand_tuple_cases(cases)?;
        let arity = expanded.first()?.items.len();
        if arity == 0 {
            return None;
        }

        let ids = (0..arity)
            .map(|idx| self.fresh_ident(&format!("match{idx}")))
            .collect::<Vec<_>>();
        let states = expanded
            .into_iter()
            .map(|case| TupleCaseState {
                case,
                selected: Vec::new(),
            })
            .collect::<Vec<_>>();
        let body = self.compile_simple_tuple_components(loc.clone(), &ids, &states, 0, partial)?;

        let result = match &scrut.exp_desc {
            ExpressionDesc::Texp_tuple(items) if items.len() == arity => items
                .iter()
                .zip(ids.iter())
                .rev()
                .fold(body, |acc, (item, id)| {
                    Lambda::let_(LetKind::Strict, id.clone(), self.convert_expr(item), acc)
                }),
            _ => {
                let tuple_id = self.fresh_ident("tuple");
                let tuple_var = Lambda::var(tuple_id.clone());
                let with_fields = ids.iter().enumerate().rev().fold(body, |acc, (idx, id)| {
                    let field = Lambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![tuple_var.clone()],
                        loc.clone(),
                    );
                    Lambda::let_(LetKind::Alias, id.clone(), field, acc)
                });
                Lambda::let_(
                    LetKind::Strict,
                    tuple_id,
                    self.convert_expr(scrut),
                    with_fields,
                )
            }
        };

        Some(result)
    }

    fn compile_simple_tuple_match_raw(
        &mut self,
        loc: Location,
        scrut: &Expression,
        cases: &[Case],
        partial: Partial,
    ) -> Option<RawLambda> {
        let expanded = Self::expand_tuple_cases(cases)?;
        let arity = expanded.first()?.items.len();
        if arity == 0 {
            return None;
        }

        let ids = (0..arity)
            .map(|_| self.fresh_ident("match"))
            .collect::<Vec<_>>();
        let states = expanded
            .into_iter()
            .map(|case| TupleCaseState {
                case,
                selected: Vec::new(),
            })
            .collect::<Vec<_>>();
        let body = self.compile_simple_tuple_components_raw(loc, &ids, &states, 0, partial)?;

        let result = match &scrut.exp_desc {
            ExpressionDesc::Texp_tuple(items) if items.len() == arity => items
                .iter()
                .zip(ids.iter())
                .rev()
                .fold(body, |acc, (item, id)| {
                    RawLambda::let_(
                        LetKind::Strict,
                        id.clone(),
                        self.convert_expr_raw(item),
                        acc,
                    )
                }),
            _ => {
                let tuple_id = self.fresh_ident("tuple");
                let tuple_var = RawLambda::var(tuple_id.clone());
                let with_fields = ids.iter().enumerate().rev().fold(body, |acc, (idx, id)| {
                    let field = RawLambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![tuple_var.clone()],
                        loc,
                    );
                    RawLambda::let_(LetKind::Alias, id.clone(), field, acc)
                });
                RawLambda::let_(
                    LetKind::Strict,
                    tuple_id,
                    self.convert_expr_raw(scrut),
                    with_fields,
                )
            }
        };

        Some(result)
    }

    fn compile_simple_tuple_components(
        &mut self,
        loc: Location,
        ids: &[Ident],
        states: &[TupleCaseState<'_>],
        idx: usize,
        partial: Partial,
    ) -> Option<Lambda> {
        if states.is_empty() {
            return Some(match partial {
                Partial::Partial => self.match_failure(loc),
                Partial::Total => Lambda::unit(),
            });
        }

        if idx >= ids.len() {
            let mut body = self.convert_expr(&states[0].case.case.c_rhs);
            for (pos, pat) in states[0].selected.iter().rev() {
                body = self.bind_selected_tuple_pattern(&ids[*pos], pat, body)?;
            }
            return Some(body);
        }

        let mut const_keys = Vec::new();
        let mut block_keys = Vec::new();
        let mut default_states = Vec::new();
        for state in states {
            let pat = state.case.items[idx];
            match Self::simple_switch_key(pat) {
                Some(key) => {
                    if key.is_block() {
                        if !block_keys.contains(&key) {
                            block_keys.push(key);
                        }
                    } else if !const_keys.contains(&key) {
                        const_keys.push(key);
                    }
                }
                None if Self::is_default_pattern(pat) => default_states.push(state.clone()),
                None => return None,
            }
        }

        if const_keys.is_empty() && block_keys.is_empty() {
            return self.compile_simple_tuple_components(
                loc,
                ids,
                &default_states,
                idx + 1,
                partial,
            );
        }

        let mut sw_consts = Vec::new();
        for key in const_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat)
                        || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch = self.compile_simple_tuple_components(
                loc.clone(),
                ids,
                &branch_states,
                idx + 1,
                partial,
            )?;
            sw_consts.push((key.tag(), branch));
        }

        let mut sw_blocks = Vec::new();
        for key in block_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat)
                        || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch = self.compile_simple_tuple_components(
                loc.clone(),
                ids,
                &branch_states,
                idx + 1,
                partial,
            )?;
            sw_blocks.push((key.tag(), branch));
        }

        let failaction = if default_states.is_empty() {
            match partial {
                Partial::Partial => Some(Box::new(self.match_failure(loc.clone()))),
                Partial::Total => None,
            }
        } else {
            Some(Box::new(self.compile_simple_tuple_components(
                loc.clone(),
                ids,
                &default_states,
                idx + 1,
                partial,
            )?))
        };

        Some(Lambda::Lswitch(
            Box::new(Lambda::var(ids[idx].clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts,
                sw_blocks_full: false,
                sw_blocks,
                sw_failaction: failaction,
                sw_names: None,
            },
        ))
    }

    fn compile_simple_tuple_components_raw(
        &mut self,
        loc: Location,
        ids: &[Ident],
        states: &[TupleCaseState<'_>],
        idx: usize,
        partial: Partial,
    ) -> Option<RawLambda> {
        if states.is_empty() {
            return Some(match partial {
                Partial::Partial => RawLambda::from_lowered(self.match_failure(loc)),
                Partial::Total => RawLambda::unit(),
            });
        }

        if idx >= ids.len() {
            let mut body = self.convert_expr_raw(&states[0].case.case.c_rhs);
            for (pos, pat) in states[0].selected.iter().rev() {
                body = self.bind_selected_tuple_pattern_raw(&ids[*pos], pat, body)?;
            }
            return Some(body);
        }

        let mut const_keys = Vec::new();
        let mut block_keys = Vec::new();
        let mut default_states = Vec::new();
        for state in states {
            let pat = state.case.items[idx];
            match Self::simple_switch_key(pat) {
                Some(key) => {
                    if key.is_block() {
                        if !block_keys.contains(&key) {
                            block_keys.push(key);
                        }
                    } else if !const_keys.contains(&key) {
                        const_keys.push(key);
                    }
                }
                None if Self::is_default_pattern(pat) => default_states.push(state.clone()),
                None => return None,
            }
        }

        if const_keys.is_empty() && block_keys.is_empty() {
            return self.compile_simple_tuple_components_raw(
                loc,
                ids,
                &default_states,
                idx + 1,
                partial,
            );
        }

        let mut sw_consts = Vec::new();
        for key in const_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat)
                        || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch = self.compile_simple_tuple_components_raw(
                loc,
                ids,
                &branch_states,
                idx + 1,
                partial,
            )?;
            sw_consts.push((key.tag(), branch));
        }

        let mut sw_blocks = Vec::new();
        for key in block_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat)
                        || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch = self.compile_simple_tuple_components_raw(
                loc,
                ids,
                &branch_states,
                idx + 1,
                partial,
            )?;
            sw_blocks.push((key.tag(), branch));
        }

        let failaction = if default_states.is_empty() {
            match partial {
                Partial::Partial => {
                    Some(Box::new(RawLambda::from_lowered(self.match_failure(loc))))
                }
                Partial::Total => None,
            }
        } else {
            Some(Box::new(self.compile_simple_tuple_components_raw(
                loc,
                ids,
                &default_states,
                idx + 1,
                partial,
            )?))
        };

        // OCaml's matching.ml sorts cases by tag via sort_int_lambda_list/split_cases
        sw_consts.sort_by_key(|(tag, _)| *tag);
        sw_blocks.sort_by_key(|(tag, _)| *tag);

        Some(RawLambda::Lswitch(
            Box::new(RawLambda::var(ids[idx].clone())),
            crate::raw_lambda::RawLambdaSwitch {
                sw_numconsts: sw_consts.len(),
                sw_consts_full: false,
                sw_consts,
                sw_numblocks: sw_blocks.len(),
                sw_blocks_full: false,
                sw_blocks,
                sw_failaction: failaction,
                sw_names: None,
            },
            Location::none(),
        ))
    }

    fn expand_tuple_cases<'b>(cases: &'b [Case]) -> Option<Vec<ExpandedTupleCase<'b>>> {
        let mut expanded = Vec::new();
        let mut arity = None;
        for case in cases {
            if case.c_guard.is_some() {
                return None;
            }
            for items in Self::expand_tuple_pattern(&case.c_lhs)? {
                let len = items.len();
                match arity {
                    Some(existing) if existing != len => return None,
                    None => arity = Some(len),
                    _ => {}
                }
                expanded.push(ExpandedTupleCase { case, items });
            }
        }
        Some(expanded)
    }

    fn expand_tuple_pattern<'b>(pat: &'b Pattern) -> Option<Vec<Vec<&'b Pattern>>> {
        let (pat, _) = peel_aliases(pat);
        match &pat.pat_desc {
            PatternDesc::Tpat_or(left, right, _) => {
                let mut out = Self::expand_tuple_pattern(left)?;
                out.extend(Self::expand_tuple_pattern(right)?);
                Some(out)
            }
            PatternDesc::Tpat_tuple(items) => Some(vec![items.iter().collect()]),
            _ => None,
        }
    }

    fn is_default_pattern(pat: &Pattern) -> bool {
        matches!(
            peel_aliases(pat).0.pat_desc,
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _)
        )
    }

    fn simple_switch_key(pat: &Pattern) -> Option<SimpleSwitchKey> {
        match &peel_aliases(pat).0.pat_desc {
            PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(tag) if args.is_empty() => {
                    Some(SimpleSwitchKey::ConstCtor(*tag))
                }
                ConstructorTag::CstrBlock(tag) if args.iter().all(Self::is_irrefutable_pattern) => {
                    Some(SimpleSwitchKey::BlockCtor(*tag))
                }
                _ => None,
            },
            PatternDesc::Tpat_constant(TConstant::Int(i)) => Some(SimpleSwitchKey::Int(*i as i32)),
            PatternDesc::Tpat_constant(TConstant::Char(c)) => Some(SimpleSwitchKey::Int(*c as i32)),
            _ => None,
        }
    }

    fn bind_selected_tuple_pattern(
        &mut self,
        scrut_id: &Ident,
        pat: &Pattern,
        body: Lambda,
    ) -> Option<Lambda> {
        let (inner, aliases) = peel_aliases(pat);
        let scrut = Lambda::var(scrut_id.clone());
        let body = match &inner.pat_desc {
            PatternDesc::Tpat_any => body,
            PatternDesc::Tpat_var(_, _)
            | PatternDesc::Tpat_tuple(_)
            | PatternDesc::Tpat_record(_, _)
            | PatternDesc::Tpat_array(_)
            | PatternDesc::Tpat_variant(_, Some(_), _) => {
                self.bind_irrefutable_pattern(inner, scrut.clone(), body)
            }
            PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrConstant(_) if args.is_empty() => body,
                ConstructorTag::CstrBlock(_) if args.iter().all(Self::is_irrefutable_pattern) => {
                    self.bind_constructor_args_irrefutably(scrut_id, inner, cstr, args, body)
                }
                ConstructorTag::CstrUnboxed => {
                    self.bind_irrefutable_pattern(inner, scrut.clone(), body)
                }
                ConstructorTag::CstrExtension(_) => body,
                _ => return None,
            },
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_variant(_, None, _) => body,
            PatternDesc::Tpat_alias(_, _, _) | PatternDesc::Tpat_or(_, _, _) => return None,
        };
        Some(wrap_aliases(&aliases, scrut, body))
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
                RecordLabelDefinition::OmittedOptionalNone(_, _) => lambda_optional_none(),
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
                                    name: label_runtime_name(lbl),
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
            .map(|(_, lbl, _, _)| (label_runtime_name(lbl), lbl.lbl_optional))
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

    fn translate_value_path(&self, loc_idx: LocIdx, path: &crate::types::Path) -> Lambda {
        if let Some(lam) = self.value_path_loc_constant(path, self.loc(loc_idx)) {
            return crate::raw_lambda::lower::lower_to_lambda(lam);
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

    fn convert_let_with_body_raw(
        &mut self,
        rec_flag: crate::parser::ast::RecFlag,
        bindings: &[ValueBinding],
        body: RawLambda,
    ) -> RawLambda {
        match rec_flag {
            crate::parser::ast::RecFlag::Nonrecursive => {
                if bindings.iter().any(|binding| {
                    simple_let_binding_id(binding).is_none()
                        && !Self::is_irrefutable_pattern(&binding.vb_pat)
                }) {
                    // Use OCaml's simple_for_let / for_let approach via full matching compiler
                    let converted_bindings = bindings
                        .iter()
                        .map(|binding| {
                            let mut value = self.convert_expr_raw(&binding.vb_expr);
                            let inline_attr =
                                self.get_inline_attribute_from(&binding.vb_attributes);
                            value =
                                self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
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
                            let pat_act_list = vec![(binding.vb_pat.clone(), acc)];
                            let loc = self.loc(binding.vb_pat.pat_loc);
                            let fname = self.basename_for_loc(loc.clone());
                            let loc_for_handler = loc.clone();
                            let handler_fun = move || {
                                let line = loc_for_handler.loc_start.line;
                                let char_pos = loc_for_handler.loc_start.column();
                                let match_failure_ident = predef_exception_ident(
                                    "Match_failure",
                                    PREDEF_MATCH_FAILURE_STAMP,
                                );
                                let exn = RawLambda::LglobalModule(match_failure_ident, false);
                                let payload = RawLambda::Lconst(Constant::Block {
                                    tag: 0,
                                    tag_info: TagInfo::Tuple,
                                    elements: vec![
                                        Constant::string_with_delim(
                                            fname.clone(),
                                            StringDelim::Plain,
                                        ),
                                        Constant::int(line),
                                        Constant::int(char_pos),
                                    ],
                                });
                                RawLambda::Lprim(RawPrimInfo {
                                    primitive: Primitive::Praise,
                                    args: vec![RawLambda::Lprim(RawPrimInfo {
                                        primitive: Primitive::Pmakeblock(
                                            0,
                                            TagInfo::Extension,
                                            Mutable::Immutable,
                                        ),
                                        args: vec![exn, payload],
                                        loc: Location::none(),
                                    })],
                                    loc: Location::none(),
                                })
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
                        let mut value = self.convert_expr_raw(&binding.vb_expr);
                        // OCaml's transl_let applies inline attributes from vb_attributes
                        let inline_attr = self.get_inline_attribute_from(&binding.vb_attributes);
                        value = self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
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
                    } else if Self::is_irrefutable_pattern(&binding.vb_pat) {
                        acc = full_matching::for_let(
                            self.type_ctx,
                            self.arena,
                            self.loc(binding.vb_pat.pat_loc),
                            value,
                            &binding.vb_pat,
                            acc,
                            &mut self.next_static_raise,
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
                            let mut value = self.convert_expr_raw(&binding.vb_expr);
                            let inline_attr =
                                self.get_inline_attribute_from(&binding.vb_attributes);
                            value =
                                self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                            (
                                simple_let_binding_id(binding).expect("checked above"),
                                value,
                            )
                        })
                        .collect();
                    RawLambda::letrec(lam_bindings, body)
                } else {
                    bindings.iter().rev().fold(body, |acc, binding| {
                        let mut value = self.convert_expr_raw(&binding.vb_expr);
                        let inline_attr = self.get_inline_attribute_from(&binding.vb_attributes);
                        value = self.apply_inline_attribute_raw(value, binding.vb_loc, inline_attr);
                        full_matching::for_let(
                            self.type_ctx,
                            self.arena,
                            self.loc(binding.vb_pat.pat_loc),
                            value,
                            &binding.vb_pat,
                            acc,
                            &mut self.next_static_raise,
                        )
                    })
                }
            }
        }
    }

    fn convert_function_raw(
        &mut self,
        params: &[FunctionParam],
        cases: &[Case],
        partial: Partial,
        arity: Arity,
        function_type: TypeExprRef,
        async_: bool,
        directive: Option<String>,
        inline: InlineAttribute,
        loc: Location,
    ) -> RawLambda {
        let (all_params, final_body, _partial) =
            self.flatten_function_by_arity(params, cases, partial, arity);

        let mut param_ids = Vec::new();
        for param in all_params.iter() {
            param_ids.push(param.param_id.clone());
        }

        let return_unit = final_body
            .map(|expr| self.is_base_type(expr.exp_type, "unit"))
            .unwrap_or(false);
        let mut body = final_body
            .map(|expr| self.convert_expr_raw(expr))
            .unwrap_or_else(RawLambda::unit);
        // OCaml's transl_function recurses into inner params first, then wraps
        // with Matching.for_function. Since for_function uses lower_bind which
        // pushes Alias bindings past existing ones, processing in REVERSE produces
        // the same order as OCaml's recursive approach.
        for (param, id) in all_params.iter().zip(param_ids.iter()).rev() {
            let pat = Self::param_pattern(param);
            body = match &pat.pat_desc {
                PatternDesc::Tpat_any => body,
                PatternDesc::Tpat_var(bound, _) if bound.same(id) => body,
                _ => {
                    // Use the matching compiler (for_function) to get lower_bind
                    // behavior that pushes field bindings into conditional branches.
                    let loc = self.loc(pat.pat_loc);
                    let pat_act = vec![(pat, body)];
                    full_matching::for_function(
                        self.type_ctx,
                        self.arena,
                        loc,
                        RawLambda::var(id.clone()),
                        pat_act,
                        Partial::Total,
                        &mut self.next_static_raise,
                    )
                }
            };
        }
        let lambda = RawLambda::function_(
            param_ids.len() as i32,
            param_ids,
            body,
            FunctionAttribute {
                return_unit,
                async_,
                directive,
                inline,
                ..FunctionAttribute::default()
            },
        );

        match self.arena.get_arity(arity) {
            Some(n) => {
                let prim = if let Some((lhs, _)) = self.is_nolabel_function_type(function_type) {
                    if self.is_base_type(lhs, "unit") {
                        Primitive::PjsFnMakeUnit
                    } else {
                        Primitive::PjsFnMake(n as i32)
                    }
                } else {
                    Primitive::PjsFnMake(n as i32)
                };
                RawLambda::prim(prim, vec![lambda], loc)
            }
            None => lambda,
        }
    }

    fn convert_single_case_function_raw_borrowed(
        &mut self,
        params: &[FunctionParam],
        case: &Case,
        partial: Partial,
        arity: Arity,
        function_type: TypeExprRef,
        async_: bool,
        directive: Option<String>,
        inline: InlineAttribute,
        loc: Location,
    ) -> Option<RawLambda> {
        if case.c_guard.is_some() {
            return None;
        }

        let target_arity = match self.arena.get_arity(arity) {
            Some(n) => n as usize,
            None => params.len(),
        };

        let mut all_params: Vec<&FunctionParam> = params.iter().collect();
        let mut current_case = case;
        let mut current_partial = partial;
        let mut pushed_bindings = Vec::new();
        let final_body = loop {
            let (rhs, pending_bindings) =
                self.strip_default_bindings_before_function(&current_case.c_rhs);
            let stripped_defaults = !pending_bindings.is_empty();
            Self::push_raw_function_binding_refs(&mut pushed_bindings, pending_bindings);

            if all_params.len() < target_arity {
                if let ExpressionDesc::Texp_function {
                    params: inner_params,
                    body: inner_cases,
                    partial: inner_partial,
                    arity: inner_arity,
                    async_: inner_async,
                } = &rhs.exp_desc
                {
                    let last_param = all_params.last()?;
                    let last_pat = Self::param_pattern(last_param);
                    if inner_cases.len() == 1
                        && inner_cases[0].c_guard.is_none()
                        // OCaml's transl_function flattens through nested function
                        // cases only when Parmatch.inactive succeeds and the inner
                        // function has no arity/async marker. See
                        // compiler/ml/translcore.ml:1048-1076.
                        && Self::parmatch_inactive(&last_pat, current_partial)
                        && self.arena.get_arity(*inner_arity).is_none()
                        && !inner_async
                    {
                        all_params.extend(inner_params.iter());
                        current_partial = *inner_partial;
                        current_case = &inner_cases[0];
                        continue;
                    }
                }
            }

            if stripped_defaults && matches!(rhs.exp_desc, ExpressionDesc::Texp_function { .. }) {
                return None;
            }

            break rhs;
        };

        if !pushed_bindings.is_empty()
            && matches!(final_body.exp_desc, ExpressionDesc::Texp_function { .. })
        {
            // OCaml's push_defaults keeps pushing saved default/module-pattern
            // bindings through nested function cases before transl_function
            // decides arity flattening. Falling back preserves that exact
            // placement for higher-order defaults. See
            // compiler/ml/translcore.ml:544-607 and 668-688.
            return None;
        }

        let mut param_ids = Vec::with_capacity(all_params.len());
        for param in all_params.iter() {
            param_ids.push(param.param_id.clone());
        }

        let return_unit = self.is_base_type(final_body.exp_type, "unit");
        let mut body = self.convert_expr_raw(final_body);
        // OCaml's push_defaults uses shallow record updates, so the huge body is
        // shared while default/module-pattern bindings are pushed under function
        // abstractions. Rust expression clones were deep-copying the body here;
        // keep a borrowed binding stack and wrap the converted lambda instead.
        // See compiler/ml/translcore.ml:544-589 and 668-688.
        body = self.wrap_raw_function_binding_refs(body, &pushed_bindings);

        for (param, id) in all_params.iter().zip(param_ids.iter()).rev() {
            let pat = Self::param_pattern(param);
            body = match &pat.pat_desc {
                PatternDesc::Tpat_any => body,
                PatternDesc::Tpat_var(bound, _) if bound.same(id) => body,
                _ => {
                    let loc = self.loc(pat.pat_loc);
                    let pat_act = vec![(pat, body)];
                    full_matching::for_function(
                        self.type_ctx,
                        self.arena,
                        loc,
                        RawLambda::var(id.clone()),
                        pat_act,
                        Partial::Total,
                        &mut self.next_static_raise,
                    )
                }
            };
        }
        let lambda = RawLambda::function_(
            param_ids.len() as i32,
            param_ids,
            body,
            FunctionAttribute {
                return_unit,
                async_,
                directive,
                inline,
                ..FunctionAttribute::default()
            },
        );

        match self.arena.get_arity(arity) {
            Some(n) => {
                let prim = if let Some((lhs, _)) = self.is_nolabel_function_type(function_type) {
                    if self.is_base_type(lhs, "unit") {
                        Primitive::PjsFnMakeUnit
                    } else {
                        Primitive::PjsFnMake(n as i32)
                    }
                } else {
                    Primitive::PjsFnMake(n as i32)
                };
                Some(RawLambda::prim(prim, vec![lambda], loc))
            }
            None => Some(lambda),
        }
    }

    fn convert_apply_raw(
        &mut self,
        loc_idx: LocIdx,
        loc: Location,
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
                            [] => self.raw_loc_constant(kind, loc),
                            [arg] => {
                                let expr = arg.expression.as_ref().expect("checked above");
                                RawLambda::prim(
                                    Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                                    vec![
                                        self.raw_loc_constant(kind, self.loc(expr.exp_loc)),
                                        self.convert_expr_raw(expr),
                                    ],
                                    loc,
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
                    let primitive = self.translate_primitive_application_raw(
                        prim,
                        funct.exp_type,
                        &applied_exprs,
                        transformed_jsx,
                        loc.clone(),
                    );
                    let primitive_is_import = matches!(primitive, Primitive::Pimport);
                    let arg_lams = applied_exprs
                        .iter()
                        .map(|expr| {
                            self.convert_expr_raw_with_dynamic_import(expr, primitive_is_import)
                        })
                        .collect::<Vec<_>>();
                    self.report_polymorphic_comparison_warning(loc_idx, &primitive, &arg_lams);
                    let base = RawLambda::prim(primitive.clone(), arg_lams, loc);
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

    fn convert_let_with_body(
        &mut self,
        rec_flag: crate::parser::ast::RecFlag,
        bindings: &[ValueBinding],
        body: Lambda,
    ) -> Lambda {
        match rec_flag {
            crate::parser::ast::RecFlag::Nonrecursive => {
                if bindings
                    .iter()
                    .all(|binding| simple_let_binding_id(binding).is_some())
                {
                    bindings.iter().rev().fold(body, |acc, binding| {
                        let id = simple_let_binding_id(binding).expect("checked above");
                        let value = self.convert_expr(&binding.vb_expr);
                        Lambda::let_(LetKind::Strict, id, value, acc)
                    })
                } else {
                    let raw = self.convert_let_with_body_raw(
                        rec_flag,
                        bindings,
                        RawLambda::from_lowered(body),
                    );
                    let start_stamp = self.current_stamp();
                    crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(raw, start_stamp)
                }
            }
            crate::parser::ast::RecFlag::Recursive => {
                if bindings
                    .iter()
                    .all(|binding| simple_let_binding_id(binding).is_some())
                {
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
                    let raw = self.convert_let_with_body_raw(
                        rec_flag,
                        bindings,
                        RawLambda::from_lowered(body),
                    );
                    let start_stamp = self.current_stamp();
                    crate::raw_lambda::lower::lower_to_lambda_with_start_stamp(raw, start_stamp)
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
                PatternDesc::Tpat_alias(_, id, _) => id.clone(),
                _ => self.fresh_ident(&format!("param{idx}")),
            };
            param_ids.push(id);
        }

        let body = final_body
            .map(|expr| self.convert_expr(expr))
            .unwrap_or_else(Lambda::unit);
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

    /// OCaml's Parmatch.inactive: checks if a pattern has no mutable field access.
    /// Returns false for Partial, or if the pattern accesses any mutable record fields.
    fn parmatch_inactive(pat: &Pattern, partial: Partial) -> bool {
        match partial {
            Partial::Partial => false,
            Partial::Total => Self::pattern_inactive(pat),
        }
    }

    fn pattern_inactive(pat: &Pattern) -> bool {
        match &pat.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(_, _) => true,
            PatternDesc::Tpat_constant(_) => true,
            PatternDesc::Tpat_tuple(ps) | PatternDesc::Tpat_construct(_, _, ps) => {
                ps.iter().all(|p| Self::pattern_inactive(p))
            }
            PatternDesc::Tpat_alias(p, _, _) => Self::pattern_inactive(p),
            PatternDesc::Tpat_variant(_, None, _) => true,
            PatternDesc::Tpat_variant(_, Some(p), _) => Self::pattern_inactive(p),
            PatternDesc::Tpat_record(fields, _) => fields.iter().all(|(_, lbl, p, _)| {
                lbl.lbl_mut == crate::types::asttypes::MutableFlag::Immutable
                    && Self::pattern_inactive(p)
            }),
            PatternDesc::Tpat_or(p, q, _) => Self::pattern_inactive(p) && Self::pattern_inactive(q),
            PatternDesc::Tpat_array(_) => false,
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
            return (
                params.iter().collect(),
                cases.first().map(|case| &case.c_rhs),
                partial,
            );
        }

        let mut all_params: Vec<&'b FunctionParam> = params.iter().collect();
        let mut current_partial = partial;
        let mut current_body = &cases[0].c_rhs;

        while all_params.len() < target_arity {
            // OCaml checks Parmatch.inactive on the current level's pattern
            // before flattening into the inner function (translcore.ml line 1061)
            let last_param = all_params.last().unwrap();
            let last_pat = Self::param_pattern(last_param);
            if !Self::parmatch_inactive(&last_pat, current_partial) {
                break;
            }

            match &current_body.exp_desc {
                ExpressionDesc::Texp_function {
                    params: inner_params,
                    body: inner_cases,
                    partial: inner_partial,
                    arity: inner_arity,
                    async_: inner_async,
                } if inner_cases.len() == 1
                    && inner_cases[0].c_guard.is_none()
                    // OCaml's transl_function only flattens when inner arity is None
                    // and the inner function is not async (matching lines 1053, 1061)
                    && self.arena.get_arity(*inner_arity).is_none()
                    && !inner_async =>
                {
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
                    let prim_args = applied_exprs
                        .iter()
                        .map(|expr| self.convert_expr(expr))
                        .collect::<Vec<_>>();
                    let prim =
                        self.translate_primitive_application(prim, loc.clone(), transformed_jsx);
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
                    let protect =
                        |conv: &mut RawLambdaConverter<'_>,
                         name: &str,
                         lam: Lambda,
                         defs: &mut Vec<(Ident, Lambda)>| {
                            if is_simple(&lam) {
                                lam
                            } else {
                                let id = conv.fresh_ident(name);
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
                                arg.as_ref()
                                    .map(|lam| protect(conv, "arg", lam.clone(), &mut defs)),
                                *is_optional,
                            )
                        })
                        .collect::<Vec<_>>();
                    let id_arg = conv.fresh_ident("param");
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
                        lam => {
                            Lambda::function_(1, vec![id_arg], lam, FunctionAttribute::default())
                        }
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
                    arg.expression.as_ref().map(|expr| self.convert_expr(expr)),
                    arg.label.is_optional(),
                )
            })
            .collect::<Vec<_>>();
        build_apply(self, lam, Vec::new(), &pending, loc, transformed_jsx)
    }

    fn transl_apply_raw(
        &mut self,
        lam: RawLambda,
        sargs: &[ApplyArg],
        loc: Location,
        transformed_jsx: bool,
        uncurried_partial_application: Option<i32>,
        inlined: InlineAttribute,
    ) -> RawLambda {
        fn lapply(
            loc: Location,
            func: RawLambda,
            args: Vec<RawLambda>,
            transformed_jsx: bool,
            inlined: InlineAttribute,
        ) -> RawLambda {
            RawLambda::Lapply(crate::raw_lambda::RawApply {
                ap_func: Box::new(func),
                ap_args: args,
                ap_info: ApInfo {
                    loc,
                    inlined,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: transformed_jsx,
            })
        }

        fn is_simple(lam: &RawLambda) -> bool {
            matches!(lam, RawLambda::Lvar(_) | RawLambda::Lconst(_))
        }

        fn build_apply(
            conv: &mut RawLambdaConverter<'_>,
            lam: RawLambda,
            mut args_rev: Vec<(RawLambda, bool)>,
            pending: &[(Option<RawLambda>, bool)],
            loc: Location,
            transformed_jsx: bool,
            inlined: InlineAttribute,
        ) -> RawLambda {
            match pending.split_first() {
                Some(((None, optional), tail)) => {
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
                                defs.push((id.clone(), lam));
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
                    let protected_tail = tail
                        .iter()
                        .map(|(arg, is_optional)| {
                            (
                                arg.as_ref()
                                    .map(|lam| protect(conv, "arg", lam.clone(), &mut defs)),
                                *is_optional,
                            )
                        })
                        .collect::<Vec<_>>();
                    let id_arg = conv.fresh_ident("param");
                    let mut next_args_rev = Vec::with_capacity(1 + remaining_args.len());
                    next_args_rev.push((RawLambda::var(id_arg.clone()), *optional));
                    next_args_rev.extend(remaining_args);
                    let body = match build_apply(
                        conv,
                        handle,
                        next_args_rev,
                        &protected_tail,
                        loc,
                        transformed_jsx,
                        inlined,
                    ) {
                        RawLambda::Lfunction(func) => {
                            RawLambda::Lfunction(crate::raw_lambda::RawLFunction {
                                arity: func.arity + 1,
                                params: std::iter::once(id_arg).chain(func.params).collect(),
                                body: func.body,
                                attr: func.attr,
                            })
                        }
                        lam => {
                            RawLambda::function_(1, vec![id_arg], lam, FunctionAttribute::default())
                        }
                    };
                    defs.into_iter().fold(body, |body, (id, lam)| {
                        RawLambda::let_(LetKind::Strict, id, lam, body)
                    })
                }
                Some(((Some(arg), optional), tail)) => {
                    args_rev.insert(0, (arg.clone(), *optional));
                    build_apply(conv, lam, args_rev, tail, loc, transformed_jsx, inlined)
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
                    .filter_map(|arg| match &arg.expression {
                        Some(expr) => Some(self.convert_expr_raw(expr)),
                        None => {
                            let id = self.fresh_ident("none");
                            none_ids.push(id.clone());
                            Some(RawLambda::var(id))
                        }
                    })
                    .collect::<Vec<_>>();
                let extra_ids = (0..extra_arity)
                    .map(|_| self.fresh_ident("extra"))
                    .collect::<Vec<_>>();
                let mut ap_args = args;
                ap_args.extend(extra_ids.iter().cloned().map(RawLambda::var));
                let body = lapply(loc.clone(), lam, ap_args, transformed_jsx, inlined);
                RawLambda::function_(
                    (none_ids.len() + extra_ids.len()) as i32,
                    none_ids.into_iter().chain(extra_ids).collect(),
                    body,
                    FunctionAttribute::default(),
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
                    &pending,
                    loc,
                    transformed_jsx,
                    inlined,
                )
            }
        }
    }

    fn translate_primitive_raw(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
    ) -> RawLambda {
        self.translate_primitive_raw_in_env(loc, prim, ty, self.env)
    }

    fn translate_primitive_raw_in_env(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        env: &crate::types::env::Env,
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
                        vec![param.clone()],
                        RawLambda::prim(
                            Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                            vec![lam, RawLambda::var(param)],
                            loc,
                        ),
                        FunctionAttribute::default(),
                    )
                }
                _ => RawLambda::unit(),
            };
        }
        if raw_name == "%null" && prim.prim_arity == 0 {
            // OCaml uses Lprim(Pnull, []), not Lconst(JsNull)
            return RawLambda::prim(Primitive::Pnull, vec![], loc);
        }
        if raw_name == "%undefined" && prim.prim_arity == 0 {
            // OCaml uses Lprim(Pundefined, []), not Lconst(JsUndefined)
            return RawLambda::prim(Primitive::Pundefined, vec![], loc);
        }
        let primitive =
            if let Some(primitive) = self.specialize_primitive_raw_with_env(prim, ty, env) {
                primitive
            } else {
                self.report_unknown_builtin_primitive(loc.clone(), raw_name);
                Primitive::PjsCall {
                    prim_name: raw_name.to_string(),
                    arg_types: decoded_external_arg_types(
                        &prim.prim_native_name,
                        prim.prim_arity.max(0) as usize,
                    ),
                    ffi: self.ffi_spec_for_primitive(
                        prim,
                        self.applied_result_is_builtin_object(ty, prim.prim_arity.max(0) as usize),
                        self.applied_result_is_unit(ty, prim.prim_arity.max(0) as usize),
                    ),
                    dynamic_import: false,
                    transformed_jsx: false,
                }
            };

        if prim.prim_from_constructor || prim.prim_arity == 0 {
            RawLambda::prim(primitive, vec![], loc)
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
            RawLambda::function_(
                prim.prim_arity,
                params,
                RawLambda::prim(primitive, args, loc),
                FunctionAttribute::default(),
            )
        }
    }

    fn translate_primitive(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
    ) -> Lambda {
        let raw_name = Self::raw_primitive_name(&prim.prim_name);
        if raw_name == "%null" && prim.prim_arity == 0 {
            return Lambda::const_(Constant::JsNull);
        }
        if raw_name == "%undefined" && prim.prim_arity == 0 {
            return Lambda::const_(Constant::JsUndefined { is_unit: false });
        }
        let primitive = self.translate_primitive_application(prim, loc.clone(), false);
        if prim.prim_arity == 0 {
            Lambda::prim(primitive, vec![], loc)
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
        &mut self,
        prim: &crate::types::PrimitiveDescription,
        loc: Location,
        transformed_jsx: bool,
    ) -> Primitive {
        let raw_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some(primitive) = self.find_raw_primitive(raw_name) {
            primitive
        } else {
            self.report_unknown_builtin_primitive(loc, raw_name);
            Primitive::PjsCall {
                prim_name: raw_name.to_string(),
                arg_types: decoded_external_arg_types(
                    &prim.prim_native_name,
                    prim.prim_arity.max(0) as usize,
                ),
                ffi: self.ffi_spec_for_primitive(prim, false, false),
                dynamic_import: false,
                transformed_jsx,
            }
        }
    }

    fn raw_primitive_name(name: &str) -> &str {
        name.strip_suffix("[js]").unwrap_or(name)
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

fn ffi_marshaled_inline_constant(value: &OcamlValue) -> Option<Constant> {
    let (tag, fields) = value.as_block_opt()?;
    if tag != 2 || fields.len() != 1 {
        return None;
    }
    ffi_marshaled_constant(&fields[0])
}

fn ffi_marshaled_constant(value: &OcamlValue) -> Option<Constant> {
    match value {
        OcamlValue::Int(0) => Some(Constant::JsNull),
        OcamlValue::Int(1) => Some(Constant::JsTrue),
        OcamlValue::Int(2) => Some(Constant::JsFalse),
        OcamlValue::Int(3) => Some(Constant::ModuleAlias),
        OcamlValue::Block(0, fields) if fields.len() == 1 => Some(Constant::JsUndefined {
            is_unit: fields[0].as_bool(),
        }),
        OcamlValue::Block(1, fields) if fields.len() == 2 => Some(Constant::Int {
            i: fields[0].as_int() as i32,
            comment: ffi_marshaled_pointer_info(&fields[1]),
        }),
        OcamlValue::Block(2, fields) if fields.len() == 1 => {
            Some(Constant::Char(fields[0].as_int() as i32))
        }
        OcamlValue::Block(3, fields) if fields.len() == 2 => Some(Constant::String {
            s: fields[0].as_string().to_string(),
            delim: ffi_marshaled_optional_delim(&fields[1]),
        }),
        OcamlValue::Block(4, fields) if fields.len() == 1 => {
            Some(Constant::Float(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(5, fields) if fields.len() == 2 => Some(Constant::BigInt {
            negative: fields[0].as_bool(),
            value: fields[1].as_string().to_string(),
        }),
        OcamlValue::Block(6, fields) if fields.len() == 1 => {
            Some(Constant::Pointer(fields[0].as_string().to_string()))
        }
        OcamlValue::Block(8, fields) if fields.len() == 1 => Some(Constant::Some(Box::new(
            ffi_marshaled_constant(&fields[0])?,
        ))),
        _ => None,
    }
}

fn ffi_marshaled_pointer_info(value: &OcamlValue) -> Option<PointerInfo> {
    match value {
        OcamlValue::Int(0) => None,
        OcamlValue::Int(1) => Some(PointerInfo::AssertFalse),
        OcamlValue::Block(0, fields) if fields.len() == 1 => {
            let (tag, fields) = fields[0].as_block_opt()?;
            if tag != 0 || fields.len() != 3 {
                return None;
            }
            Some(PointerInfo::Constructor(PointerConstructorTag {
                name: fields[0].as_block_opt()?.1.first()?.as_string().to_string(),
                const_: fields[1].as_int() as i32,
                non_const: fields[2].as_int() as i32,
                runtime_tag: None,
            }))
        }
        OcamlValue::Block(1, fields) if fields.len() == 1 => {
            Some(PointerInfo::Some(fields[0].as_string().to_string()))
        }
        _ => None,
    }
}

fn ffi_marshaled_optional_delim(value: &OcamlValue) -> Option<StringDelim> {
    match value {
        OcamlValue::Int(0) => None,
        OcamlValue::Block(0, fields) if fields.len() == 1 => ffi_marshaled_delim(&fields[0]),
        _ => None,
    }
}

fn ffi_marshaled_delim(value: &OcamlValue) -> Option<StringDelim> {
    match value.as_int() {
        0 => Some(StringDelim::Plain),
        1 => Some(StringDelim::StarJ),
        2 => Some(StringDelim::NoQuotes),
        3 => Some(StringDelim::Backtick),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

    use crate::binary_ast::ffi_types::{
        Delim, ExternalSpec, FfiType, LamConstant, ReturnWrapper, encode_ffi_type,
    };
    use crate::binary_ast::ppx;
    use crate::context::IdGenerator;
    use crate::parse_arena::ParseArena;
    use crate::parser::Parser;
    use crate::parser::ast::Attributes;
    use crate::parser::module;
    use crate::types::env::initial_env;

    #[test]
    fn raw_polyvariant_compare_keeps_named_tag_metadata() {
        let scrutinee_id = Ident::create_local("value");
        let comparison = raw_polyvariant_compare(
            RawLambda::var(scrutinee_id.clone()),
            "InvalidNext",
            Location::none(),
        );

        let RawLambda::Lprim(info) = comparison else {
            panic!("expected primitive comparison");
        };

        assert!(matches!(info.primitive, Primitive::Pjscomp(Comparison::Eq)));
        assert!(
            matches!(info.args.as_slice(), [RawLambda::Lvar(id), RawLambda::Lconst(Constant::Int { i, comment: Some(PointerInfo::PolyVariant(name)) })]
            if id.same(&scrutinee_id)
                && *i == crate::types::btype::hash_variant("InvalidNext")
                && name == "InvalidNext")
        );
    }

    #[test]
    fn nullary_unboxed_constructor_keeps_constructor_metadata_in_raw_lambda() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);

        let cstr = crate::types::ConstructorDescription {
            cstr_name: "OnlyOne".to_string(),
            cstr_res: crate::types::TypeExprRef(0),
            cstr_existentials: Vec::new(),
            cstr_args: Vec::new(),
            cstr_arity: 0,
            cstr_tag: crate::types::ConstructorTag::CstrUnboxed,
            cstr_consts: 1,
            cstr_nonconsts: 0,
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: Location::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: None,
        };

        let lowered = converter.convert_construct_raw(Location::none(), EnvRef(0), &cstr, &[]);

        assert!(matches!(
            lowered,
            RawLambda::Lconst(Constant::Int {
                i: 0,
                comment: Some(PointerInfo::Constructor(PointerConstructorTag {
                    name,
                    const_,
                    non_const,
                    runtime_tag: None,
                })),
            }) if name == "OnlyOne" && const_ == 1 && non_const == 0
        ));
    }

    #[test]
    fn empty_inlined_record_constructor_keeps_inlined_record_metadata() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);

        let arg = Expression::new(
            ExpressionDesc::Texp_record {
                fields: vec![],
                extended_expression: None,
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
            cstr_tag: crate::types::ConstructorTag::CstrBlock(0),
            cstr_consts: 1,
            cstr_nonconsts: 1,
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: Location::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: Some(Box::new(crate::types::TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: crate::types::decl::TypeKind::TypeRecord(
                    vec![],
                    crate::types::decl::RecordRepresentation::RecordInlined {
                        tag: 0,
                        name: "B".to_string(),
                        num_nonconsts: 1,
                        attrs: vec![],
                    },
                ),
                type_private: crate::types::asttypes::PrivateFlag::Public,
                type_manifest: None,
                type_variance: vec![],
                type_newtype_level: None,
                type_loc: Location::none(),
                type_attributes: vec![],
                type_immediate: false,
                type_unboxed: crate::types::decl::UnboxedStatus::default(),
                type_inlined_types: vec![],
                type_path: None,
            })),
        };

        let lowered = converter.convert_construct_raw(Location::none(), EnvRef(0), &cstr, &[arg]);

        assert!(matches!(
            lowered,
            RawLambda::Lconst(Constant::Block {
                tag: 0,
                tag_info:
                    TagInfo::RecordInlined {
                        name,
                        num_nonconst,
                        tag: 0,
                        fields,
                        mutable_flag: ParserMutableFlag::Immutable,
                        ..
                    },
                elements,
            }) if name == "B" && num_nonconst == 1 && fields.is_empty() && elements.is_empty()
        ));
    }

    fn else_exit_id(raw: &RawLambda) -> Option<i32> {
        let RawLambda::Llet(_, _, _, body) = raw else {
            return None;
        };
        let RawLambda::LifThenElse(_, _, else_) = body.as_ref() else {
            return None;
        };
        let RawLambda::LstaticRaise(id, args) = else_.as_ref() else {
            return None;
        };
        if args.is_empty() { Some(*id) } else { None }
    }

    fn try_handler_exit_id(raw: &RawLambda) -> Option<i32> {
        let RawLambda::LtryWith(_, _, handler) = raw else {
            return None;
        };
        let RawLambda::LstaticCatch(_, (id, params), _) = handler.as_ref() else {
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
        let path = crate::types::Path::Pident(Ident::create_persistent(name));
        let constructor = crate::types::ConstructorDescription {
            cstr_name: name.to_string(),
            cstr_res: crate::types::TypeExprRef(0),
            cstr_existentials: Vec::new(),
            cstr_args: Vec::new(),
            cstr_arity: 0,
            cstr_tag: crate::types::ConstructorTag::CstrExtension(path),
            cstr_consts: -1,
            cstr_nonconsts: -1,
            cstr_generalized: false,
            cstr_private: crate::types::asttypes::PrivateFlag::Public,
            cstr_loc: Location::none(),
            cstr_attributes: Vec::new(),
            cstr_inlined: None,
        };
        let case = Case::simple(
            Pattern::new(
                PatternDesc::Tpat_construct(lid, constructor, Vec::new()),
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
                PatternDesc::Tpat_var(id.clone(), Located::mknoloc(id.name().to_string())),
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

        let directive_expr = crate::parser::ast::Expression {
            pexp_desc: Box::new(crate::parser::ast::ExpressionDesc::Pexp_constant(Box::new(
                crate::parser::ast::Constant::String(Cow::Owned("'use memo'".to_string()), None),
            ))),
            pexp_loc: LocIdx::none(),
            pexp_attributes: Attributes::new(),
        };
        let directive_expr_idx = arena.push_expr(directive_expr);
        let directive_attrs = Attributes::from_vec(vec![(
            Located::mknoloc(arena.intern_string("directive")),
            crate::parser::ast::Payload::PStr(Box::new(vec![crate::parser::ast::StructureItem {
                pstr_desc: Box::new(crate::parser::ast::StructureItemDesc::Pstr_eval(Box::new(
                    (directive_expr_idx, Attributes::new()),
                ))),
                pstr_loc: LocIdx::none(),
            }])),
        )]);

        let param_id = Ident::create_local("name");
        let param_pat = Pattern::new(
            PatternDesc::Tpat_var(param_id.clone(), Located::mknoloc("name".to_string())),
            LocIdx::none(),
            crate::types::TypeExprRef(0),
            EnvRef(0),
            Attributes::new(),
        );
        let expr = Expression::new(
            ExpressionDesc::Texp_function {
                params: vec![FunctionParam {
                    param_id: param_id.clone(),
                    label: crate::parser::ast::ArgLabel::Nolabel,
                    default: None,
                    pat: FunctionParamPattern::Simple(param_pat.clone()),
                }],
                body: vec![Case::simple(
                    param_pat,
                    Expression::new(
                        ExpressionDesc::Texp_constant(TConstant::Int(1)),
                        LocIdx::none(),
                        crate::types::TypeExprRef(0),
                        EnvRef(0),
                        Attributes::new(),
                    ),
                )],
                partial: Partial::Total,
                arity: arena.push_arity(None),
                async_: false,
            },
            LocIdx::none(),
            crate::types::TypeExprRef(0),
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
    fn simple_trywith_extension_handler_assigns_exit_ids_in_source_order() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        converter.next_static_raise = 1;
        let exn_id = Ident::create_local("exn");

        let handler = converter.build_simple_trywith_extension_chain_raw(
            Location::none(),
            &exn_id,
            vec![
                (
                    crate::types::Path::Pident(Ident::create_persistent("A")),
                    RawLambda::const_(Constant::int(1)),
                ),
                (
                    crate::types::Path::Pident(Ident::create_persistent("B")),
                    RawLambda::const_(Constant::int(2)),
                ),
                (
                    crate::types::Path::Pident(Ident::create_persistent("C")),
                    RawLambda::const_(Constant::int(3)),
                ),
            ],
            RawLambda::LstaticRaise(1, Vec::new()),
        );

        let RawLambda::LstaticCatch(first_case, (first_handler, first_params), rest) = handler
        else {
            panic!("expected outer static catch");
        };
        assert_eq!(first_handler, 3);
        assert!(first_params.is_empty());
        assert_eq!(else_exit_id(&first_case), Some(3));

        let RawLambda::LstaticCatch(second_case, (second_handler, second_params), last_case) =
            *rest
        else {
            panic!("expected second static catch");
        };
        assert_eq!(second_handler, 2);
        assert!(second_params.is_empty());
        assert_eq!(else_exit_id(&second_case), Some(2));
        assert_eq!(else_exit_id(&last_case), Some(1));
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
            simple_value_binding(
                first_id.clone(),
                simple_extension_try(&mut arena, "A", 1, 11),
            ),
            simple_value_binding(
                second_id.clone(),
                simple_extension_try(&mut arena, "B", 2, 22),
            ),
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

    #[test]
    fn ffi_spec_reads_null_to_opt_return_wrapper() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "get".to_string(),
            prim_arity: 1,
            prim_native_name: encode_ffi_type(&FfiType::FfiBs {
                params: crate::binary_ast::ffi_types::Params::ParamNumber(1),
                return_wrapper: ReturnWrapper::ReturnNullToOpt,
                external_spec: ExternalSpec::JsGet {
                    js_get_name: "x".to_string(),
                    js_get_scopes: Vec::new(),
                },
            }),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert_eq!(spec.return_wrapper, ExternalReturnWrapper::NullToOpt);
    }

    #[test]
    fn ffi_spec_preserves_marshaled_js_var_shape() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "process".to_string(),
            prim_arity: 0,
            prim_native_name: encode_ffi_type(&FfiType::FfiBs {
                params: crate::binary_ast::ffi_types::Params::ParamNumber(0),
                return_wrapper: ReturnWrapper::ReturnIdentity,
                external_spec: ExternalSpec::JsVar {
                    name: "process".to_string(),
                    external_module_name: None,
                    scopes: Vec::new(),
                },
            }),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert!(matches!(
            spec.spec,
            Some(crate::lambda::lam_primitive::ExternalSpec::JsVar {
                ref name,
                external_module_name: None,
                ref scopes,
            }) if name == "process" && scopes.is_empty()
        ));
    }

    #[test]
    fn ffi_spec_preserves_marshaled_import_attributes() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "default".to_string(),
            prim_arity: 0,
            prim_native_name: encode_ffi_type(&FfiType::FfiBs {
                params: crate::binary_ast::ffi_types::Params::ParamNumber(0),
                return_wrapper: ReturnWrapper::ReturnIdentity,
                external_spec: ExternalSpec::JsModuleAsVar(
                    crate::binary_ast::ffi_types::ExternalModuleName {
                        bundle: "./myJson.json".to_string(),
                        module_bind_name:
                            crate::binary_ast::ffi_types::ModuleBindName::PhintNothing,
                        import_attributes: Some(vec![
                            ("type".to_string(), "json".to_string()),
                            ("some-identifier".to_string(), "yep".to_string()),
                        ]),
                    },
                ),
            }),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert!(matches!(
            spec.spec,
            Some(crate::lambda::lam_primitive::ExternalSpec::JsModuleAsVar(
                crate::lambda::lam_primitive::ExternalModuleName {
                    ref bundle,
                    import_attributes: Some(ref attrs),
                    ..
                }
            )) if bundle == "./myJson.json"
                && attrs == &vec![
                    ("type".to_string(), "json".to_string()),
                    ("some-identifier".to_string(), "yep".to_string()),
                ]
        ));
    }

    #[test]
    fn ffi_spec_preserves_import_attributes_from_rewritten_external() {
        let source = r#"
@module({from: "./myJson.json", with: {type_: "json", \"some-identifier": "yep"}})
external myJson: Js.Json.t = "default"
"#;
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(
            !parser.has_errors(),
            "parse errors: {:?}",
            parser.take_diagnostics()
        );

        let primitive = structure
            .iter()
            .find_map(|item| match &*item.pstr_desc {
                crate::parser::ast::StructureItemDesc::Pstr_primitive(vd) => Some(vd),
                _ => None,
            })
            .expect("expected parsed external primitive");
        let encoded = ppx::encode_external(primitive, parser.arena_mut());
        let prim_name = parser.arena().get_string(encoded.pval_prim[0]).to_string();
        let encoded = parser.arena().get_string(encoded.pval_prim[1]).to_string();

        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(parser.arena(), &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name,
            prim_arity: 0,
            prim_native_name: encoded,
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        let module_name = match spec.spec {
            Some(crate::lambda::lam_primitive::ExternalSpec::JsModuleAsVar(module_name)) => {
                module_name
            }
            Some(crate::lambda::lam_primitive::ExternalSpec::JsVar {
                external_module_name: Some(module_name),
                ..
            }) => module_name,
            other => panic!("expected module import metadata, got {other:?}"),
        };
        assert_eq!(module_name.bundle, "./myJson.json");
        assert_eq!(
            module_name.import_attributes,
            Some(vec![
                ("type".to_string(), "json".to_string()),
                ("some-identifier".to_string(), "yep".to_string()),
            ])
        );
    }

    #[test]
    fn ffi_spec_preserves_marshaled_js_new_shape() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "URL".to_string(),
            prim_arity: 1,
            prim_native_name: encode_ffi_type(&FfiType::FfiBs {
                params: crate::binary_ast::ffi_types::Params::ParamNumber(1),
                return_wrapper: ReturnWrapper::ReturnIdentity,
                external_spec: ExternalSpec::JsNew {
                    name: "URL".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: Vec::new(),
                },
            }),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert!(matches!(
            spec.spec,
            Some(crate::lambda::lam_primitive::ExternalSpec::JsNew {
                ref name,
                external_module_name: None,
                splice: false,
                ref scopes,
            }) if name == "URL" && scopes.is_empty()
        ));
    }

    #[test]
    fn ffi_spec_reads_marshaled_object_create_kind() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: String::new(),
            prim_arity: 1,
            prim_native_name: encode_ffi_type(&FfiType::FfiObjCreate(Vec::new())),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert_eq!(spec.kind, ExternalFfiKind::ObjCreate);
    }

    #[test]
    fn ffi_spec_reads_marshaled_inline_string_constant() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: String::new(),
            prim_arity: 0,
            prim_native_name: encode_ffi_type(&FfiType::FfiInlineConst(LamConstant::ConstString {
                s: "hello".to_string(),
                delim: Some(Delim::DStarJ),
            })),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert_eq!(
            spec.inline_constant,
            Some(Constant::String {
                s: "hello".to_string(),
                delim: Some(StringDelim::StarJ),
            })
        );
    }

    #[test]
    fn ffi_spec_reads_marshaled_inline_int_constant() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: String::new(),
            prim_arity: 0,
            prim_native_name: encode_ffi_type(&FfiType::FfiInlineConst(LamConstant::ConstInt {
                i: 1,
                comment: crate::binary_ast::ffi_types::PointerInfo::None,
            })),
            prim_native_float: false,
            prim_from_constructor: false,
        };

        let spec = converter.ffi_spec_for_primitive(&prim, false, false);
        assert_eq!(
            spec.inline_constant,
            Some(Constant::Int {
                i: 1,
                comment: None,
            })
        );
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
            type_loc: Location::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_unboxed: crate::types::decl::UnboxedStatus::default(),
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
        env.add_type(alias_id.clone(), type_alias_decl(compare_ty));

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "%compare".to_string(),
            prim_arity: 2,
            prim_native_name: String::new(),
            prim_native_float: false,
            prim_from_constructor: false,
        };
        let alias_ty = ctx.new_constr(crate::types::Path::Pident(alias_id), vec![]);

        let primitive = primitive_wrapper_body_primitive(converter.translate_primitive_raw_in_env(
            Location::none(),
            &prim,
            alias_ty,
            &env,
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
            original_module.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigModule(
                        local_n.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtyAlias(
                                crate::types::decl::AliasPresence::MtaPresent,
                                crate::types::Path::Pident(local_n.clone()),
                            ),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let alias_path = crate::types::Path::pdot_pos(
            crate::types::Path::Pident(original_module.clone()),
            "N",
            0,
        );
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
        env.add_type(alias_id.clone(), type_alias_decl(eq_ty));

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let prim = crate::types::PrimitiveDescription {
            prim_name: "%equal".to_string(),
            prim_arity: 2,
            prim_native_name: String::new(),
            prim_native_float: false,
            prim_from_constructor: false,
        };
        let alias_ty = ctx.new_constr(crate::types::Path::Pident(alias_id), vec![]);

        let primitive = primitive_wrapper_body_primitive(converter.translate_primitive_raw_in_env(
            Location::none(),
            &prim,
            alias_ty,
            &env,
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
            pkg.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigModule(
                        Ident::create_local("List"),
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtyIdent(
                                crate::types::Path::Pident(pkg_list.clone()),
                            ),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );
        env.add_module(
            pkg_list.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_module_path_raw(
            &crate::types::Path::pdot(crate::types::Path::Pident(pkg), "List"),
            Location::none(),
        );

        assert!(matches!(
            lowered,
            RawLambda::LglobalModule(id, false) if id.same(&pkg_list)
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
            &crate::types::Path::Pident(side_effect.clone()),
            Location::none(),
        );
        let possible_required_modules = converter.take_possible_required_modules();

        assert!(matches!(
            lowered,
            RawLambda::LglobalModule(id, false) if id.same(&side_effect)
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
                crate::types::Path::Pident(side_effect.clone()),
                crate::parse_arena::Located::mknoloc(crate::parse_arena::LidentIdx(0)),
            ),
            mod_loc: crate::parse_arena::LocIdx::default(),
            mod_type: crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaAbsent,
                crate::types::Path::Pident(side_effect.clone()),
            ),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        };

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        converter.note_possible_required_modules_from_empty_include(&module_expr);
        let possible_required_modules = converter.take_possible_required_modules();
        let expected = ModuleId {
            id: side_effect.clone(),
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
                crate::types::Path::Pident(side_effect.clone()),
                crate::parse_arena::Located::mknoloc(crate::parse_arena::LidentIdx(0)),
            ),
            mod_loc: crate::parse_arena::LocIdx::default(),
            mod_type: crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaPresent,
                crate::types::Path::Pident(side_effect),
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
    fn dynamic_import_marks_global_modules_as_dynamic_possible_requirements() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let side_effect = Ident::create_persistent("Side_effect");

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        converter.note_possible_required_modules_in_raw_lambda(&RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::global_module(side_effect.clone(), false)],
            Location::none(),
        ));
        let possible_required_modules = converter.take_possible_required_modules();

        assert_eq!(possible_required_modules.len(), 1);
        assert!(possible_required_modules.contains(&ModuleId {
            id: side_effect.clone(),
            kind: Kind::Ml,
            dynamic_import: true,
        }));
        assert!(!possible_required_modules.contains(&ModuleId {
            id: side_effect,
            kind: Kind::Ml,
            dynamic_import: false,
        }));
    }

    #[test]
    fn dynamic_import_alias_lets_mark_global_modules_as_dynamic_possible_requirements() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let module_id = Ident::create_persistent("ModuleWithAlias");

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        converter.note_possible_required_modules_in_raw_lambda(&RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::let_(
                LetKind::Strict,
                Ident::create_local("let"),
                RawLambda::global_module(module_id.clone(), false),
                RawLambda::unit(),
            )],
            Location::none(),
        ));
        let possible_required_modules = converter.take_possible_required_modules();

        assert_eq!(possible_required_modules.len(), 1);
        assert!(possible_required_modules.contains(&ModuleId {
            id: module_id.clone(),
            kind: Kind::Ml,
            dynamic_import: true,
        }));
        assert!(!possible_required_modules.contains(&ModuleId {
            id: module_id,
            kind: Kind::Ml,
            dynamic_import: false,
        }));
    }

    #[test]
    fn dynamic_import_pack_idents_record_only_dynamic_possible_requirements() {
        let arena = ParseArena::new();
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let side_effect = Ident::create_persistent("Side_effect");
        let module_expr = crate::types::typedtree::ModuleExpr {
            mod_desc: crate::types::typedtree::ModuleExprDesc::Tmod_ident(
                crate::types::Path::Pident(side_effect.clone()),
                crate::parse_arena::Located::mknoloc(crate::parse_arena::LidentIdx(0)),
            ),
            mod_loc: crate::parse_arena::LocIdx::default(),
            mod_type: crate::types::decl::ModuleType::MtyAlias(
                crate::types::decl::AliasPresence::MtaAbsent,
                crate::types::Path::Pident(side_effect.clone()),
            ),
            mod_env: EnvRef(0),
            mod_attributes: Attributes::new(),
        };

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered =
            converter.convert_module_expr_for_pack_raw_with_dynamic_import(&module_expr, true);
        let possible_required_modules = converter.take_possible_required_modules();

        assert!(matches!(
            lowered,
            RawLambda::LglobalModule(id, false) if id.same(&side_effect)
        ));
        assert_eq!(possible_required_modules.len(), 1);
        assert!(possible_required_modules.contains(&ModuleId {
            id: side_effect.clone(),
            kind: Kind::Ml,
            dynamic_import: true,
        }));
        assert!(!possible_required_modules.contains(&ModuleId {
            id: side_effect,
            kind: Kind::Ml,
            dynamic_import: false,
        }));
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
            local_l.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtyIdent(crate::types::Path::Pident(
                    modtype_x.clone(),
                )),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot(crate::types::Path::Pident(local_l.clone()), "length"),
            Location::none(),
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
            pkg.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigModule(
                        Ident::create_local("List"),
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtyIdent(
                                crate::types::Path::Pident(pkg_list.clone()),
                            ),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );
        env.add_module(
            pkg_list.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigValue(
                        Ident::create_local("length"),
                        crate::types::decl::ValueDescription {
                            val_type: ctx.new_var(None),
                            val_kind: crate::types::decl::ValueKind::ValReg,
                            val_loc: Location::none(),
                            val_attributes: Vec::new(),
                            val_path: None,
                        },
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot(
                crate::types::Path::pdot(crate::types::Path::Pident(pkg), "List"),
                "length",
            ),
            Location::none(),
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
            [RawLambda::LglobalModule(id, false)] if id.same(&pkg_list)
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

        let icon_export_path = crate::types::Path::pdot(
            crate::types::Path::Pident(icon.clone()),
            export.name().to_string(),
        );
        let subtitles_path =
            crate::types::Path::pdot(icon_export_path.clone(), subtitles.name().to_string());
        let main_path = crate::types::Path::pdot(subtitles_path.clone(), main.name().to_string());

        let main_decl = crate::types::decl::ModuleDeclaration {
            md_type: crate::types::decl::ModuleType::MtySignature(vec![
                crate::types::SignatureItem::SigValue(
                    make.clone(),
                    crate::types::decl::ValueDescription {
                        val_type: ctx.new_var(None),
                        val_kind: crate::types::decl::ValueKind::ValReg,
                        val_loc: Location::none(),
                        val_attributes: Vec::new(),
                        val_path: None,
                    },
                ),
            ]),
            md_attributes: Vec::new(),
            md_loc: Location::none(),
            md_path: None,
        };

        env.add_module(
            icon.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigModule(
                        export.clone(),
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtySignature(vec![
                                crate::types::SignatureItem::SigModule(
                                    subtitles.clone(),
                                    crate::types::decl::ModuleDeclaration {
                                        md_type: crate::types::decl::ModuleType::MtySignature(
                                            vec![
                                                crate::types::SignatureItem::SigModule(
                                                    main.clone(),
                                                    main_decl,
                                                    crate::types::decl::RecStatus::TrecNot,
                                                ),
                                                crate::types::SignatureItem::SigModule(
                                                    separate.clone(),
                                                    crate::types::decl::ModuleDeclaration {
                                                        md_type:
                                                            crate::types::decl::ModuleType::MtyAlias(
                                                                crate::types::decl::AliasPresence::MtaPresent,
                                                                main_path.clone(),
                                                            ),
                                                        md_attributes: Vec::new(),
                                                        md_loc: Location::none(),
                                                        md_path: None,
                                                    },
                                                    crate::types::decl::RecStatus::TrecNot,
                                                ),
                                            ],
                                        ),
                                        md_attributes: Vec::new(),
                                        md_loc: Location::none(),
                                        md_path: None,
                                    },
                                    crate::types::decl::RecStatus::TrecNot,
                                ),
                            ]),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let path = crate::types::Path::pdot(
            crate::types::Path::pdot(subtitles_path, separate.name().to_string()),
            make.name().to_string(),
        );
        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(&env, &path, Location::none());

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
            inner_define.clone(),
            crate::types::decl::ModuleDeclaration {
                md_type: crate::types::decl::ModuleType::MtySignature(vec![
                    crate::types::SignatureItem::SigModule(
                        runtime_n,
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtySignature(vec![]),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                    crate::types::SignatureItem::SigModtype(
                        modtype_s0,
                        crate::types::decl::ModtypeDeclaration {
                            mtd_type: Some(crate::types::decl::ModuleType::MtySignature(vec![
                                crate::types::SignatureItem::SigValue(
                                    Ident::create_local("f1"),
                                    crate::types::decl::ValueDescription {
                                        val_type: ctx.new_var(None),
                                        val_kind: crate::types::decl::ValueKind::ValReg,
                                        val_loc: Location::none(),
                                        val_attributes: Vec::new(),
                                        val_path: None,
                                    },
                                ),
                            ])),
                            mtd_attributes: Vec::new(),
                            mtd_loc: Location::none(),
                        },
                    ),
                    crate::types::SignatureItem::SigModule(
                        constrained_n0,
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtyIdent(
                                crate::types::Path::pdot(
                                    crate::types::Path::Pident(inner_define.clone()),
                                    "S0",
                                ),
                            ),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                    crate::types::SignatureItem::SigModule(
                        runtime_n1,
                        crate::types::decl::ModuleDeclaration {
                            md_type: crate::types::decl::ModuleType::MtySignature(vec![]),
                            md_attributes: Vec::new(),
                            md_loc: Location::none(),
                            md_path: None,
                        },
                        crate::types::decl::RecStatus::TrecNot,
                    ),
                ]),
                md_attributes: Vec::new(),
                md_loc: Location::none(),
                md_path: None,
            },
        );

        let mut converter = RawLambdaConverter::new(&arena, &ctx, &env);
        let lowered = converter.translate_value_path_raw_in_env(
            &env,
            &crate::types::Path::pdot_pos(
                crate::types::Path::pdot_pos(
                    crate::types::Path::Pident(inner_define.clone()),
                    "N0",
                    1,
                ),
                "f1",
                0,
            ),
            Location::none(),
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
                    [RawLambda::LglobalModule(id, false)] if id.same(&inner_define)
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
                val_loc: Location::none(),
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
        let [init_v, Constant::String { s, delim }] = elements.as_slice() else {
            panic!("expected function shape tuple");
        };
        assert_eq!(s, "u");
        assert!(matches!(delim, Some(StringDelim::Plain)));
        assert!(matches!(
            init_v,
            Constant::Int {
                i: 0,
                comment: Some(PointerInfo::Constructor(PointerConstructorTag {
                    name,
                    const_,
                    non_const,
                    runtime_tag: None,
                })),
            } if name == "Function"
                && *const_ == REC_MODULE_FUNCTION_CSTR_CONST
                && *non_const == REC_MODULE_FUNCTION_CSTR_NON_CONST
        ));
    }
}
