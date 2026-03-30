//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path as StdPath;
use std::sync::{Mutex, OnceLock};

use crate::context::IdGenerator;
use crate::ident::{Ident, IdentFlags};
use crate::lambda::constant::StringDelim;
use crate::lambda::Constant;
use crate::lambda::compat::LetKind;
use crate::lambda::convert::LambdaConverter;
use crate::lambda::primitive::{ExternalArgSpec, ExternalFfiSpec, Mutable};
use crate::lambda::tag_info::TagInfo;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, Comparison, FieldDbgInfo, FunctionAttribute, InlineAttribute,
    Lambda, LambdaSwitch, Primitive, SetFieldDbgInfo,
};
use crate::location::Location;
use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::{Arity, MutableFlag as ParserMutableFlag};
use crate::raw_lambda::RawLambda;
use crate::raw_lambda::typeopt::{
    constructor_has_optional_shape, type_cannot_contain_undefined,
};
use crate::types::context::TypeContext;
use crate::types::asttypes::MutableFlag as TypeMutableFlag;
use crate::types::ConstructorTag;
use crate::types::decl::{LabelDescription, RecordRepresentation, ValueKind};
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typedtree::{
    ApplyArg, Case, Constant as TConstant, Expression, ExpressionDesc, FunctionParam,
    FunctionParamPattern, MethKind, ModuleCoercion, ModuleExpr, ModuleExprDesc, ModuleTypeDesc,
    Partial, Pattern, PatternDesc, RecordLabelDefinition, Structure, StructureItem,
    StructureItemDesc, ValueBinding,
};
use crate::types::SignatureItem;

const PREDEF_MATCH_FAILURE_STAMP: i32 = 17;
const PREDEF_ASSERT_FAILURE_STAMP: i32 = 27;

#[derive(Clone)]
enum RawFunctionBinding {
    Value(Vec<ValueBinding>),
    Module(Ident, Located<String>, ModuleExpr),
}

fn predef_exception_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::PREDEF_EXN.with_global())
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
            RawLambda::Lswitch(arg, sw) => {
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
            RawLambda::Lassign(id, expr) => {
                collect(expr, fv);
                fv.insert(id.clone());
            }
            RawLambda::Lsend(_, obj, _) => collect(obj, fv),
        }
    }

    let mut fv = HashSet::new();
    collect(lam, &mut fv);
    fv
}

fn raw_subst_lambda(subst: &HashMap<Ident, RawLambda>, lam: &RawLambda) -> RawLambda {
    if subst.is_empty() {
        return lam.clone();
    }

    match lam {
        RawLambda::Lvar(id) => subst.get(id).cloned().unwrap_or_else(|| lam.clone()),
        RawLambda::LglobalModule(_, _) | RawLambda::Lconst(_) => lam.clone(),
        RawLambda::Lapply(apply) => RawLambda::Lapply(crate::raw_lambda::RawApply {
            ap_func: Box::new(raw_subst_lambda(subst, &apply.ap_func)),
            ap_args: apply
                .ap_args
                .iter()
                .map(|arg| raw_subst_lambda(subst, arg))
                .collect(),
            ap_info: apply.ap_info.clone(),
            ap_transformed_jsx: apply.ap_transformed_jsx,
        }),
        RawLambda::Lfunction(func) => RawLambda::Lfunction(crate::raw_lambda::RawLFunction {
            arity: func.arity,
            params: func.params.clone(),
            body: Box::new(raw_subst_lambda(subst, &func.body)),
            attr: func.attr.clone(),
        }),
        RawLambda::Llet(kind, id, arg, body) => RawLambda::Llet(
            *kind,
            id.clone(),
            Box::new(raw_subst_lambda(subst, arg)),
            Box::new(raw_subst_lambda(subst, body)),
        ),
        RawLambda::Lletrec(bindings, body) => RawLambda::Lletrec(
            bindings
                .iter()
                .map(|(id, expr)| (id.clone(), raw_subst_lambda(subst, expr)))
                .collect(),
            Box::new(raw_subst_lambda(subst, body)),
        ),
        RawLambda::Lprim(info) => RawLambda::Lprim(crate::raw_lambda::RawPrimInfo {
            primitive: info.primitive.clone(),
            args: info
                .args
                .iter()
                .map(|arg| raw_subst_lambda(subst, arg))
                .collect(),
            loc: info.loc.clone(),
        }),
        RawLambda::Lswitch(arg, sw) => RawLambda::Lswitch(
            Box::new(raw_subst_lambda(subst, arg)),
            crate::raw_lambda::RawLambdaSwitch {
                sw_consts_full: sw.sw_consts_full,
                sw_consts: sw
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| (*tag, raw_subst_lambda(subst, lam)))
                    .collect(),
                sw_blocks_full: sw.sw_blocks_full,
                sw_blocks: sw
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| (*tag, raw_subst_lambda(subst, lam)))
                    .collect(),
                sw_failaction: sw
                    .sw_failaction
                    .as_ref()
                    .map(|lam| Box::new(raw_subst_lambda(subst, lam))),
                sw_names: sw.sw_names.clone(),
            },
        ),
        RawLambda::LstringSwitch(arg, cases, default) => RawLambda::LstringSwitch(
            Box::new(raw_subst_lambda(subst, arg)),
            cases
                .iter()
                .map(|(name, lam)| (name.clone(), raw_subst_lambda(subst, lam)))
                .collect(),
            default
                .as_ref()
                .map(|lam| Box::new(raw_subst_lambda(subst, lam))),
        ),
        RawLambda::LstaticRaise(i, args) => RawLambda::LstaticRaise(
            *i,
            args.iter().map(|arg| raw_subst_lambda(subst, arg)).collect(),
        ),
        RawLambda::LstaticCatch(body, handler, on_raise) => RawLambda::LstaticCatch(
            Box::new(raw_subst_lambda(subst, body)),
            handler.clone(),
            Box::new(raw_subst_lambda(subst, on_raise)),
        ),
        RawLambda::LtryWith(body, exn, handler) => RawLambda::LtryWith(
            Box::new(raw_subst_lambda(subst, body)),
            exn.clone(),
            Box::new(raw_subst_lambda(subst, handler)),
        ),
        RawLambda::LifThenElse(cond, ifso, ifnot) => RawLambda::LifThenElse(
            Box::new(raw_subst_lambda(subst, cond)),
            Box::new(raw_subst_lambda(subst, ifso)),
            Box::new(raw_subst_lambda(subst, ifnot)),
        ),
        RawLambda::Lsequence(first, second) => RawLambda::Lsequence(
            Box::new(raw_subst_lambda(subst, first)),
            Box::new(raw_subst_lambda(subst, second)),
        ),
        RawLambda::Lwhile(cond, body) => RawLambda::Lwhile(
            Box::new(raw_subst_lambda(subst, cond)),
            Box::new(raw_subst_lambda(subst, body)),
        ),
        RawLambda::Lfor(var, lo, hi, dir, body) => RawLambda::Lfor(
            var.clone(),
            Box::new(raw_subst_lambda(subst, lo)),
            Box::new(raw_subst_lambda(subst, hi)),
            *dir,
            Box::new(raw_subst_lambda(subst, body)),
        ),
        RawLambda::Lassign(id, expr) => {
            RawLambda::Lassign(id.clone(), Box::new(raw_subst_lambda(subst, expr)))
        }
        RawLambda::Lsend(name, obj, loc) => RawLambda::Lsend(
            name.clone(),
            Box::new(raw_subst_lambda(subst, obj)),
            loc.clone(),
        ),
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
        PatternDesc::Tpat_alias(inner, id, _) if matches!(inner.pat_desc, PatternDesc::Tpat_any) => {
            Some(id.clone())
        }
        _ => None,
    }
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
        RecordRepresentation::RecordInlined { .. } => FieldDbgInfo::RecordInline {
            name,
        },
        RecordRepresentation::RecordExtension => FieldDbgInfo::RecordExtension {
            name,
        },
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
        RecordRepresentation::RecordInlined { .. } => {
            SetFieldDbgInfo::RecordInlineSet(name)
        }
        RecordRepresentation::RecordExtension => {
            SetFieldDbgInfo::RecordExtensionSet(name)
        }
    };
    let pos = match lbl.lbl_repres {
        RecordRepresentation::RecordExtension => lbl.lbl_pos + 1,
        _ => lbl.lbl_pos,
    };
    Some((pos, info))
}

fn raw_record_mutable_flag(
    fields: &[(Located<LidentIdx>, LabelDescription, RecordLabelDefinition, bool)],
) -> ParserMutableFlag {
    fields
        .iter()
        .find(|(_, lbl, _, _)| lbl.lbl_mut == TypeMutableFlag::Mutable)
        .map(|_| ParserMutableFlag::Mutable)
        .unwrap_or(ParserMutableFlag::Immutable)
}

fn trace_raw_fallback(kind: &'static str) {
    if std::env::var_os("RUST_RAW_FALLBACK_TRACE").is_none() {
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
    if std::env::var_os("RUST_RAW_FALLBACK_TRACE").is_none() {
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
            SimpleSwitchKey::Int(i) | SimpleSwitchKey::ConstCtor(i) | SimpleSwitchKey::BlockCtor(i) => *i,
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

/// Converter from typedtree to raw lambda.
pub struct RawLambdaConverter<'a> {
    arena: &'a ParseArena,
    type_ctx: &'a TypeContext<'a>,
    env: &'a crate::types::env::Env,
    persistent_env: Option<crate::cmi::persistent_env::PersistentEnv>,
    id_gen: IdGenerator,
    next_static_raise: i32,
    lowered: LambdaConverter<'a>,
    unit_name: String,
}

impl<'a> RawLambdaConverter<'a> {
    /// Create a new raw-lambda converter.
    pub fn new(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext<'a>,
        env: &'a crate::types::env::Env,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            id_gen: IdGenerator::new(),
            next_static_raise: 0,
            lowered: LambdaConverter::new(arena),
            unit_name: String::new(),
        }
    }

    /// Create a new raw-lambda converter with stamps continuing from an existing phase.
    pub fn with_start_stamp(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext<'a>,
        env: &'a crate::types::env::Env,
        start_stamp: i32,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            id_gen: IdGenerator::with_start_stamp(start_stamp),
            next_static_raise: 0,
            lowered: LambdaConverter::with_start_stamp(arena, start_stamp),
            unit_name: String::new(),
        }
    }

    /// Create a new raw-lambda converter with the current compilation unit name.
    pub fn with_start_stamp_and_unit_name(
        arena: &'a ParseArena,
        type_ctx: &'a TypeContext<'a>,
        env: &'a crate::types::env::Env,
        start_stamp: i32,
        unit_name: String,
    ) -> Self {
        Self {
            arena,
            type_ctx,
            env,
            persistent_env: None,
            id_gen: IdGenerator::with_start_stamp(start_stamp),
            next_static_raise: 0,
            lowered: LambdaConverter::with_start_stamp(arena, start_stamp),
            unit_name,
        }
    }

    pub fn set_persistent_env(&mut self, persistent_env: crate::cmi::persistent_env::PersistentEnv) {
        self.persistent_env = Some(persistent_env);
    }

    #[inline]
    fn loc(&self, idx: LocIdx) -> Location {
        self.arena.to_location(idx)
    }

    fn next_raise_count(&mut self) -> i32 {
        self.next_static_raise += 1;
        self.next_static_raise
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
            .unwrap_or_else(|| self.id_gen.create(default))
    }

    fn fresh_name_from_cases(&self, default: &str, cases: &[Case]) -> String {
        case_name_hint(default, cases)
            .unwrap_or_else(|| default.to_string())
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

    fn field_path(rootpath: &Option<crate::types::Path>, field: &Ident) -> Option<crate::types::Path> {
        rootpath
            .as_ref()
            .map(|path| crate::types::Path::pdot(path.clone(), field.name().to_string()))
    }

    /// Extract inline attribute from module attributes, matching OCaml's
    /// Translattribute.get_inline_attribute.
    fn get_inline_attribute_from(
        attrs: &crate::parser::ast::Attributes,
        arena: &ParseArena,
    ) -> InlineAttribute {
        use crate::parser::ast::{Payload, StructureItemDesc, ExpressionDesc};
        use crate::parser::longident::Longident;
        for (located_name, payload) in attrs.iter() {
            let attr_name = arena.get_string(located_name.txt);
            if attr_name == "inline" {
                match payload {
                    Payload::PStr(items) if items.is_empty() => {
                        // @inline without arguments = always
                        return InlineAttribute::Always;
                    }
                    Payload::PStr(items) if items.len() == 1 => {
                        if let StructureItemDesc::Pstr_eval(eval_inner) = &*items[0].pstr_desc {
                            let (expr_idx, _) = &**eval_inner;
                            let expr = arena.get_expr(*expr_idx);
                            if let ExpressionDesc::Pexp_ident(ident) = &*expr.pexp_desc {
                                let lid = arena.get_longident(ident.txt);
                                if let Longident::Lident(str_idx) = lid {
                                    let name = arena.get_string(*str_idx);
                                    if name == "always" {
                                        return InlineAttribute::Always;
                                    } else if name == "never" {
                                        return InlineAttribute::Never;
                                    }
                                }
                            }
                        }
                        return InlineAttribute::Default;
                    }
                    _ => return InlineAttribute::Default,
                }
            }
        }
        InlineAttribute::Default
    }

    /// OCaml's share_actions_sw: deduplicate switch actions by wrapping shared
    /// actions in catch/exit. Returns the list of catch handlers to wrap around the switch.
    fn share_actions_sw(
        &mut self,
        sw: &mut crate::raw_lambda::RawLambdaSwitch,
    ) -> Vec<(i32, RawLambda)> {
        use crate::raw_lambda::print::RawLambdaPrinter;

        // Map from action key (string repr) to (exit_id, original_action)
        let mut store: Vec<(String, i32, RawLambda)> = Vec::new();
        let mut handlers: Vec<(i32, RawLambda)> = Vec::new();

        let mut get_or_create = |action: &RawLambda, self_ref: &mut Self| -> Option<RawLambda> {
            // If already an exit, don't wrap again
            if matches!(action, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                return None;
            }

            let key = format!("{}", RawLambdaPrinter::new(action));

            // Check if we've seen this action before
            for (stored_key, exit_id, _) in &store {
                if *stored_key == key {
                    // Shared! Return exit to existing handler
                    return Some(RawLambda::LstaticRaise(*exit_id, Vec::new()));
                }
            }

            // First occurrence - store it but don't wrap yet
            let exit_id = self_ref.next_raise_count();
            store.push((key, exit_id, action.clone()));
            None
        };

        // First pass: identify shared actions
        let all_actions: Vec<(String, bool)> = sw.sw_consts.iter()
            .map(|(_, act)| (format!("{}", RawLambdaPrinter::new(act)), true))
            .chain(sw.sw_blocks.iter()
                .map(|(_, act)| (format!("{}", RawLambdaPrinter::new(act)), false)))
            .collect();

        // Count occurrences of each action key
        let mut key_counts: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for (key, _) in &all_actions {
            *key_counts.entry(key.clone()).or_insert(0) += 1;
        }

        // Second pass: wrap shared actions in catch/exit
        let mut exit_map: std::collections::HashMap<String, i32> = std::collections::HashMap::new();

        for (tag, action) in sw.sw_consts.iter_mut() {
            if matches!(action, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                continue;
            }
            let key = format!("{}", RawLambdaPrinter::new(action));
            let count = key_counts.get(&key).copied().unwrap_or(0);
            if count >= 2 {
                let exit_id = if let Some(&eid) = exit_map.get(&key) {
                    eid
                } else {
                    let eid = self.next_raise_count();
                    exit_map.insert(key.clone(), eid);
                    handlers.push((eid, action.clone()));
                    eid
                };
                *action = RawLambda::LstaticRaise(exit_id, Vec::new());
            }
        }

        for (tag, action) in sw.sw_blocks.iter_mut() {
            if matches!(action, RawLambda::LstaticRaise(_, args) if args.is_empty()) {
                continue;
            }
            let key = format!("{}", RawLambdaPrinter::new(action));
            let count = key_counts.get(&key).copied().unwrap_or(0);
            if count >= 2 {
                let exit_id = if let Some(&eid) = exit_map.get(&key) {
                    eid
                } else {
                    let eid = self.next_raise_count();
                    exit_map.insert(key.clone(), eid);
                    handlers.push((eid, action.clone()));
                    eid
                };
                *action = RawLambda::LstaticRaise(exit_id, Vec::new());
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
            sw.sw_consts.retain(|(_, lam)| as_simple_exit(lam) != Some(best_exit));
            sw.sw_blocks.retain(|(_, lam)| as_simple_exit(lam) != Some(best_exit));
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
                        sw_consts_full: false,
                        sw_consts: const_cases,
                        sw_blocks_full: false,
                        sw_blocks: block_cases,
                        sw_failaction: Some(Box::new(RawLambda::LstaticRaise(
                            exit_id,
                            Vec::new(),
                        ))),
                        sw_names: None,
                    },
                );
                RawLambda::LstaticCatch(
                    Box::new(switch),
                    (exit_id, Vec::new()),
                    default,
                )
            }
            None => {
                let mut sw = crate::raw_lambda::RawLambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: const_cases,
                    sw_blocks_full: false,
                    sw_blocks: block_cases,
                    sw_failaction: None,
                    sw_names: None,
                };
                // OCaml: share_actions_sw then reintroduce_fail
                let share_handlers = self.share_actions_sw(&mut sw);
                Self::reintroduce_fail(&mut sw);
                let mut result = RawLambda::Lswitch(Box::new(scrut), sw);
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
    fn apply_inline_attribute_raw(lam: RawLambda, inline: InlineAttribute) -> RawLambda {
        if matches!(inline, InlineAttribute::Default) {
            return lam;
        }
        match lam {
            RawLambda::Lfunction(mut func) => {
                func.attr.inline = inline;
                RawLambda::Lfunction(func)
            }
            RawLambda::Lprim(prim) => {
                // Walk through Pjs_fn_make wrappers
                match &prim.primitive {
                    Primitive::PjsFnMake(_) | Primitive::PjsFnMakeUnit => {
                        let mut args = prim.args;
                        if let Some(last) = args.pop() {
                            let inner = Self::apply_inline_attribute_raw(last, inline);
                            args.push(inner);
                        }
                        RawLambda::Lprim(crate::raw_lambda::RawPrimInfo {
                            primitive: prim.primitive,
                            args,
                            loc: prim.loc,
                        })
                    }
                    _ => RawLambda::Lprim(prim),
                }
            }
            other => other,
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
                    self.transl_extension_constructor_raw(Self::field_path(rootpath, &ext.ext_id), ext),
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
        match self.type_desc(ty) {
            TypeDesc::Tarrow { arg, ret, .. } => Some((arg.typ, ret)),
            _ => None,
        }
    }

    /// Like is_function_type but only matches when the argument has no label (Nolabel).
    /// Matches OCaml's check: Tarrow ({lbl = Nolabel; typ}, ...)
    fn is_nolabel_function_type(&self, ty: TypeExprRef) -> Option<(TypeExprRef, TypeExprRef)> {
        match self.type_desc(ty) {
            TypeDesc::Tarrow { arg, ret, .. }
                if matches!(arg.lbl, crate::types::asttypes::ArgLabel::Nolabel) =>
            {
                Some((arg.typ, ret))
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
            TypeDesc::Tarrow { arity, .. } => *arity,
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
        match self.type_desc(ty) {
            TypeDesc::Tconstr { path, .. } => path.head_name() == name || path.last() == name,
            _ => false,
        }
    }

    fn is_immediate_type(&self, ty: TypeExprRef) -> bool {
        self.is_base_type(ty, "int")
            || self.is_base_type(ty, "char")
            || self.is_base_type(ty, "bool")
            || self.is_base_type(ty, "unit")
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
            RawLocKind::Module => RawLambda::const_(Constant::ImmString(if self.unit_name.is_empty() {
                format!("//{file}//")
            } else {
                self.unit_name.clone()
            })),
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

    fn raw_assert_failure(&self, loc: Location) -> RawLambda {
        RawLambda::from_lowered(self.raise_predef_exception(
            "Assert_failure",
            PREDEF_ASSERT_FAILURE_STAMP,
            loc,
        ))
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
                ExpressionDesc::Texp_let(crate::parser::ast::RecFlag::Nonrecursive, binds, inner)
                    if self.has_only_expr_attr(&case.c_rhs, "#default")
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
        let choose = |int_prim: Primitive,
                      bool_prim: Option<Primitive>,
                      float_prim: Option<Primitive>,
                      bigint_prim: Option<Primitive>,
                      string_prim: Option<Primitive>| {
            if self.is_base_type(lhs_type, "int") || self.is_immediate_type(lhs_type) {
                int_prim
            } else if self.is_base_type(lhs_type, "float") {
                float_prim.unwrap_or(int_prim)
            } else if self.is_base_type(lhs_type, "bigint") {
                bigint_prim.unwrap_or(int_prim)
            } else if self.is_base_type(lhs_type, "string") {
                string_prim.unwrap_or(int_prim)
            } else if self.is_base_type(lhs_type, "bool") {
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
        let table = |cmp: crate::lambda::Comparison,
                     simplify_constant_constructor| ComparisonSpecialization {
            objcomp: Primitive::Pobjcomp(cmp),
            intcomp: Primitive::Pintcomp(cmp),
            boolcomp: Primitive::Pboolcomp(cmp),
            floatcomp: Primitive::Pfloatcomp(cmp),
            stringcomp: Primitive::Pstringcomp(cmp),
            bigintcomp: Primitive::Pbigintcomp(cmp),
            simplify_constant_constructor,
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

    fn specialize_comparison(
        &self,
        table: ComparisonSpecialization,
        ty: TypeExprRef,
    ) -> Primitive {
        if self.is_base_type(ty, "int")
            || self.is_base_type(ty, "char")
            || self.is_immediate_type(ty)
        {
            table.intcomp
        } else if self.is_base_type(ty, "float") {
            table.floatcomp
        } else if self.is_base_type(ty, "string") {
            table.stringcomp
        } else if self.is_base_type(ty, "bigint") {
            table.bigintcomp
        } else if self.is_base_type(ty, "bool") {
            table.boolcomp
        } else {
            table.objcomp
        }
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
            "%makeref" => Some(Primitive::Pmakeblock(0, TagInfo::ref_tag(), Mutable::Mutable)),
            "%refset" => Some(Primitive::Psetfield(
                0,
                crate::lambda::compat::SetFieldDbgInfo::RecordSet("contents".to_string()),
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
                            crate::lambda::compat::SetFieldDbgInfo::RecordSet(String::new()),
                        ));
                    }
                }
                self.lowered.primitive_from_name(prim_name)
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
        let resolved = self.specialize_primitive_raw(prim, ty).unwrap_or_else(|| {
            Primitive::PjsCall {
                prim_name: Self::raw_primitive_name(&prim.prim_name).to_string(),
                arg_types: vec![ExternalArgSpec { label: None }; prim.prim_arity.max(0) as usize],
                ffi: ExternalFfiSpec { module_name: None },
                dynamic_import: false,
                transformed_jsx: false,
            }
        });

        let prim_arity = prim.prim_arity;

        // OCaml: if p.prim_from_constructor || prim_arity = 0 then Lprim (prim, [], loc)
        if prim_arity == 0 {
            return RawLambda::prim(resolved, vec![], loc);
        }

        // Create parameter idents matching OCaml's naming
        let params: Vec<Ident> = if prim_arity == 1 {
            vec![self.id_gen.create("prim")]
        } else {
            (0..prim_arity)
                .map(|i| self.id_gen.create(&format!("prim{}", i)))
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
        let prim_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some((lhs, _)) = self.is_function_type(ty) {
            if let Some(primitive) = self.translate_unified_ops_primitive(prim_name, lhs) {
                return Some(primitive);
            }
            if let Some(table) = Self::comparison_specialization(prim_name) {
                return Some(self.specialize_comparison(table, lhs));
            }
        } else if let Some(table) = Self::comparison_specialization(prim_name) {
            return Some(table.objcomp);
        }

        self.find_raw_primitive(prim_name)
    }

    fn translate_primitive_application_raw(
        &self,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
        args: &[&Expression],
        transformed_jsx: bool,
    ) -> Primitive {
        let prim_name = Self::raw_primitive_name(&prim.prim_name);

        if let [arg1] | [arg1, _] = args {
            if let Some(primitive) = self.translate_unified_ops_primitive(prim_name, arg1.exp_type)
            {
                return primitive;
            }
        }

        if let [arg1, _] = args {
            if let Some(table) = Self::comparison_specialization(prim_name) {
                if self.is_base_type(arg1.exp_type, "bool") {
                    return table.boolcomp;
                }
                if args.iter().any(|arg| Self::has_constant_constructor_arg(arg))
                    && table.simplify_constant_constructor
                {
                    return table.intcomp;
                }
            }
        }

        if let Some(primitive) = self.specialize_primitive_raw(prim, ty) {
            primitive
        } else {
            Primitive::PjsCall {
                prim_name: prim_name.to_string(),
                arg_types: vec![ExternalArgSpec { label: None }; prim.prim_arity.max(0) as usize],
                ffi: ExternalFfiSpec { module_name: None },
                dynamic_import: false,
                transformed_jsx,
            }
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
    ) -> TagInfo {
        match &cstr.cstr_tag {
            ConstructorTag::CstrBlock(_)
                if constructor_has_optional_shape(cstr) =>
            {
                match args {
                    [arg]
                        if type_cannot_contain_undefined(
                            self.type_ctx,
                            self.env,
                            arg.exp_type,
                        ) =>
                    {
                        TagInfo::SomeNotNested
                    }
                    _ => TagInfo::Some,
                }
            }
            ConstructorTag::CstrBlock(tag) => TagInfo::constructor(
                cstr.cstr_name.clone(),
                cstr.cstr_nonconsts,
                *tag,
            ),
            _ => TagInfo::constructor(cstr.cstr_name.clone(), cstr.cstr_nonconsts, 0),
        }
    }

    fn convert_construct_raw(
        &mut self,
        loc: Location,
        cstr: &crate::types::ConstructorDescription,
        args: &[Expression],
    ) -> RawLambda {
        if cstr.cstr_inlined.is_some() {
            return match args {
                [arg] => self.convert_expr_raw(arg),
                _ => RawLambda::unit(),
            };
        }

        match &cstr.cstr_tag {
            ConstructorTag::CstrConstant(tag) => match cstr.cstr_name.as_str() {
                "true" => RawLambda::const_(Constant::JsTrue),
                "false" => RawLambda::const_(Constant::JsFalse),
                _ => RawLambda::const_(Constant::Pointer(format!("{tag}a"))),
            },
            ConstructorTag::CstrUnboxed => match args {
                [arg] => self.convert_expr_raw(arg),
                _ => RawLambda::unit(),
            },
            ConstructorTag::CstrBlock(tag) => {
                let elems = args.iter().map(|arg| self.convert_expr_raw(arg)).collect();
                let tag_info = self.raw_constructor_tag_info(cstr, args);
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
        fields: &[(Located<LidentIdx>, LabelDescription, RecordLabelDefinition, bool)],
        base: Option<&Expression>,
    ) -> RawLambda {
        let Some((_, first_lbl, _, _)) = fields.first() else {
            // Empty record: OCaml creates Pmakeblock(tag=0, []) which prints as [0]
            return self.raw_block_or_prim(
                0,
                TagInfo::Record {
                    fields: Vec::new(),
                    mutable_flag: ParserMutableFlag::Immutable,
                },
                Vec::new(),
                loc,
            );
        };

        let repres = first_lbl.lbl_repres.clone();
        let mutable_flag = raw_record_mutable_flag(fields);
        let base_lam = base.map(|expr| self.convert_expr_raw(expr));
        let has_optional = fields.iter().any(|(_, lbl, _, _)| lbl.lbl_optional);
        // OCaml uses field-by-field construction when:
        // - no base expression, OR
        // - all fields are overridden (no Kept), OR
        // - size < 20 AND no optional fields (OCaml's transl_record line 1130)
        let build_direct = base.is_none()
            || fields
                .iter()
                .all(|(_, _, def, _)| matches!(def, RecordLabelDefinition::Overridden(_, _)))
            || (fields.len() < 20 && !has_optional);

        if build_direct {
            // OCaml wraps the init expression in a let binding when there's a
            // base expression, so field accesses use Lvar(init_id) not the expr.
            let init_id = base_lam.as_ref().map(|_| self.id_gen.create("init"));
            let init_var = init_id.as_ref().map(|id| RawLambda::var(id.clone()));

            let mut elems = Vec::with_capacity(fields.len());
            for (lid, lbl, def, _) in fields {
                let value = match def {
                    RecordLabelDefinition::Overridden(_, expr) => self.convert_expr_raw(expr),
                    RecordLabelDefinition::Kept(_) => {
                        let Some(base_var) = &init_var else {
                            elems.push(RawLambda::unit());
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
            }

            let fields_info = fields
                .iter()
                .map(|(_, lbl, _, _)| (label_runtime_name(lbl), lbl.lbl_optional))
                .collect::<Vec<_>>();

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
                    tag,
                    name,
                    num_nonconsts,
                    ..
                } => {
                    let tag_info = TagInfo::RecordInlined {
                        name,
                        num_nonconst: num_nonconsts,
                        tag,
                        fields: fields_info,
                        mutable_flag,
                        attrs: vec![],
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
                            Mutable::Immutable,
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

        let copy_id = self.id_gen.create("newrecord");
        let mut body = RawLambda::var(copy_id.clone());
        for (_, lbl, def, _) in fields.iter().rev() {
            let RecordLabelDefinition::Overridden(_, expr) = def else {
                continue;
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
        let mut fields = Vec::new();
        self.convert_structure_items_raw(
            &mut fields,
            &structure.str_items,
            true,
            &self.global_path(),
            cc,
            Location::none(),
        )
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
                let id = self.id_gen.create("let");
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

    fn translate_normal_path_raw(&self, path: &crate::types::Path, loc: Location) -> RawLambda {
        match path {
            crate::types::Path::Pident(id) => {
                if id.is_global() {
                    RawLambda::global_module(id.clone(), false)
                } else {
                    RawLambda::var(id.clone())
                }
            }
            crate::types::Path::Pdot(prefix, name, pos) => {
                let prefix_lam = self.translate_normal_path_raw(prefix, loc);
                RawLambda::prim(
                    Primitive::Pfield(*pos, FieldDbgInfo::Module { name: name.clone() }),
                    vec![prefix_lam],
                    loc,
                )
            }
            crate::types::Path::Papply(_, _) => RawLambda::unit(),
        }
    }

    fn resolve_module_type_for_path(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        visiting: &mut HashSet<crate::types::Path>,
    ) -> Option<crate::types::decl::ModuleType> {
        use crate::types::decl::{ModuleType, SignatureItem};

        if !visiting.insert(path.clone()) {
            return None;
        }

        match path {
            crate::types::Path::Pident(id) => {
                if let Ok(md) = env.lookup_module(path) {
                    Some(md.md_type.clone())
                } else if id.is_persistent() {
                    self.persistent_env
                        .as_mut()
                        .and_then(|pers| pers.find_pers_struct(id.name(), self.type_ctx))
                        .map(|ps| ModuleType::MtySignature(ps.ps_sig.clone()))
                } else {
                    None
                }
            }
            crate::types::Path::Pdot(parent, name, _) => {
                let parent_mty = self.resolve_module_type_for_path(env, parent, visiting)?;
                let parent_sig = match parent_mty {
                    ModuleType::MtySignature(sig) => sig,
                    ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
                        match self.resolve_module_type_for_path(env, &alias_path, visiting)? {
                            ModuleType::MtySignature(sig) => sig,
                            _ => return None,
                        }
                    }
                    ModuleType::MtyFunctor { .. } => return None,
                };
                parent_sig.iter().find_map(|item| match item {
                    SignatureItem::SigModule(id, md, _) if id.name() == name => Some(md.md_type.clone()),
                    _ => None,
                })
            }
            crate::types::Path::Papply(_, _) => None,
        }
    }

    fn normalize_module_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        let path = match path {
            crate::types::Path::Pdot(prefix, name, pos) => crate::types::Path::Pdot(
                Box::new(self.normalize_module_path_in_env(env, prefix)),
                name.clone(),
                *pos,
            ),
            crate::types::Path::Papply(left, right) => crate::types::Path::Papply(
                Box::new(self.normalize_module_path_in_env(env, left)),
                Box::new(self.normalize_module_path_in_env(env, right)),
            ),
            _ => path.clone(),
        };

        let mut visiting = HashSet::new();
        match self.resolve_module_type_for_path(env, &path, &mut visiting) {
            Some(crate::types::decl::ModuleType::MtyAlias(_, alias_path))
            | Some(crate::types::decl::ModuleType::MtyIdent(alias_path)) => {
                self.normalize_module_path_in_env(env, &alias_path)
            }
            _ => path,
        }
    }

    fn normalize_value_path_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
    ) -> crate::types::Path {
        match path {
            crate::types::Path::Pdot(prefix, name, pos) => crate::types::Path::Pdot(
                Box::new(self.normalize_module_path_in_env(env, prefix)),
                name.clone(),
                *pos,
            ),
            crate::types::Path::Pident(_) => path.clone(),
            crate::types::Path::Papply(_, _) => path.clone(),
        }
    }

    fn translate_module_path_raw(&mut self, path: &crate::types::Path, loc: Location) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(self.env, path);
        self.translate_normal_path_raw(&normalized, loc)
    }

    fn translate_module_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: Location,
    ) -> RawLambda {
        let normalized = self.normalize_module_path_in_env(env, path);
        self.translate_normal_path_raw(&normalized, loc)
    }

    fn translate_value_path_raw(&mut self, path: &crate::types::Path, loc: Location) -> RawLambda {
        if let Some(lam) = self.value_path_loc_constant(path, loc) {
            return lam;
        }
        let normalized = self.normalize_value_path_in_env(self.env, path);
        if let Some(lam) = self.value_path_loc_constant(&normalized, loc) {
            return lam;
        }
        self.translate_normal_path_raw(&normalized, loc)
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
        self.translate_normal_path_raw(&normalized, loc)
    }

    fn translate_extension_path_raw(
        &mut self,
        path: &crate::types::Path,
        loc: Location,
    ) -> RawLambda {
        self.translate_value_path_raw(path, loc)
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

    fn compose_coercions_raw(
        left: &ModuleCoercion,
        right: &ModuleCoercion,
    ) -> ModuleCoercion {
        match (left, right) {
            (ModuleCoercion::Tcoerce_none, other) => other.clone(),
            (other, ModuleCoercion::Tcoerce_none) => other.clone(),
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
        let fv = raw_free_variables(&lam);
        let mut lam = lam;
        let mut subst = HashMap::new();

        for (id, pos, coercion) in id_pos_list {
            if fv.contains(id) {
                let rebound = self.id_gen.create(id.name());
                let field = get_field(self, id.name(), *pos);
                let value = self.apply_coercion_raw(loc.clone(), LetKind::Alias, coercion, field);
                lam = RawLambda::let_(LetKind::Alias, rebound.clone(), value, lam);
                subst.insert(id.clone(), RawLambda::var(rebound));
            }
        }

        if subst.is_empty() {
            lam
        } else {
            raw_subst_lambda(&subst, &lam)
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
                let param = self.id_gen.create("funarg");
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
            ModuleCoercion::Tcoerce_alias(_, path, inner) => self.name_lambda_raw(strict, arg, |this, _| {
                this.apply_coercion_raw(
                    loc.clone(),
                    LetKind::Alias,
                    inner,
                    this.translate_normal_path_raw(path, loc.clone()),
                )
            }),
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
                let block_fields = fields.iter().cloned().map(RawLambda::var).collect();
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
                            block_fields.push(
                                self.transl_primitive_raw(&pc.pc_desc, pc.pc_type, pc.pc_loc.clone()),
                            );
                        }
                        _ => {
                            if let Some(id) = fields.get(*pos).cloned() {
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
                    |_, _name, pos| {
                        fields
                            .get(pos)
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
        if matches!(module_expr.mod_type.mty_desc, ModuleTypeDesc::Tmty_alias(_, _)) {
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
            ModuleExprDesc::Tmod_constraint(inner, _, _, inner_cc) => self
                .convert_module_expr_raw_with_coercion(
                    inner,
                    rootpath,
                    &Self::compose_coercions_raw(cc, inner_cc),
                ),
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
                let inline_attribute = Self::get_inline_attribute_from(&module_expr.mod_attributes, self.arena);
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
                let apply = RawLambda::Lapply(crate::raw_lambda::RawApply {
                    ap_func: Box::new(self.convert_module_expr_raw_with_coercion(
                        funct,
                        &None,
                        &ModuleCoercion::Tcoerce_none,
                    )),
                    ap_args: vec![self.convert_module_expr_raw_with_coercion(arg, &None, ccarg)],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined: InlineAttribute::Default,
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
        self.convert_module_expr_raw_with_coercion(module_expr, rootpath, &ModuleCoercion::Tcoerce_none)
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
            StructureItemDesc::Tstr_eval(expr, _) => RawLambda::seq(
                self.convert_expr_raw(expr),
                self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc),
            ),
            StructureItemDesc::Tstr_value(rec_flag, bindings) => {
                let old_len = fields.len();
                fields.extend(let_bound_idents(bindings));
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                self.convert_let_with_body_raw(*rec_flag, bindings, body)
            }
            StructureItemDesc::Tstr_module(binding) => {
                let old_len = fields.len();
                if !self.rescript_hide_attributes(&binding.mb_attributes) {
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
                let inline_attr =
                    Self::get_inline_attribute_from(&binding.mb_attributes, self.arena);
                module_body =
                    Self::apply_inline_attribute_raw(module_body, inline_attr);
                RawLambda::let_(
                    Self::pure_module(&binding.mb_expr),
                    binding.mb_id.clone(),
                    module_body,
                    body,
                )
            }
            StructureItemDesc::Tstr_typext(tyext) => {
                let old_len = fields.len();
                fields.extend(tyext.tyext_constructors.iter().map(|ext| ext.ext_id.clone()));
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
                let old_len = fields.len();
                fields.extend(ids.iter().map(|(id, _)| id.clone()));
                let body =
                    self.convert_structure_items_raw(fields, rem, is_top_level, rootpath, cc, loc);
                fields.truncate(old_len);
                let mid = self.id_gen.create("include");
                let body = self.rebind_included_idents_raw(
                    &mid,
                    &ids,
                    body,
                    self.loc(incl.incl_loc),
                );
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
                    fields.push(mb.mb_id.clone());
                }
                let body = self.convert_structure_items_raw(
                    fields, rem, is_top_level, rootpath, cc, loc,
                );
                fields.truncate(old_len);

                // OCaml's Transl_recmodule.compile_recmodule generates:
                // - Simple letrec for function/const-only modules
                // - init_mod/update_mod for complex recursive modules
                // For now, always generate simple letrec
                let rec_bindings: Vec<(Ident, RawLambda)> = bindings
                    .iter()
                    .map(|mb| {
                        let module_lam = self.convert_module_expr_raw(&mb.mb_expr, &None);
                        (mb.mb_id.clone(), module_lam)
                    })
                    .collect();

                RawLambda::Lletrec(rec_bindings, Box::new(body))
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
            | StructureItemDesc::Tstr_attribute(_) => self.convert_structure_items(fields, rem, is_top_level),
        }
    }

    fn convert_expr_raw(&mut self, expr: &Expression) -> RawLambda {
        match &expr.exp_desc {
            ExpressionDesc::Texp_ident(path, _, desc) => match &desc.val_kind {
                ValueKind::ValPrim(prim) => {
                    self.translate_primitive_raw(self.loc(expr.exp_loc), prim, expr.exp_type)
                }
                ValueKind::ValReg => {
                    if let Some(env) = self.env_for_expr(expr) {
                        self.translate_value_path_raw_in_env(env.as_ref(), path, self.loc(expr.exp_loc))
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
            } if body.len() == 1 && body[0].c_guard.is_none() => {
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
                    self.loc(expr.exp_loc),
                )
            }
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => self.convert_apply_raw(
                self.loc(expr.exp_loc),
                funct,
                args,
                *partial,
                *transformed_jsx,
            ),
            ExpressionDesc::Texp_match(scrut, cases, exn_cases, partial) if exn_cases.is_empty() => self
                .compile_irrefutable_match_raw(scrut, cases)
                .or_else(|| {
                    self.compile_simple_string_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .or_else(|| {
                    self.compile_simple_variant_match_raw(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .or_else(|| {
                    self.compile_simple_tuple_match_raw(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .or_else(|| {
                    self.compile_simple_constructor_match_raw(
                        self.loc(expr.exp_loc),
                        scrut,
                        cases,
                        *partial,
                    )
                })
                .unwrap_or_else(|| {
                    trace_raw_match_fallback(&self.loc(expr.exp_loc), scrut, cases);
                    RawLambda::from_lowered(self.lowered.convert_expr(expr))
                }),
            ExpressionDesc::Texp_try(body, cases) => self
                .compile_simple_trywith_raw(self.loc(expr.exp_loc), body, cases)
                .unwrap_or_else(|| RawLambda::from_lowered(self.lowered.convert_expr(expr))),
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items
                    .iter()
                    .map(|item| self.convert_expr_raw(item))
                    .collect::<Vec<_>>();
                self.raw_block_or_prim(0, TagInfo::Tuple, elems, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => {
                self.convert_construct_raw(self.loc(expr.exp_loc), cstr, args)
            }
            ExpressionDesc::Texp_variant(tag, arg) => match arg {
                None => RawLambda::const_(Constant::Pointer(format!(
                    "{}a",
                    crate::types::btype::hash_variant(tag)
                ))),
                Some(arg) => {
                    let arg_lam = self.convert_expr_raw(arg);
                    self.raw_block_or_prim(
                        0,
                        TagInfo::PolyVar(tag.to_string()),
                        vec![
                            RawLambda::const_(Constant::int(crate::types::btype::hash_variant(tag))),
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
            ),
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
                RawLambda::seq(self.convert_expr_raw(a), self.convert_expr_raw(b))
            }
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
            ExpressionDesc::Texp_send(obj_expr, MethKind::Tmeth_name(name), _) => RawLambda::Lsend(
                name.clone(),
                Box::new(self.convert_expr_raw(obj_expr)),
                self.loc(expr.exp_loc),
            ),
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
            ExpressionDesc::Texp_pack(modl) => self.convert_module_expr_raw(modl, &None),
            ExpressionDesc::Texp_assert(inner_expr) => {
                if matches!(
                    inner_expr.exp_desc,
                    ExpressionDesc::Texp_construct(_, ref cstr, ref args)
                        if cstr.cstr_name == "false" && args.is_empty()
                ) {
                    self.raw_assert_failure(self.loc(expr.exp_loc))
                } else {
                    let failure = self.raw_assert_failure(self.loc(expr.exp_loc));
                    RawLambda::LifThenElse(
                        Box::new(self.convert_expr_raw(inner_expr)),
                        Box::new(RawLambda::unit()),
                        Box::new(failure),
                    )
                }
            }
            _ => RawLambda::from_lowered(self.convert_expr(expr)),
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
            ExpressionDesc::Texp_match(scrut, cases, exn_cases, partial) if exn_cases.is_empty() => self
                .compile_irrefutable_match(scrut, cases)
                .or_else(|| {
                    self.compile_simple_tuple_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .or_else(|| {
                    self.compile_simple_constructor_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .unwrap_or_else(|| {
                    trace_raw_match_fallback(&self.loc(expr.exp_loc), scrut, cases);
                    self.lowered.convert_expr(expr)
                }),
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
                _ => self.lowered.convert_expr(expr),
            },
            ExpressionDesc::Texp_variant(tag, arg) => self.convert_poly_variant(tag, arg),
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
            } => self.convert_record(
                self.loc(expr.exp_loc),
                fields,
                extended_expression.as_deref(),
            ),
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
                    crate::lambda::compat::SetFieldDbgInfo::RecordSet(label_runtime_name(lbl)),
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
                    crate::parser::ast::DirectionFlag::Upto => crate::lambda::DirectionFlag::Upto,
                    crate::parser::ast::DirectionFlag::Downto => {
                        crate::lambda::DirectionFlag::Downto
                    }
                };
                Lambda::for_(var.clone(), start_lam, end_lam, dir, body_lam)
            }
            ExpressionDesc::Texp_letmodule(_, _, _, body) => self.convert_expr(body),
            ExpressionDesc::Texp_letexception(_, body) => self.convert_expr(body),
            ExpressionDesc::Texp_assert(inner_expr) => {
                let cond = self.convert_expr(inner_expr);
                let failure = self.match_failure(self.loc(inner_expr.exp_loc));
                Lambda::if_(cond, Lambda::unit(), failure)
            }
            _ => {
                trace_raw_fallback(Self::expr_desc_name(&expr.exp_desc));
                self.lowered.convert_expr(expr)
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
            ExpressionDesc::Texp_field(_, _, _) => "Texp_field",
            ExpressionDesc::Texp_setfield(_, _, _, _) => "Texp_setfield",
            ExpressionDesc::Texp_array(_) => "Texp_array",
            ExpressionDesc::Texp_ifthenelse(_, _, _) => "Texp_ifthenelse",
            ExpressionDesc::Texp_sequence(_, _) => "Texp_sequence",
            ExpressionDesc::Texp_while(_, _) => "Texp_while",
            ExpressionDesc::Texp_for(_, _, _, _, _, _) => "Texp_for",
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
                delim: delim.as_ref().and_then(|d| match d.as_str() {
                    "`" => Some(StringDelim::Backtick),
                    _ => None,
                }),
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
                PatternDesc::Tpat_construct(_, cstr, args) => {
                    match &cstr.cstr_tag {
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
                    }
                }
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
                    default_case = Some(DefaultCase::Bind(id.clone(), self.convert_expr(&case.c_rhs)));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case = Some(DefaultCase::Bind(id.clone(), self.convert_expr(&case.c_rhs)));
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
                let scrut_id = self.id_gen.create("match");
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
                                &scrut_id,
                                pat,
                                cstr,
                                args,
                                body,
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
                    default_case =
                        Some(DefaultCase::Bind(id.clone(), self.convert_expr_raw(&case.c_rhs)));
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
                let scrut_id = self.id_gen.create(&scrut_name);
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
            if (repeated || failaction.as_ref().is_some_and(|default| self.raw_lambda_key(default) == key))
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
            if let Some((_, exit_id)) = shared_ids.iter().find(|(key, _)| *key == self.raw_lambda_key(&act)) {
                cases_with_exits.push((s, RawLambda::LstaticRaise(*exit_id, Vec::new())));
            } else {
                cases_with_exits.push((s, act));
            }
        }

        let default = failaction.map(|act| {
            if let Some((_, exit_id)) =
                shared_ids.iter().find(|(key, _)| *key == self.raw_lambda_key(&act))
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
            result = RawLambda::LstaticCatch(Box::new(result), (exit_id, Vec::new()), Box::new(handler));
        }

        Some(match wrap_let {
            Some((id, value)) => RawLambda::let_(LetKind::Strict, id, value, result),
            None => result,
        })
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
        Some(self.bind_irrefutable_pattern_raw(&cases[0].c_lhs, scrut_lam, body))
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
                    .unwrap_or_else(|| self.id_gen.create("match"));
                let bound = self.bind_irrefutable_pattern_raw(pat, RawLambda::var(id.clone()), body);
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
        let mut result = body;
        for (idx, arg_pat) in args.iter().enumerate().rev() {
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
                    let act = wrap_aliases_raw(
                        &aliases,
                        RawLambda::var(exn_id.clone()),
                        self.bind_extension_args_trywith_raw(
                            exn_id,
                            args,
                            body,
                            self.loc(pat.pat_loc),
                        ),
                    );
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

        let reraise = RawLambda::prim(
            Primitive::Praise,
            vec![RawLambda::var(exn_id.clone())],
            loc,
        );

        let default = match default_case {
            Some(DefaultCase::Any(body)) => body,
            Some(DefaultCase::Bind(id, body)) => RawLambda::let_(
                LetKind::Alias,
                id,
                RawLambda::var(exn_id.clone()),
                body,
            ),
            None => RawLambda::LstaticRaise(self.next_raise_count(), Vec::new()),
        };

        let exit_id = match &default {
            RawLambda::LstaticRaise(id, args) if args.is_empty() => Some(*id),
            _ => None,
        };

        let tests = extension_cases
            .into_iter()
            .rev()
            .fold(default, |rem, (path, act)| {
                let tag_id = self.id_gen.create("tag");
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
                    RawLambda::LifThenElse(Box::new(cond), Box::new(act), Box::new(rem)),
                )
            });

        Some(match exit_id {
            Some(exit_id) => RawLambda::LstaticCatch(
                Box::new(tests),
                (exit_id, Vec::new()),
                Box::new(reraise),
            ),
            None => tests,
        })
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
                    self.bind_irrefutable_pattern_raw(arg_pat, RawLambda::var(scrut_id.clone()), body)
                }
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
                    .unwrap_or(Primitive::PvalFromOption);
                let payload =
                    RawLambda::prim(from_option, vec![RawLambda::var(scrut_id.clone())], pat_loc);
                // For Tpat_any, OCaml's matching.ml still creates a binding
                if matches!(arg_pat.pat_desc, PatternDesc::Tpat_any) {
                    let match_id = self.id_gen.create("match");
                    result = RawLambda::let_(LetKind::Alias, match_id, payload, result);
                } else {
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
                    unreachable!("constructor payload binding only applies to non-constant constructors")
                }
            };
            // For Tpat_any, OCaml's matching.ml still creates a binding
            // (let (match/N =a (field:var/K scrut)) body). Match this behavior.
            if matches!(arg_pat.pat_desc, PatternDesc::Tpat_any) {
                let match_id = self.id_gen.create("match");
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
        let mut const_cases = Vec::<(i32, RawLambda)>::new();
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
                        tag,
                        wrap_aliases_raw(&aliases, RawLambda::const_(Constant::Pointer(format!("{tag}a"))), body),
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
                PatternDesc::Tpat_alias(inner, id, _) if matches!(inner.pat_desc, PatternDesc::Tpat_any) => {
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
            Some(DefaultCase::Bind(id, body)) => Some(RawLambda::let_(
                LetKind::Alias,
                id,
                scrut_lam.clone(),
                body,
            )),
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
            cases_to_test.0.into_iter().rev().fold(cases_to_test.1, |else_, (tag, body)| {
                RawLambda::LifThenElse(
                    Box::new(RawLambda::prim(
                        Primitive::Pjscomp(Comparison::Eq),
                        vec![
                            scrut_lam.clone(),
                            RawLambda::const_(Constant::Pointer(format!("{tag}a"))),
                        ],
                        loc,
                    )),
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
        self.compile_simple_constructor_match_raw_from_scrut(
            loc,
            scrut_lam,
            cases,
            partial,
        )
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
                        seen_block_tags.insert(*tag)
                            && args.iter().all(Self::is_irrefutable_pattern)
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
            _ => Self::check_simple_constructor_leaf(
                inner,
                seen_const_tags,
                seen_block_tags,
                seen_extensions,
                repr_cstr,
                has_non_ctor_constants,
            ),
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
                        wrap_aliases_raw(
                            &aliases,
                            RawLambda::var(scrut_id.clone()),
                            act,
                        ),
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
                    default_case =
                        Some(DefaultCase::Bind(id.clone(), self.convert_expr_raw(&case.c_rhs)));
                }
                PatternDesc::Tpat_alias(inner, id, _)
                    if matches!(inner.pat_desc, PatternDesc::Tpat_any) =>
                {
                    if default_case.is_some() {
                        return None;
                    }
                    default_case =
                        Some(DefaultCase::Bind(id.clone(), self.convert_expr_raw(&case.c_rhs)));
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
                let scrut_id = self.id_gen.create(&scrut_name);
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
                                &scrut_id,
                                pat,
                                cstr,
                                args,
                                body,
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

            let tests = remaining_cases.into_iter().rev().fold(default, |rem, (path, act)| {
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
                            wrap_aliases_raw(
                                &aliases,
                                RawLambda::var(scrut_id.clone()),
                                body,
                            ),
                        )),
                        ConstructorTag::CstrBlock(tag) => {
                            // Skip field extraction if all args are wildcards and there's a guard
                            // (OCaml doesn't extract unused fields for guarded cases)
                            let all_wildcards = args.iter().all(|a| matches!(a.pat_desc, PatternDesc::Tpat_any));
                            let block_body = if case.c_guard.is_some() && all_wildcards {
                                body
                            } else {
                                self.bind_constructor_args_irrefutably_raw(
                                    &scrut_id,
                                    pat,
                                    cstr,
                                    args,
                                    body,
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
                        ConstructorTag::CstrUnboxed | ConstructorTag::CstrExtension(_) => {}
                    },
                    PatternDesc::Tpat_constant(TConstant::Int(i)) => {
                        const_cases.push((
                            *i as i32,
                            wrap_aliases_raw(
                                &aliases,
                                RawLambda::var(scrut_id.clone()),
                                body,
                            ),
                        ));
                    }
                    PatternDesc::Tpat_constant(TConstant::Char(c)) => {
                        const_cases.push((
                            *c as i32,
                            wrap_aliases_raw(
                                &aliases,
                                RawLambda::var(scrut_id.clone()),
                                body,
                            ),
                        ));
                    }
                    _ => {}
                }
            }
        }

        // OCaml's combine_constructor: when sig_complete (all constructor tags covered),
        // fail_opt = None (no failaction). The wildcard/default fills missing tags explicitly.
        let failaction = match default_case {
            Some(default) => {
                let default_body = match default {
                    DefaultCase::Any(body) => body,
                    DefaultCase::Bind(id, body) => RawLambda::let_(
                        LetKind::Alias,
                        id,
                        RawLambda::var(scrut_id.clone()),
                        body,
                    ),
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
                Partial::Partial => Some(Box::new(RawLambda::from_lowered(self.match_failure(
                    loc.clone(),
                )))),
                Partial::Total => None,
            },
        };

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
                let offset_arg = if first == 0 {
                    scrut_var.clone()
                } else {
                    RawLambda::prim(
                        Primitive::Poffsetint(-first),
                        vec![scrut_var.clone()],
                        loc,
                    )
                };
                let is_out = RawLambda::prim(
                    Primitive::Pisout(last - first),
                    vec![offset_arg],
                    loc,
                );

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
                            sw_consts_full: false,
                            sw_consts: sorted_consts,
                            sw_blocks_full: false,
                            sw_blocks: Vec::new(),
                            sw_failaction: None,
                            sw_names: None,
                        },
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
                    (1, 1, [(0, act1)], [(0, act2)], _) if
                        cstr.cstr_name == "::"
                            || cstr.cstr_name == "[]"
                            || constructor_has_optional_shape(cstr) =>
                    {
                        let cond = if constructor_has_optional_shape(cstr) {
                            RawLambda::prim(
                                Primitive::PisNotNone,
                                vec![scrut_var.clone()],
                                loc,
                            )
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
            result = RawLambda::LstaticCatch(
                Box::new(result),
                (exit_id, Vec::new()),
                Box::new(handler),
            );
        }

        Some(match wrap_let {
            Some((id, value)) => RawLambda::let_(LetKind::Strict, id, value, result),
            None => result,
        })
    }

    fn compile_irrefutable_match(
        &mut self,
        scrut: &Expression,
        cases: &[Case],
    ) -> Option<Lambda> {
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
        let tmp = self.id_gen.create("ctor");
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
                    unreachable!("constructor payload binding only applies to non-constant constructors")
                }
            };
            result = self.bind_irrefutable_pattern(arg_pat, field, result);
        }

        Lambda::let_(LetKind::Alias, tmp, Lambda::var(scrut_id.clone()), result)
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
            PatternDesc::Tpat_construct(_, cstr, args) => {
                match cstr.cstr_tag {
                    ConstructorTag::CstrUnboxed => args.iter().all(Self::is_irrefutable_pattern),
                    ConstructorTag::CstrConstant(_) => {
                        args.is_empty()
                            && cstr.cstr_consts == 1
                            && cstr.cstr_nonconsts == 0
                    }
                    ConstructorTag::CstrBlock(_) => {
                        cstr.cstr_consts == 0
                            && cstr.cstr_nonconsts == 1
                            && args.iter().all(Self::is_irrefutable_pattern)
                    }
                    ConstructorTag::CstrExtension(_) => false,
                }
            }
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
                let tmp = self.id_gen.create("tuple");
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
                let tmp = self.id_gen.create("match");
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
                let tmp = self.id_gen.create("array");
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
            PatternDesc::Tpat_var(id, _) => RawLambda::let_(LetKind::Alias, id.clone(), scrut, body),
            PatternDesc::Tpat_alias(inner, id, _) => {
                let inner = self.bind_irrefutable_pattern_raw(inner, scrut.clone(), body);
                RawLambda::let_(LetKind::Alias, id.clone(), scrut, inner)
            }
            PatternDesc::Tpat_tuple(items) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.id_gen.create("match");
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
                    result = self.bind_irrefutable_pattern_raw(item, field, result);
                }
                match wrap_tmp {
                    // OCaml: make_tuple_matching binds tuple element accesses with Alias
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_record(fields, _) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.id_gen.create("match");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let mut result = body;
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
                    // OCaml: matching uses StrictOpt for mutable fields, Alias for immutable
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
                match wrap_tmp {
                    // OCaml: make_record_matching binds field accesses with Alias (immutable)
                    // or StrictOpt (mutable). When we wrap a sub-record scrutinee that came
                    // from a field access, use Alias to match OCaml's arg_to_var behavior.
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_array(items) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.id_gen.create("array");
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
                        let id = self.id_gen.create("match");
                        (id.clone(), Some((id, scrut)))
                    }
                };
                let result = self.bind_constructor_args_irrefutably_raw(
                    &scrut_id, pat, cstr, args, body,
                );
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

    fn raw_simple_for_let(&mut self, pat: &Pattern, param: RawLambda, body: RawLambda) -> RawLambda {
        match &pat.pat_desc {
            PatternDesc::Tpat_any => RawLambda::seq(param, body),
            PatternDesc::Tpat_var(id, _) => RawLambda::let_(LetKind::Strict, id.clone(), param, body),
            _ => {
                match param {
                    RawLambda::Lvar(_) => self.bind_irrefutable_pattern_raw(pat, param, body),
                    _ => {
                        let match_id = self.id_gen.create("match");
                        let body =
                            self.bind_irrefutable_pattern_raw(pat, RawLambda::var(match_id.clone()), body);
                        RawLambda::let_(LetKind::Strict, match_id, param, body)
                    }
                }
            }
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
            .map(|idx| self.id_gen.create(&format!("match{idx}")))
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
                let tuple_id = self.id_gen.create("tuple");
                let tuple_var = Lambda::var(tuple_id.clone());
                let with_fields = ids.iter().enumerate().rev().fold(body, |acc, (idx, id)| {
                    let field = Lambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![tuple_var.clone()],
                        loc.clone(),
                    );
                    Lambda::let_(LetKind::Alias, id.clone(), field, acc)
                });
                Lambda::let_(LetKind::Strict, tuple_id, self.convert_expr(scrut), with_fields)
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
            .map(|_| self.id_gen.create("match"))
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
                    RawLambda::let_(LetKind::Strict, id.clone(), self.convert_expr_raw(item), acc)
                }),
            _ => {
                let tuple_id = self.id_gen.create("tuple");
                let tuple_var = RawLambda::var(tuple_id.clone());
                let with_fields = ids.iter().enumerate().rev().fold(body, |acc, (idx, id)| {
                    let field = RawLambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![tuple_var.clone()],
                        loc,
                    );
                    RawLambda::let_(LetKind::Alias, id.clone(), field, acc)
                });
                RawLambda::let_(LetKind::Strict, tuple_id, self.convert_expr_raw(scrut), with_fields)
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
            return self.compile_simple_tuple_components(loc, ids, &default_states, idx + 1, partial);
        }

        let mut sw_consts = Vec::new();
        for key in const_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat) || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch =
                self.compile_simple_tuple_components(loc.clone(), ids, &branch_states, idx + 1, partial)?;
            sw_consts.push((key.tag(), branch));
        }

        let mut sw_blocks = Vec::new();
        for key in block_keys {
            let branch_states = states
                .iter()
                .filter(|state| {
                    let pat = state.case.items[idx];
                    Self::is_default_pattern(pat) || Self::simple_switch_key(pat).as_ref() == Some(&key)
                })
                .cloned()
                .map(|mut state| {
                    state.selected.push((idx, state.case.items[idx]));
                    state
                })
                .collect::<Vec<_>>();
            let branch =
                self.compile_simple_tuple_components(loc.clone(), ids, &branch_states, idx + 1, partial)?;
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
            return self.compile_simple_tuple_components_raw(loc, ids, &default_states, idx + 1, partial);
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
            let branch =
                self.compile_simple_tuple_components_raw(loc, ids, &branch_states, idx + 1, partial)?;
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
            let branch =
                self.compile_simple_tuple_components_raw(loc, ids, &branch_states, idx + 1, partial)?;
            sw_blocks.push((key.tag(), branch));
        }

        let failaction = if default_states.is_empty() {
            match partial {
                Partial::Partial => Some(Box::new(RawLambda::from_lowered(self.match_failure(loc)))),
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
                sw_consts_full: false,
                sw_consts,
                sw_blocks_full: false,
                sw_blocks,
                sw_failaction: failaction,
                sw_names: None,
            },
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
                ConstructorTag::CstrUnboxed => self.bind_irrefutable_pattern(inner, scrut.clone(), body),
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
        fields: &[(Located<LidentIdx>, LabelDescription, RecordLabelDefinition, bool)],
        base: Option<&Expression>,
    ) -> Lambda {
        let mut values = vec![None; fields.len()];
        let base_lam = base.map(|e| self.convert_expr(e));

        for (idx, (lid, lbl, def, _opt)) in fields.iter().enumerate() {
            let value = match def {
                RecordLabelDefinition::Overridden(_, expr) => self.convert_expr(expr),
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
        if let Some(lam) = self.lowered.value_path_loc_constant(path, loc_idx) {
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
                    return RawLambda::from_lowered(
                        self.lowered
                            .convert_let_with_body(rec_flag, bindings, body.into_lowered()),
                    );
                }

                let mut acc = body;
                for binding in bindings.iter().rev() {
                    let mut value = self.convert_expr_raw(&binding.vb_expr);
                    // OCaml's transl_let applies inline attributes from vb_attributes
                    let inline_attr =
                        Self::get_inline_attribute_from(&binding.vb_attributes, self.arena);
                    value = Self::apply_inline_attribute_raw(value, inline_attr);
                    if let Some(id) = simple_let_binding_id(binding) {
                        // OCaml's Matching.for_let uses Strict for Tpat_var(id).
                        // For Tpat_alias(Tpat_any, id, _), compile_matching produces
                        // Alias when the RHS is a variable, Strict otherwise (because
                        // arg_to_var + bind_check wrap non-var args in Strict let).
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
                        acc = self.raw_simple_for_let(&binding.vb_pat, value, acc);
                    }
                }
                acc
            }
            crate::parser::ast::RecFlag::Recursive => {
                if bindings.iter().all(|binding| simple_let_binding_id(binding).is_some()) {
                    let lam_bindings = bindings
                        .iter()
                        .map(|binding| {
                            let mut value = self.convert_expr_raw(&binding.vb_expr);
                            let inline_attr =
                                Self::get_inline_attribute_from(&binding.vb_attributes, self.arena);
                            value = Self::apply_inline_attribute_raw(value, inline_attr);
                            (
                                simple_let_binding_id(binding).expect("checked above"),
                                value,
                            )
                        })
                        .collect();
                    RawLambda::letrec(lam_bindings, body)
                } else {
                    RawLambda::from_lowered(
                        self.lowered
                            .convert_let_with_body(rec_flag, bindings, body.into_lowered()),
                    )
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
        for (param, id) in all_params.iter().zip(param_ids.iter()).rev() {
            let pat = Self::param_pattern(param);
            body = match &pat.pat_desc {
                PatternDesc::Tpat_any => body,
                PatternDesc::Tpat_var(bound, _) if bound.same(id) => body,
                PatternDesc::Tpat_alias(_, bound, _) if bound.same(id) => body,
                _ if Self::is_irrefutable_pattern(&pat) => {
                    self.raw_simple_for_let(&pat, RawLambda::var(id.clone()), body)
                }
                _ => body,
            };
        }
        let lambda = RawLambda::function_(
            param_ids.len() as i32,
            param_ids,
            body,
            FunctionAttribute {
                return_unit,
                async_,
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

    fn convert_apply_raw(
        &mut self,
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
                    && args.iter().take(prim_arity).all(|arg| arg.expression.is_some())
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
                            self.transl_apply_raw(base, rest, loc, transformed_jsx, None)
                        };
                    }
                    let base = RawLambda::prim(
                        self.translate_primitive_application_raw(
                            prim,
                            funct.exp_type,
                            &applied_exprs,
                            transformed_jsx,
                        ),
                        applied_exprs
                            .iter()
                            .map(|expr| self.convert_expr_raw(expr))
                            .collect(),
                        loc,
                    );
                    return if rest.is_empty() {
                        base
                    } else {
                        self.transl_apply_raw(base, rest, loc, transformed_jsx, None)
                    };
                }
            }
        }

        let funct_lam = self.convert_expr_raw(funct);
        let uncurried_partial_application = if partial {
            self.env_for_expr(funct).and_then(|env| {
                self.get_function_arity_from_type(env.as_ref(), funct.exp_type)
                    .and_then(|arity| {
                        let real_args = args.iter().filter(|arg| arg.expression.is_some()).count() as i32;
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
                PatternDesc::Tpat_alias(_, id, _) => id.clone(),
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

    fn transl_apply_raw(
        &mut self,
        lam: RawLambda,
        sargs: &[ApplyArg],
        loc: Location,
        transformed_jsx: bool,
        uncurried_partial_application: Option<i32>,
    ) -> RawLambda {
        fn lapply(
            loc: Location,
            func: RawLambda,
            args: Vec<RawLambda>,
            transformed_jsx: bool,
        ) -> RawLambda {
            RawLambda::Lapply(crate::raw_lambda::RawApply {
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

        fn is_simple(lam: &RawLambda) -> bool {
            matches!(lam, RawLambda::Lvar(_) | RawLambda::Lconst(_))
        }

        fn may_map<T, U, F>(value: Option<T>, f: F) -> Option<U>
        where
            F: FnOnce(T) -> U,
        {
            value.map(f)
        }

        fn build_apply(
            conv: &mut RawLambdaConverter<'_>,
            lam: RawLambda,
            mut args_rev: Vec<(RawLambda, bool)>,
            pending: &[(Option<RawLambda>, bool)],
            loc: Location,
            transformed_jsx: bool,
        ) -> RawLambda {
            match pending.split_first() {
                Some(((None, optional), tail)) => {
                    let mut defs: Vec<(Ident, RawLambda)> = Vec::new();
                    let protect = |conv: &mut RawLambdaConverter<'_>,
                                   name: &str,
                                   lam: RawLambda,
                                   defs: &mut Vec<(Ident, RawLambda)>| {
                        if is_simple(&lam) {
                            lam
                        } else {
                            let id = conv.id_gen.create(name);
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
                    let id_arg = conv.id_gen.create("param");
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
                    ) {
                        RawLambda::Lfunction(func) => RawLambda::Lfunction(crate::raw_lambda::RawLFunction {
                            arity: func.arity + 1,
                            params: std::iter::once(id_arg).chain(func.params).collect(),
                            body: func.body,
                            attr: func.attr,
                        }),
                        lam => RawLambda::function_(
                            1,
                            vec![id_arg],
                            lam,
                            FunctionAttribute::default(),
                        ),
                    };
                    defs.into_iter().fold(body, |body, (id, lam)| {
                        RawLambda::let_(LetKind::Strict, id, lam, body)
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

        match uncurried_partial_application {
            Some(arity) => {
                let extra_arity = arity - sargs.len() as i32;
                let mut none_ids = Vec::new();
                let args = sargs
                    .iter()
                    .filter_map(|arg| match &arg.expression {
                        Some(expr) => Some(self.convert_expr_raw(expr)),
                        None => {
                            let id = self.id_gen.create("none");
                            none_ids.push(id.clone());
                            Some(RawLambda::var(id))
                        }
                    })
                    .collect::<Vec<_>>();
                let extra_ids = (0..extra_arity)
                    .map(|_| self.id_gen.create("extra"))
                    .collect::<Vec<_>>();
                let mut ap_args = args;
                ap_args.extend(extra_ids.iter().cloned().map(RawLambda::var));
                let body = lapply(loc.clone(), lam, ap_args, transformed_jsx);
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
                            may_map(arg.expression.clone(), |expr| self.convert_expr_raw(&expr)),
                            arg.label.is_optional(),
                        )
                    })
                    .collect::<Vec<_>>();
                build_apply(self, lam, Vec::new(), &pending, loc, transformed_jsx)
            }
        }
    }

    fn translate_primitive_raw(
        &mut self,
        loc: Location,
        prim: &crate::types::PrimitiveDescription,
        ty: TypeExprRef,
    ) -> RawLambda {
        let raw_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some(kind) = Self::raw_loc_kind(raw_name) {
            let lam = self.raw_loc_constant(kind, loc);
            return match prim.prim_arity {
                0 => lam,
                1 => {
                    let param = self.id_gen.create("prim");
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
        let primitive = if let Some(primitive) = self.specialize_primitive_raw(prim, ty) {
            primitive
        } else {
            Primitive::PjsCall {
                prim_name: raw_name.to_string(),
                arg_types: vec![ExternalArgSpec { label: None }; prim.prim_arity.max(0) as usize],
                ffi: ExternalFfiSpec { module_name: None },
                dynamic_import: false,
                transformed_jsx: false,
            }
        };

        if prim.prim_arity == 0 {
            RawLambda::prim(primitive, vec![], loc)
        } else {
            let params = if prim.prim_arity == 1 {
                vec![self.id_gen.create("prim")]
            } else {
                let mut params = (0..prim.prim_arity)
                    .rev()
                    .map(|i| self.id_gen.create(&format!("prim{i}")))
                    .collect::<Vec<_>>();
                params.reverse();
                params
            };
            let args = params.iter().cloned().map(RawLambda::var).collect::<Vec<_>>();
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
        let primitive = self.translate_primitive_application(prim, false);
        if prim.prim_arity == 0 {
            Lambda::prim(primitive, vec![], loc)
        } else {
            let params = if prim.prim_arity == 1 {
                vec![self.id_gen.create("prim")]
            } else {
                let mut params = (0..prim.prim_arity)
                    .rev()
                    .map(|i| self.id_gen.create(&format!("prim{i}")))
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
        &self,
        prim: &crate::types::PrimitiveDescription,
        transformed_jsx: bool,
    ) -> Primitive {
        let raw_name = Self::raw_primitive_name(&prim.prim_name);
        if let Some(primitive) = self.lowered.primitive_from_name(raw_name) {
            primitive
        } else {
            Primitive::PjsCall {
                prim_name: raw_name.to_string(),
                arg_types: vec![ExternalArgSpec { label: None }; prim.prim_arity.max(0) as usize],
                ffi: ExternalFfiSpec { module_name: None },
                dynamic_import: false,
                transformed_jsx,
            }
        }
    }

    fn raw_primitive_name(name: &str) -> &str {
        name.strip_suffix("[js]").unwrap_or(name)
    }
}
