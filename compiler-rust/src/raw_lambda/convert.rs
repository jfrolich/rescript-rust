//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use std::collections::{BTreeSet, HashSet};
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
    ApInfo, Apply, ApplyStatus, FieldDbgInfo, FunctionAttribute, InlineAttribute, Lambda,
    LambdaSwitch, Primitive,
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

fn predef_exception_ident(name: &str, stamp: i32) -> Ident {
    Ident::new(name, stamp, IdentFlags::PREDEF_EXN.with_global())
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

fn id_of_pattern(pat: &Pattern) -> Option<Ident> {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => Some(id.clone()),
        PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => match &args[0].pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => Some(id.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn name_pattern(default: &str, cases: &[Case]) -> Option<Ident> {
    cases.iter().find_map(|case| id_of_pattern(&case.c_lhs)).or_else(|| {
        if cases.is_empty() {
            None
        } else {
            Some(Ident::create_persistent(default))
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

    fn fresh_name_from_cases(&self, default: &str, cases: &[Case]) -> String {
        name_pattern(default, cases)
            .map(|id| id.name().to_string())
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
            _ => self.lowered.primitive_from_name(prim_name),
        }
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
            ConstructorTag::CstrExtension(_) => unreachable!(
                "extension constructors stay on the lowered path for now"
            ),
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
        let normalized = self.normalize_value_path_in_env(self.env, path);
        self.translate_normal_path_raw(&normalized, loc)
    }

    fn translate_value_path_raw_in_env(
        &mut self,
        env: &crate::types::env::Env,
        path: &crate::types::Path,
        loc: Location,
    ) -> RawLambda {
        let normalized = self.normalize_value_path_in_env(env, path);
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

    fn make_module_block_raw(
        &mut self,
        fields: &[Ident],
        is_top_level: bool,
        cc: &ModuleCoercion,
        loc: Location,
    ) -> RawLambda {
        fn apply_coercion_raw(
            this: &mut RawLambdaConverter<'_>,
            coercion: &ModuleCoercion,
            arg: RawLambda,
            loc: Location,
        ) -> RawLambda {
            match coercion {
                ModuleCoercion::Tcoerce_none => arg,
                ModuleCoercion::Tcoerce_alias(_, path, inner) => {
                    let alias = this.translate_module_path_raw(path, loc);
                    apply_coercion_raw(this, inner, alias, loc)
                }
                ModuleCoercion::Tcoerce_structure(positions, _, runtime_fields) => {
                    let block_fields = positions
                        .iter()
                        .map(|(pos, field_cc)| {
                            let field = RawLambda::prim(
                                Primitive::Pfield(
                                    *pos as i32,
                                    FieldDbgInfo::Module {
                                        name: runtime_fields
                                            .get(*pos)
                                            .cloned()
                                            .unwrap_or_else(|| format!("field{pos}")),
                                    },
                                ),
                                vec![arg.clone()],
                                loc,
                            );
                            apply_coercion_raw(this, field_cc, field, loc)
                        })
                        .collect::<Vec<_>>();
                    RawLambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::Module(runtime_fields.clone()),
                            Mutable::Immutable,
                        ),
                        block_fields,
                        loc,
                    )
                }
                _ => arg,
            }
        }

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
            ModuleCoercion::Tcoerce_structure(positions, _, runtime_fields) => {
                let block_fields = positions
                    .iter()
                    .filter_map(|(pos, field_cc)| {
                        fields.get(*pos).cloned().map(|id| {
                            apply_coercion_raw(self, field_cc, RawLambda::var(id), loc)
                        })
                    })
                    .collect::<Vec<_>>();
                let tag = if is_top_level {
                    let ids = positions
                        .iter()
                        .filter_map(|(pos, _)| fields.get(*pos).cloned())
                        .collect::<Vec<_>>();
                    TagInfo::ModuleExport(ids)
                } else {
                    TagInfo::Module(
                        positions
                            .iter()
                            .filter_map(|(pos, _)| {
                                fields.get(*pos).map(|id| id.name().to_string())
                            })
                            .collect(),
                    )
                };
                RawLambda::prim(
                    Primitive::Pmakeblock(0, tag, Mutable::Immutable),
                    block_fields,
                    loc,
                )
            }
            _ => {
                let block_fields = fields
                    .iter()
                    .cloned()
                    .map(|id| apply_coercion_raw(self, cc, RawLambda::var(id), loc))
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
            return RawLambda::const_(Constant::ModuleAlias);
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
                if let Some(env) = self.env_for_module_expr(module_expr) {
                    self.translate_module_path_raw_in_env(env.as_ref(), path, self.loc(module_expr.mod_loc))
                } else {
                    self.translate_module_path_raw(path, self.loc(module_expr.mod_loc))
                }
            }
            ModuleExprDesc::Tmod_unpack(expr, _) => self.convert_expr_raw(expr),
            ModuleExprDesc::Tmod_apply(_, _, _) | ModuleExprDesc::Tmod_functor(_, _, _, _) => {
                RawLambda::from_lowered(self.convert_module_expr(module_expr))
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
                RawLambda::let_(
                    Self::pure_module(&binding.mb_expr),
                    binding.mb_id.clone(),
                    self.convert_module_expr_raw(
                        &binding.mb_expr,
                        &Self::field_path(rootpath, &binding.mb_id),
                    ),
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
            StructureItemDesc::Tstr_primitive(_)
            | StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_recmodule(_)
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
                self.convert_function_raw(
                    params,
                    body,
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
                .compile_irrefutable_match(scrut, cases)
                .map(RawLambda::from_lowered)
                .or_else(|| {
                    self.compile_simple_string_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                })
                .or_else(|| {
                    self.compile_simple_tuple_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                        .map(RawLambda::from_lowered)
                })
                .or_else(|| {
                    self.compile_simple_constructor_match(self.loc(expr.exp_loc), scrut, cases, *partial)
                        .map(RawLambda::from_lowered)
                })
                .unwrap_or_else(|| {
                    trace_raw_match_fallback(&self.loc(expr.exp_loc), scrut, cases);
                    RawLambda::from_lowered(self.lowered.convert_expr(expr))
                }),
            ExpressionDesc::Texp_tuple(items) => {
                let elems = items
                    .iter()
                    .map(|item| self.convert_expr_raw(item))
                    .collect::<Vec<_>>();
                self.raw_block_or_prim(0, TagInfo::Tuple, elems, self.loc(expr.exp_loc))
            }
            ExpressionDesc::Texp_construct(_, cstr, args) => match &cstr.cstr_tag {
                ConstructorTag::CstrExtension(path) => {
                    let mut args_lam = Vec::with_capacity(args.len() + 1);
                    args_lam.push(self.translate_extension_path_raw(path, self.loc(expr.exp_loc)));
                    args_lam.extend(args.iter().map(|arg| self.convert_expr_raw(arg)));
                    RawLambda::prim(
                        Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
                        args_lam,
                        self.loc(expr.exp_loc),
                    )
                }
                _ => self.convert_construct_raw(self.loc(expr.exp_loc), cstr, args),
            },
            ExpressionDesc::Texp_variant(tag, arg) => match arg {
                None => RawLambda::const_(Constant::Pointer(tag.to_string())),
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
                    crate::lambda::compat::SetFieldDbgInfo::RecordSet(lbl.lbl_name.clone()),
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
            TConstant::BigInt(neg, v) => Constant::BigInt {
                negative: *neg,
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
                matches!(cstr.cstr_tag, ConstructorTag::CstrUnboxed)
                    && args.iter().all(Self::is_irrefutable_pattern)
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
                let tmp = self.id_gen.create("record");
                let mut result = body;
                for (lid, lbl, inner_pat, _) in fields.iter().rev() {
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
                        let tmp = self.id_gen.create("tuple");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate().rev() {
                    let field = RawLambda::prim(
                        Primitive::Pfield(idx as i32, FieldDbgInfo::Tuple),
                        vec![RawLambda::var(tmp.clone())],
                        pat_loc,
                    );
                    result = self.bind_irrefutable_pattern_raw(item, field, result);
                }
                match wrap_tmp {
                    Some((tmp, scrut)) => RawLambda::let_(LetKind::Alias, tmp, scrut, result),
                    None => result,
                }
            }
            PatternDesc::Tpat_record(fields, _) => {
                let (tmp, wrap_tmp) = match scrut.clone() {
                    RawLambda::Lvar(id) => (id, None),
                    _ => {
                        let tmp = self.id_gen.create("record");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let mut result = body;
                for (lid, lbl, inner_pat, _) in fields.iter().rev() {
                    let field = RawLambda::prim(
                        Primitive::Pfield(
                            lbl.lbl_pos,
                            FieldDbgInfo::Record {
                                name: lbl.lbl_name.clone(),
                                mutable_flag: to_parser_mutable(lbl.lbl_mut),
                            },
                        ),
                        vec![RawLambda::var(tmp.clone())],
                        self.loc(lid.loc),
                    );
                    result = self.bind_irrefutable_pattern_raw(inner_pat, field, result);
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
                        let tmp = self.id_gen.create("array");
                        (tmp.clone(), Some((tmp, scrut)))
                    }
                };
                let pat_loc = self.loc(pat.pat_loc);
                let mut result = body;
                for (idx, item) in items.iter().enumerate().rev() {
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
                    let value = self.convert_expr_raw(&binding.vb_expr);
                    if let Some(id) = simple_let_binding_id(binding) {
                        acc = RawLambda::let_(LetKind::Strict, id, value, acc);
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
                            (
                                simple_let_binding_id(binding).expect("checked above"),
                                self.convert_expr_raw(&binding.vb_expr),
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
        for (idx, param) in all_params.iter().enumerate() {
            let pat = Self::param_pattern(param);
            let id = match &pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => id.clone(),
                PatternDesc::Tpat_alias(_, id, _) => id.clone(),
                _ if all_params.len() == 1 => self.id_gen.create("param"),
                _ => self.id_gen.create(&format!("param{idx}")),
            };
            param_ids.push(id);
        }

        let return_unit = final_body
            .map(|expr| self.is_base_type(expr.exp_type, "unit"))
            .unwrap_or(false);
        let body = final_body
            .map(|expr| self.convert_expr_raw(expr))
            .unwrap_or_else(RawLambda::unit);
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
                let prim = if let Some((lhs, _)) = self.is_function_type(function_type) {
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
        _partial: bool,
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
                            self.transl_apply_raw(base, rest, loc, transformed_jsx)
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
                        self.transl_apply_raw(base, rest, loc, transformed_jsx)
                    };
                }
            }
        }

        let funct_lam = self.convert_expr_raw(funct);
        self.transl_apply_raw(funct_lam, args, loc, transformed_jsx)
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
            return RawLambda::const_(Constant::JsNull);
        }
        if raw_name == "%undefined" && prim.prim_arity == 0 {
            return RawLambda::const_(Constant::JsUndefined { is_unit: false });
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
