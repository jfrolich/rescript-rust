//! Typedtree -> Raw Lambda conversion.
//!
//! This stage ports the OCaml raw-lambda structure shape first and then
//! incrementally ports expression lowering from `translcore.ml`.

use std::collections::BTreeSet;
use std::sync::{Mutex, OnceLock};

use crate::context::IdGenerator;
use crate::ident::Ident;
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
use crate::types::asttypes::MutableFlag as TypeMutableFlag;
use crate::types::ConstructorTag;
use crate::types::decl::{LabelDescription, RecordRepresentation, ValueKind};
use crate::types::typedtree::{
    ApplyArg, Case, Constant as TConstant, Expression, ExpressionDesc, FunctionParam,
    FunctionParamPattern, ModuleExpr, ModuleExprDesc, Partial, Pattern, PatternDesc,
    RecordLabelDefinition, Structure, StructureItem, StructureItemDesc, ValueBinding,
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
        let mut fields = Vec::new();
        RawLambda::from_lowered(self.convert_structure_items(
            &mut fields,
            &structure.str_items,
            true,
        ))
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
            TConstant::Int(i) => Constant::Int {
                i: *i as i32,
                comment: None,
            },
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
        let msg = Lambda::const_(Constant::String {
            s: "Match_failure".to_string(),
            delim: None,
        });
        Lambda::prim(Primitive::Praise, vec![msg], loc)
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
