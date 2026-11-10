//! Port of `compiler/ml/parmatch.ml`: detection of partial matches, unused
//! match cases, fragile matches and ambiguous or-pattern bindings.
//!
//! OCaml builds and shares `Typedtree.pattern` values freely while exploring
//! pattern matrices. This port keeps the same algorithms over an arena of
//! pattern nodes (`P` indices) so sub-patterns are shared instead of cloned.
//! Nodes imported from the typed tree keep a reference to their source
//! pattern (for locations and attributes); nodes built by the algorithm
//! (`omega`, `set_args`, `build_other`, ...) carry the type and environment of
//! the pattern they were derived from, like OCaml's `make_pat`.
//!
//! Environment queries (type expansion, the constructors or labels of a type)
//! go through [`Oracle`], implemented by the type checker.

use std::borrow::Cow;

use crate::ident::Ident;
use crate::parse_arena::{LidentIdx, LocIdx};
use crate::parser::ast::ClosedFlag;
use crate::types::MutableFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorDescription, ConstructorKind, LabelArrayRef, LabelDescription, same_constructor,
};
use crate::types::path::Path;
use crate::types::type_expr::{RowField, TypeDesc, TypeExprRef};
use crate::types::typedtree::{
    Constant, EnvRef, Pattern, PatternDesc, TPatIdx, TPatList, TypedArena,
};

/// A pattern node in the matrix arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct P(u32);

/// Environment queries needed by the algorithms (`Env.find_type`,
/// `Env.find_type_descrs`, `Ctype.expand_head`, ...).
pub(crate) trait Oracle {
    fn ctx(&self) -> &TypeContext;
    /// `Ctype.expand_head env ty`, returned in representative form.
    fn expand_head(&mut self, env: EnvRef, ty: TypeExprRef) -> TypeExprRef;
    /// `get_variant_constructors env ty` (parmatch.ml:492-503): the
    /// constructors of the variant type, in declaration order.
    fn variant_constructors(&mut self, env: EnvRef, ty: TypeExprRef)
    -> Vec<ConstructorDescription>;
    /// The part of `pats_of_type` that needs `Env.find_type`
    /// (parmatch.ml:943-965).
    fn type_shape(&mut self, env: EnvRef, ty: TypeExprRef, always: bool) -> TypeShape;
    /// `Ident.create name`.
    fn create_ident(&mut self, name: &str) -> Ident;
    /// `close_variant env row` (parmatch.ml:872-894), where `row` is
    /// `row_of_pat` of the pattern with type `ty` in `pat_env`.
    fn close_variant(&mut self, env: EnvRef, pat_env: EnvRef, ty: TypeExprRef);
    /// Report a warning.
    fn warn(&mut self, loc: LocIdx, warning: ParmatchWarning);
    /// `Warnings.is_active w`.
    fn is_active(&self, warning: &ParmatchWarning) -> bool;
    /// Whether `loc` is a ghost location.
    fn is_ghost(&self, loc: LocIdx) -> bool;
    /// The arena counter-examples are stored in: [`Parmatch::export`] adds
    /// to it and [`Oracle::pred`] retypes from it. It is scratch space,
    /// separate from the arena holding the patterns being checked.
    fn scratch(&self) -> &TypedArena;
    fn scratch_mut(&mut self) -> &mut TypedArena;
    /// `!print_res_pat v` (Pattern_printer.print_pattern).
    fn print_pattern(&mut self, v: &Pattern) -> String;
    /// The type checker's `partial_pred` on `Conv.conv u`
    /// (typecore.ml:1743-1776): `None` when the counter-example does not type.
    fn pred(&mut self, kind: PredKind, u: Pattern, loc: Option<LocIdx>) -> Option<Pattern>;
    /// `Path.same path Predef.path_{bool,list,unit,option}`.
    fn is_non_extendable_predef_path(&self, path: &Path) -> bool;
    /// A longident to use for the `?temp?`/`?pat_of_constr?` placeholders.
    fn placeholder_lid(&self) -> LidentIdx;
    /// `Ctype.none`.
    fn none_type(&mut self) -> TypeExprRef;
    /// `(Ctype.expand_head env ty).desc` is the predefined `dict` type.
    fn is_dict_type(&mut self, env: EnvRef, ty: TypeExprRef) -> bool {
        let ty = self.expand_head(env, ty);
        matches!(
            &*self.ctx().get_desc(self.ctx().repr(ty)),
            TypeDesc::Tconstr { path, .. } if path.same(&crate::types::predef::path_dict())
        )
    }
    /// Whether pattern attributes include `res.patFromVariantSpread`.
    fn is_pat_from_variant_spread(&self, attrs: &crate::parser::ast::Attributes) -> bool;
    /// `Variant_runtime.length (Variant_runtime.get_layout variant)`.
    fn variant_length(&self, cstr: &ConstructorDescription) -> usize;
    /// `get_type_path ty tenv` (parmatch.ml:334-338).
    fn type_path(&mut self, env: EnvRef, ty: TypeExprRef) -> Path;
    /// `row_of_pat pat`: the static row of the pattern's expanded type.
    fn row_of(&mut self, env: EnvRef, ty: TypeExprRef) -> crate::types::type_expr::RowDesc;
}

/// Warnings emitted by the checks.
#[derive(Debug, Clone)]
pub(crate) enum ParmatchWarning {
    AllClausesGuarded,
    PartialMatch(String),
    FragileMatch(String),
    /// `Unused_match reason`; the reason is empty for an ordinary unused case.
    UnusedMatch(String),
    /// `Unused_pat reason`.
    UnusedPat(String),
    UnreachableCase,
    AmbiguousPattern(Vec<String>),
}

/// Which `partial_pred` the checks call back into.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PredKind {
    /// `check_partial`: `partial_pred ~explode` with `explode = 5` for a
    /// single case and `0` otherwise (typecore.ml:1761-1770).
    Partial,
    /// `check_unused`: `partial_pred ~mode:Split_or ~explode:5`.
    Unused,
}

/// A case as seen by the checks (`c_lhs`, whether `c_guard` is present).
#[derive(Clone, Copy)]
pub(crate) struct CaseRef<'a> {
    pub lhs: &'a Pattern,
    pub guarded: bool,
}

/// `Partial | Total`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Partiality {
    Partial,
    Total,
}

/// Result of the environment part of `pats_of_type`.
pub(crate) enum TypeShape {
    /// A variant whose constructors are all returned (`always`, a single
    /// constructor, or only GADT constructors).
    Variant(Vec<ConstructorDescription>),
    Record(Vec<LabelDescription>),
    Tuple(usize),
    Other,
}

#[derive(Debug, Clone)]
pub(crate) enum VarKind {
    /// A source variable (or alias) name.
    Source,
    /// `extra_pat`: `Tpat_var (Ident.create "+", mknoloc "+")`.
    Extra,
    /// The `*extension*` placeholder built by `build_other`, with the
    /// location of the constructor longident it replaces.
    Extension(Ident, LocIdx),
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub(crate) struct Field<'a> {
    /// The source label longident; `None` for the `?temp?`/`?pat_of_label?`
    /// fields built by the algorithm.
    pub lid: Option<crate::parse_arena::Located<LidentIdx>>,
    pub lbl: Cow<'a, LabelDescription>,
    pub pat: P,
    pub opt: bool,
}

#[derive(Debug, Clone)]
pub(crate) enum Desc<'a> {
    Any,
    Var(VarKind),
    Alias(P),
    Constant(Cow<'a, Constant>),
    /// `Tpat_interval (lo, hi)`: an int or char range.
    Interval(Constant, Constant),
    Tuple(Vec<P>),
    Construct {
        lid: Option<crate::parse_arena::Located<LidentIdx>>,
        /// Shared with the typed tree, so cloning a node stays cheap.
        cstr: std::sync::Arc<ConstructorDescription>,
        args: Vec<P>,
    },
    Variant {
        label: Cow<'a, str>,
        arg: Option<P>,
    },
    Record {
        fields: Vec<Field<'a>>,
        closed: ClosedFlag,
        has_rest: bool,
    },
    Array(Vec<P>),
    Or(P, P),
}

#[derive(Debug, Clone)]
pub(crate) struct Node<'a> {
    pub desc: Desc<'a>,
    /// `pat_type`; `None` for `Ctype.none`.
    pub ty: Option<TypeExprRef>,
    pub env: EnvRef,
    pub loc: LocIdx,
    /// The typed-tree pattern this node was imported from.
    pub src: Option<&'a Pattern>,
}

/// Pattern matrices (`pattern list list`).
pub(crate) type Row = Vec<P>;

/// The arena and algorithms.
pub(crate) struct Parmatch<'a, O: Oracle> {
    pub oracle: O,
    /// The arena of the patterns being checked ([`Parmatch::import`]).
    ta: &'a TypedArena,
    nodes: Vec<Node<'a>>,
    omega: P,
    extra: P,
    zero: P,
}

/// `Empty` (parmatch.ml:321): an empty or-pattern was requested.
#[derive(Debug)]
pub(crate) struct Empty;

impl<'a, O: Oracle> Parmatch<'a, O> {
    pub fn new(oracle: O, ta: &'a TypedArena) -> Self {
        let mut pm = Parmatch {
            oracle,
            ta,
            nodes: Vec::new(),
            omega: P(0),
            extra: P(0),
            zero: P(0),
        };
        pm.omega = pm.push(Desc::Any, None, EnvRef(0), LocIdx::none(), None);
        pm.extra = pm.push(
            Desc::Var(VarKind::Extra),
            None,
            EnvRef(0),
            LocIdx::none(),
            None,
        );
        pm.zero = pm.push(
            Desc::Constant(Cow::Owned(Constant::Int(0))),
            None,
            EnvRef(0),
            LocIdx::none(),
            None,
        );
        pm
    }

    /// `irrefutable pat` (parmatch.ml:2260): `le_pat pat omega`.
    pub fn irrefutable(&mut self, pat: &'a Pattern) -> bool {
        let p = self.import(pat);
        let omega = self.omega;
        self.le_pat(p, omega)
    }

    /// Whether the node is `Tpat_any`.
    pub fn is_any(&self, p: P) -> bool {
        matches!(self.desc(p), Desc::Any)
    }

    fn push(
        &mut self,
        desc: Desc<'a>,
        ty: Option<TypeExprRef>,
        env: EnvRef,
        loc: LocIdx,
        src: Option<&'a Pattern>,
    ) -> P {
        let id = P(self.nodes.len() as u32);
        self.nodes.push(Node {
            desc,
            ty,
            env,
            loc,
            src,
        });
        id
    }

    pub fn node(&self, p: P) -> &Node<'a> {
        &self.nodes[p.0 as usize]
    }

    fn desc(&self, p: P) -> &Desc<'a> {
        &self.node(p).desc
    }

    /// `make_pat desc ty tenv` (parmatch.ml:26-34): a fresh node with a ghost
    /// location and no attributes.
    fn make_pat(&mut self, desc: Desc<'a>, ty: Option<TypeExprRef>, env: EnvRef) -> P {
        self.push(desc, ty, env, LocIdx::none(), None)
    }

    /// `make_pat desc q.pat_type q.pat_env`.
    fn make_pat_like(&mut self, desc: Desc<'a>, like: P) -> P {
        let (ty, env) = (self.node(like).ty, self.node(like).env);
        self.make_pat(desc, ty, env)
    }

    /// `{p with pat_desc = desc}`: keeps location and source attributes.
    fn with_desc(&mut self, p: P, desc: Desc<'a>) -> P {
        let node = self.node(p).clone();
        self.push(desc, node.ty, node.env, node.loc, node.src)
    }

    fn omegas(&self, n: usize) -> Vec<P> {
        vec![self.omega; n]
    }

    /// Import a typed-tree pattern.
    pub fn import(&mut self, pat: &'a Pattern) -> P {
        let ta = self.ta;
        let desc = match &pat.pat_desc {
            PatternDesc::Tpat_any => Desc::Any,
            PatternDesc::Tpat_var(_, _) => Desc::Var(VarKind::Source),
            PatternDesc::Tpat_alias(inner, _, _) => Desc::Alias(self.import(ta.pattern(*inner))),
            PatternDesc::Tpat_constant(c) => Desc::Constant(Cow::Borrowed(c)),
            PatternDesc::Tpat_interval(lo, hi) => Desc::Interval(lo.constant(), hi.constant()),
            PatternDesc::Tpat_tuple(items) => {
                Desc::Tuple(ta.patterns(*items).map(|item| self.import(item)).collect())
            }
            PatternDesc::Tpat_construct(lid, cstr, args) => Desc::Construct {
                lid: Some(*lid),
                cstr: std::sync::Arc::clone(cstr),
                args: ta.patterns(*args).map(|arg| self.import(arg)).collect(),
            },
            PatternDesc::Tpat_variant(label, arg, _) => Desc::Variant {
                label: Cow::Borrowed(label.as_str()),
                arg: arg.map(|arg| self.import(ta.pattern(arg))),
            },
            PatternDesc::Tpat_record(fields, closed, rest) => Desc::Record {
                fields: fields
                    .iter()
                    .map(|(lid, lbl, p, opt)| Field {
                        lid: Some(*lid),
                        lbl: Cow::Borrowed(lbl),
                        pat: self.import(ta.pattern(*p)),
                        opt: *opt,
                    })
                    .collect(),
                closed: *closed,
                has_rest: rest.is_some(),
            },
            PatternDesc::Tpat_array(items) => {
                Desc::Array(ta.patterns(*items).map(|item| self.import(item)).collect())
            }
            // Callers lower dict patterns to records first (`Dict_pattern`).
            PatternDesc::Tpat_dict(_) => crate::misc::fatal_error("Parmatch.import: dict pattern"),
            PatternDesc::Tpat_or(left, right, _) => Desc::Or(
                self.import(ta.pattern(*left)),
                self.import(ta.pattern(*right)),
            ),
        };
        self.push(
            desc,
            Some(pat.pat_type),
            pat.pat_env,
            pat.pat_loc,
            Some(pat),
        )
    }

    // ---------------------------------------------------------------------
    // Coherence check (parmatch.ml:117-188)
    // ---------------------------------------------------------------------

    /// `simplify_head_pat p k`.
    fn simplify_head_pat(&self, p: P, k: &mut Vec<P>) {
        match self.desc(p) {
            Desc::Alias(inner) => self.simplify_head_pat(*inner, k),
            Desc::Var(_) => k.push(self.omega),
            Desc::Or(p1, p2) => {
                self.simplify_head_pat(*p1, k);
                self.simplify_head_pat(*p2, k);
            }
            _ => k.push(p),
        }
    }

    /// `simplified_first_col` over the first column of `rows`.
    fn simplified_first_col(&self, rows: &[Row]) -> Vec<P> {
        let mut column = Vec::new();
        for row in rows {
            self.simplify_head_pat(row[0], &mut column);
        }
        column
    }

    fn head_path(&mut self, p: P) -> Option<Path> {
        let node = self.node(p);
        let (env, ty) = (node.env, node.ty?);
        let expanded = self.oracle.expand_head(env, ty);
        let ctx = self.oracle.ctx();
        match &*ctx.get_desc(ctx.repr(expanded)) {
            TypeDesc::Tconstr { path, .. } => Some(path.clone()),
            _ => None,
        }
    }

    /// `lbl.lbl_all`: every label carries the array its record's labels were
    /// described with (or `Dict_pattern` built).
    fn lbl_all(&mut self, lbl_all: LabelArrayRef) -> Vec<LabelDescription> {
        self.oracle
            .ctx()
            .label_all(lbl_all)
            .unwrap_or_else(|| panic!("a pattern label carries no lbl_all array ({lbl_all:?})"))
    }

    /// `int_range p`: the values matched by an int or char constant or
    /// interval, as bounds.
    fn int_range(&self, p: P) -> Option<(i64, i64)> {
        match self.desc(p) {
            Desc::Constant(c) => int_of_constant(c).map(|i| (i, i)),
            Desc::Interval(lo, hi) => Some((int_of_constant(lo)?, int_of_constant(hi)?)),
            _ => None,
        }
    }

    /// `make_int_range p lo hi`: a constant or interval for `lo .. hi`, of
    /// the same kind as `p`: chars when `p` starts with a char and the bounds
    /// can be written as char literals.
    fn make_int_range(&mut self, p: P, lo: i64, hi: i64) -> P {
        let starts_with_char = match self.desc(p) {
            Desc::Constant(c) => matches!(**c, Constant::Char(_)),
            Desc::Interval(lo, _) => matches!(lo, Constant::Char(_)),
            _ => false,
        };
        let chars = is_valid_uchar(lo) && is_valid_uchar(hi) && starts_with_char;
        let konst = |i: i64| {
            if chars {
                Constant::Char(i as i32)
            } else {
                Constant::Int(i)
            }
        };
        let desc = if lo == hi {
            Desc::Constant(Cow::Owned(konst(lo)))
        } else {
            Desc::Interval(konst(lo), konst(hi))
        };
        self.with_desc(p, desc)
    }

    /// `split_int_range q column`: splits interval `q` at the bounds of the
    /// ranges in `column`, so that each piece is either inside or outside
    /// each of them. A constant is one piece.
    fn split_int_range(&mut self, q: P, column: &[P]) -> Vec<P> {
        let (Desc::Interval(..), Some((lo, hi))) = (self.desc(q), self.int_range(q)) else {
            return vec![q];
        };
        let mut cuts = Vec::new();
        for &p in column {
            if let Some((a, b)) = self.int_range(p) {
                if lo < a && a <= hi {
                    cuts.push(a);
                }
                if b < hi && lo <= b {
                    cuts.push(b + 1);
                }
            }
        }
        cuts.sort_unstable();
        cuts.dedup();
        let mut pieces = Vec::with_capacity(cuts.len() + 1);
        let mut start = lo;
        for c in cuts {
            pieces.push(self.make_int_range(q, start, c - 1));
            start = c;
        }
        pieces.push(self.make_int_range(q, start, hi));
        pieces
    }

    fn coherent_heads(&mut self, hp1: P, hp2: P) -> bool {
        enum Check {
            Done(bool),
            HeadPaths,
            RecordLabelCounts((LabelArrayRef, TypeExprRef), (LabelArrayRef, TypeExprRef)),
        }
        let check = match (self.desc(hp1), self.desc(hp2)) {
            (Desc::Construct { .. }, Desc::Construct { .. }) => Check::HeadPaths,
            (Desc::Constant(c1), Desc::Constant(c2)) => Check::Done(matches!(
                (&**c1, &**c2),
                (
                    Constant::Char(_) | Constant::Int(_),
                    Constant::Char(_) | Constant::Int(_)
                ) | (Constant::BigInt(..), Constant::BigInt(..))
                    | (Constant::Float(_), Constant::Float(_))
                    | (Constant::String(..), Constant::String(..))
            )),
            (Desc::Constant(_) | Desc::Interval(..), Desc::Constant(_) | Desc::Interval(..)) => {
                Check::Done(self.int_range(hp1).is_some() && self.int_range(hp2).is_some())
            }
            (Desc::Tuple(l1), Desc::Tuple(l2)) => Check::Done(l1.len() == l2.len()),
            (Desc::Record { fields: f1, .. }, Desc::Record { fields: f2, .. })
                if !f1.is_empty() && !f2.is_empty() =>
            {
                Check::RecordLabelCounts(
                    (f1[0].lbl.lbl_all, f1[0].lbl.lbl_res),
                    (f2[0].lbl.lbl_all, f2[0].lbl.lbl_res),
                )
            }
            (Desc::Any, _)
            | (_, Desc::Any)
            | (Desc::Record { .. }, Desc::Record { .. })
            | (Desc::Variant { .. }, Desc::Variant { .. })
            | (Desc::Array(_), Desc::Array(_)) => Check::Done(true),
            _ => Check::Done(false),
        };
        match check {
            Check::Done(result) => result,
            Check::HeadPaths => match (self.head_path(hp1), self.head_path(hp2)) {
                (Some(path1), Some(path2)) => path1.same(&path2),
                _ => false,
            },
            Check::RecordLabelCounts(lbl1, lbl2) => {
                self.lbl_all(lbl1.0).len() == self.lbl_all(lbl2.0).len()
            }
        }
    }

    /// `all_coherent column`.
    fn all_coherent(&mut self, column: &[P]) -> bool {
        let Some(discr) = column
            .iter()
            .copied()
            .find(|p| !matches!(self.desc(*p), Desc::Any))
        else {
            return true;
        };
        column.iter().all(|p| self.coherent_heads(discr, *p))
    }

    // ---------------------------------------------------------------------
    // Compatibility (parmatch.ml:189-318)
    // ---------------------------------------------------------------------

    /// `is_absent tag row`: the row of the variant pattern's type.
    fn is_absent(&mut self, p: P, tag: &str) -> bool {
        let node = self.node(p);
        let Some(ty) = node.ty else {
            return true;
        };
        let env = node.env;
        let expanded = self.oracle.expand_head(env, ty);
        let ctx = self.oracle.ctx();
        let desc = ctx.get_desc(ctx.repr(expanded));
        match &*desc {
            TypeDesc::Tvariant(row) => {
                let row = row.clone();
                drop(desc);
                matches!(
                    crate::types::btype::row_field(ctx, tag, &ctx.row_desc(row)),
                    RowField::Rabsent
                )
            }
            _ => false,
        }
    }

    fn is_absent_pat(&mut self, p: P) -> bool {
        match self.desc(p).clone() {
            Desc::Variant { label, .. } => self.is_absent(p, &label),
            _ => false,
        }
    }

    /// `records_args l1 l2`: fields are sorted by position.
    fn records_args(&self, l1: &[Field<'a>], l2: &[Field<'a>]) -> (Vec<P>, Vec<P>) {
        let (mut r1, mut r2) = (Vec::new(), Vec::new());
        let (mut i, mut j) = (0, 0);
        while i < l1.len() || j < l2.len() {
            if i == l1.len() {
                r1.push(self.omega);
                r2.push(l2[j].pat);
                j += 1;
            } else if j == l2.len() {
                r1.push(l1[i].pat);
                r2.push(self.omega);
                i += 1;
            } else if l1[i].lbl.lbl_pos < l2[j].lbl.lbl_pos {
                r1.push(l1[i].pat);
                r2.push(self.omega);
                i += 1;
            } else if l1[i].lbl.lbl_pos > l2[j].lbl.lbl_pos {
                r1.push(self.omega);
                r2.push(l2[j].pat);
                j += 1;
            } else {
                r1.push(l1[i].pat);
                r2.push(l2[j].pat);
                i += 1;
                j += 1;
            }
        }
        (r1, r2)
    }

    /// `Compat.compat ~equal_cd:Types.same_constructor p q`.
    pub fn compat(&self, p: P, q: P) -> bool {
        match (self.desc(p), self.desc(q)) {
            (Desc::Any | Desc::Var(_), _) | (_, Desc::Any | Desc::Var(_)) => true,
            (Desc::Alias(p), _) => self.compat(*p, q),
            (_, Desc::Alias(q)) => self.compat(p, *q),
            (Desc::Or(p1, p2), _) => self.compat(*p1, q) || self.compat(*p2, q),
            (_, Desc::Or(q1, q2)) => self.compat(p, *q1) || self.compat(p, *q2),
            (
                Desc::Construct {
                    cstr: c1, args: a1, ..
                },
                Desc::Construct {
                    cstr: c2, args: a2, ..
                },
            ) => same_constructor(c1, c2) && self.compats(a1, a2),
            (Desc::Variant { label: l1, arg: a1 }, Desc::Variant { label: l2, arg: a2 }) => {
                l1 == l2
                    && match (a1, a2) {
                        (None, None) => true,
                        (Some(p), Some(q)) => self.compat(*p, *q),
                        _ => false,
                    }
            }
            (Desc::Constant(c1), Desc::Constant(c2)) => {
                const_compare(c1, c2) == std::cmp::Ordering::Equal
            }
            (Desc::Constant(_) | Desc::Interval(..), Desc::Constant(_) | Desc::Interval(..)) => {
                match (self.int_range(p), self.int_range(q)) {
                    (Some((lo1, hi1)), Some((lo2, hi2))) => lo1 <= hi2 && lo2 <= hi1,
                    _ => false,
                }
            }
            (Desc::Tuple(ps), Desc::Tuple(qs)) => self.compats(ps, qs),
            (Desc::Record { fields: l1, .. }, Desc::Record { fields: l2, .. }) => {
                let (ps, qs) = self.records_args(l1, l2);
                self.compats(&ps, &qs)
            }
            (Desc::Array(ps), Desc::Array(qs)) => ps.len() == qs.len() && self.compats(ps, qs),
            _ => false,
        }
    }

    /// `Compat.compats`: lists of different lengths are not compatible.
    pub fn compats(&self, ps: &[P], qs: &[P]) -> bool {
        ps.len() == qs.len() && ps.iter().zip(qs).all(|(p, q)| self.compat(*p, *q))
    }
}

/// `const_compare x y` (parmatch.ml:222-229).
pub(crate) fn const_compare(x: &Constant, y: &Constant) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (x, y) {
        (Constant::Float(f1), Constant::Float(f2)) => {
            let (a, b) = (parse_ocaml_float(f1), parse_ocaml_float(f2));
            // OCaml's polymorphic `compare` on floats: nan is equal to itself
            // and smaller than any other float.
            match (a.is_nan(), b.is_nan()) {
                (true, true) => Ordering::Equal,
                (true, false) => Ordering::Less,
                (false, true) => Ordering::Greater,
                (false, false) => a.partial_cmp(&b).unwrap_or(Ordering::Equal),
            }
        }
        (Constant::BigInt(s1, b1), Constant::BigInt(s2, b2)) => {
            bigint_compare((*s1, b1), (*s2, b2))
        }
        (Constant::String(s1), Constant::String(s2)) => s1.as_bytes().cmp(s2.as_bytes()),
        // `char` is an alias of `int`.
        (Constant::Char(_) | Constant::Int(_), Constant::Char(_) | Constant::Int(_)) => {
            int_of_constant(x).cmp(&int_of_constant(y))
        }
        _ => constant_structural_compare(x, y),
    }
}

/// The value of an int or char constant.
pub(crate) fn int_of_constant(c: &Constant) -> Option<i64> {
    match c {
        Constant::Int(i) => Some(*i),
        Constant::Char(c) => Some(i64::from(*c)),
        Constant::String(_) | Constant::Float(_) | Constant::BigInt(..) => None,
    }
}

/// OCaml `Uchar.is_valid`.
fn is_valid_uchar(i: i64) -> bool {
    (0..=0xD7FF).contains(&i) || (0xE000..=0x10FFFF).contains(&i)
}

/// `Parmatch.int_range` on a typed pattern: the values matched by an int or
/// char constant or interval, as bounds.
pub(crate) fn int_range(p: &Pattern) -> Option<(i64, i64)> {
    match &p.pat_desc {
        PatternDesc::Tpat_constant(c) => int_of_constant(c).map(|i| (i, i)),
        PatternDesc::Tpat_interval(lo, hi) => Some((int_of_constant(&lo.constant())?, int_of_constant(&hi.constant())?)),
        _ => None,
    }
}

/// `Parmatch.make_int_range` on a typed pattern: a constant or interval for
/// `lo .. hi`, of the same kind as `p`, as `{p with pat_desc; pat_extra = []}`.
/// The pattern keeps `p`'s cold side data: its attributes, as in OCaml, and
/// its `pat_extra`, which the typed arena holds immutably here; match
/// compilation, the only caller, never reads `pat_extra`.
pub(crate) fn make_int_range(p: &Pattern, lo: i64, hi: i64) -> Pattern {
    let starts_with_char = matches!(
        &p.pat_desc,
        PatternDesc::Tpat_constant(Constant::Char(_))
            | PatternDesc::Tpat_interval(crate::types::typedtree::IntervalBound::Char(_), _)
    );
    let chars = is_valid_uchar(lo) && is_valid_uchar(hi) && starts_with_char;
    let konst = |i: i64| {
        if chars {
            Constant::Char(i as i32)
        } else {
            Constant::Int(i)
        }
    };
    let mut q = p.clone();
    q.pat_desc = if lo == hi {
        PatternDesc::Tpat_constant(konst(lo))
    } else {
        PatternDesc::Tpat_interval(crate::types::typedtree::IntervalBound::from_constant(konst(lo)), crate::types::typedtree::IntervalBound::from_constant(konst(hi)))
    };
    q
}

/// OCaml `float_of_string` for the float literals kept in the typed tree.
fn parse_ocaml_float(text: &str) -> f64 {
    let cleaned: String = text.chars().filter(|c| *c != '_').collect();
    cleaned.parse::<f64>().unwrap_or(f64::NAN)
}

/// `Bigint_utils.compare` (compiler/ml/bigint_utils.ml:77-96).
fn bigint_compare((p0, s0): (bool, &String), (p1, s1): (bool, &String)) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (p0, p1) {
        (false, true) => Ordering::Less,
        (true, false) => Ordering::Greater,
        _ => {
            let (len0, len1) = (s0.len(), s1.len());
            if len0 == len1 {
                if p0 {
                    s0.as_bytes().cmp(s1.as_bytes())
                } else {
                    s1.as_bytes().cmp(s0.as_bytes())
                }
            } else if len0 > len1 {
                if p0 {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            } else if p0 {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        }
    }
}

/// OCaml's structural `compare` on constants of the same or different
/// constructors (declaration order: Const_int, Const_char, Const_string,
/// Const_float, Const_bigint).
fn constant_structural_compare(x: &Constant, y: &Constant) -> std::cmp::Ordering {
    fn rank(c: &Constant) -> u8 {
        match c {
            Constant::Int(_) => 0,
            Constant::Char(_) => 1,
            Constant::String(..) => 2,
            Constant::Float(_) => 3,
            Constant::BigInt(..) => 4,
        }
    }
    match (x, y) {
        (Constant::Int(a), Constant::Int(b)) => a.cmp(b),
        (Constant::Char(a), Constant::Char(b)) => a.cmp(b),
        _ => rank(x).cmp(&rank(y)),
    }
}

/// OCaml `string_of_float` (`valid_float_lexem (format_float "%.12g" f)`) for
/// the integral values `build_other_constant` produces.
fn ocaml_string_of_float(f: f64) -> String {
    if f.fract() == 0.0 && f.abs() < 1e12 {
        format!("{}.", f as i64)
    } else {
        let text = format!("{f:.12e}");
        if text.contains('.') || text.contains('e') {
            text
        } else {
            format!("{text}.")
        }
    }
}

/// `some_other_tag` (parmatch.ml:1008).
pub(crate) const SOME_OTHER_TAG: &str = "<some other tag>";

/// Result of `exhaust` (parmatch.ml:1233-1236).
type ExhaustResult = Option<Vec<Row>>;

// ---------------------------------------------------------------------------
// Matching utilities (parmatch.ml:492-1006)
// ---------------------------------------------------------------------------

impl<'a, O: Oracle> Parmatch<'a, O> {
    fn head_is_var(&self, p: P) -> bool {
        matches!(self.desc(p), Desc::Any | Desc::Var(_))
    }

    /// `simple_match p1 p2` (parmatch.ml:506-517).
    fn simple_match(&self, p1: P, p2: P) -> bool {
        match (self.desc(p1), self.desc(p2)) {
            (Desc::Construct { cstr: c1, .. }, Desc::Construct { cstr: c2, .. }) => {
                same_constructor(c1, c2)
            }
            (Desc::Variant { label: l1, .. }, Desc::Variant { label: l2, .. }) => l1 == l2,
            (Desc::Constant(c1), Desc::Constant(c2)) => {
                const_compare(c1, c2) == std::cmp::Ordering::Equal
            }
            // `p1` is a piece of a column split by `split_int_range`, so it
            // is either inside or outside `p2`.
            (Desc::Constant(_) | Desc::Interval(..), Desc::Constant(_) | Desc::Interval(..)) => {
                match (self.int_range(p1), self.int_range(p2)) {
                    (Some((lo1, hi1)), Some((lo2, hi2))) => lo2 <= lo1 && hi1 <= hi2,
                    _ => false,
                }
            }
            (Desc::Record { .. }, Desc::Record { .. }) => true,
            (Desc::Tuple(a), Desc::Tuple(b)) | (Desc::Array(a), Desc::Array(b)) => {
                a.len() == b.len()
            }
            (_, Desc::Any | Desc::Var(_)) => true,
            _ => false,
        }
    }

    /// `record_arg p` (parmatch.ml:520-524).
    fn record_arg(&self, p: P) -> Vec<Field<'a>> {
        match self.desc(p) {
            Desc::Any => Vec::new(),
            Desc::Record { fields, .. } => fields.clone(),
            _ => crate::misc::fatal_error("Parmatch.as_record"),
        }
    }

    /// `extract_fields omegas arg` (parmatch.ml:531-536).
    fn extract_fields(&self, omegas: &[Field<'a>], arg: &[Field<'a>]) -> Vec<P> {
        omegas
            .iter()
            .map(|field| {
                arg.iter()
                    .find(|a| a.lbl.lbl_pos == field.lbl.lbl_pos)
                    .map_or(self.omega, |a| a.pat)
            })
            .collect()
    }

    /// `all_record_args lbls` (parmatch.ml:538-573).
    fn all_record_args(
        &mut self,
        lbls: &[Field<'a>],
    ) -> Vec<Field<'a>> {
        let Some(first) = lbls.first() else {
            return Vec::new();
        };
        let opt = first.opt;
        let lbl_all = self.lbl_all(first.lbl.lbl_all);
        let mut table: Vec<Field<'a>> = lbl_all
            .into_iter()
            .map(|lbl| Field {
                lid: None,
                lbl: Cow::Owned(lbl),
                pat: self.omega,
                opt,
            })
            .collect();
        for field in lbls {
            let pos = field.lbl.lbl_pos as usize;
            if pos < table.len() {
                table[pos] = field.clone();
            }
        }
        table
    }

    /// `simple_match_args p1 p2` (parmatch.ml:576-593).
    fn simple_match_args(&self, p1: P, p2: P) -> Vec<P> {
        match self.desc(p2) {
            Desc::Alias(p2) => self.simple_match_args(p1, *p2),
            Desc::Construct { args, .. } => args.clone(),
            Desc::Variant { arg: Some(arg), .. } => vec![*arg],
            Desc::Tuple(args) | Desc::Array(args) => args.clone(),
            Desc::Record { fields, .. } => self.extract_fields(&self.record_arg(p1), fields),
            Desc::Any | Desc::Var(_) => match self.desc(p1) {
                Desc::Construct { args, .. } => self.omegas(args.len()),
                Desc::Variant { arg: Some(_), .. } => vec![self.omega],
                Desc::Tuple(args) | Desc::Array(args) => self.omegas(args.len()),
                Desc::Record { fields, .. } => self.omegas(fields.len()),
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// `normalize_pat q` (parmatch.ml:599-622).
    fn normalize_pat(&mut self, q: P) -> P {
        match self.desc(q).clone() {
            Desc::Any | Desc::Constant(_) | Desc::Interval(..) => q,
            Desc::Var(_) => self.make_pat_like(Desc::Any, q),
            Desc::Alias(p) => self.normalize_pat(p),
            Desc::Tuple(args) => {
                let desc = Desc::Tuple(self.omegas(args.len()));
                self.make_pat_like(desc, q)
            }
            Desc::Construct { lid, cstr, args } => {
                let desc = Desc::Construct {
                    lid,
                    cstr,
                    args: self.omegas(args.len()),
                };
                self.make_pat_like(desc, q)
            }
            Desc::Variant { label, arg } => {
                let desc = Desc::Variant {
                    label,
                    arg: arg.map(|_| self.omega),
                };
                self.make_pat_like(desc, q)
            }
            Desc::Array(args) => {
                let desc = Desc::Array(self.omegas(args.len()));
                self.make_pat_like(desc, q)
            }
            Desc::Record {
                fields,
                closed,
                has_rest,
            } => {
                let omega = self.omega;
                let desc = Desc::Record {
                    fields: fields
                        .into_iter()
                        .map(|field| Field {
                            pat: omega,
                            ..field
                        })
                        .collect(),
                    closed,
                    has_rest,
                };
                self.make_pat_like(desc, q)
            }
            Desc::Or(..) => crate::misc::fatal_error("Parmatch.normalize_pat"),
        }
    }

    /// `discr_pat q pss` (parmatch.ml:629-660) over the first column heads.
    fn discr_pat(&mut self, q: P, heads: &[P]) -> P {
        let q = self.normalize_pat(q);
        if !matches!(self.desc(q), Desc::Any | Desc::Record { .. }) {
            return q;
        }
        let mut acc = q;
        let mut stack: Vec<P> = heads.iter().rev().copied().collect();
        while let Some(head) = stack.pop() {
            match self.desc(head).clone() {
                Desc::Alias(p) => stack.push(p),
                Desc::Or(p1, p2) => {
                    stack.push(p2);
                    stack.push(p1);
                }
                Desc::Any | Desc::Var(_) => {}
                Desc::Tuple(_) => return self.normalize_pat(head),
                Desc::Record {
                    fields: largs,
                    closed,
                    has_rest,
                } => {
                    let mut r = self.record_arg(acc);
                    for field in largs.iter().rev() {
                        if !r.iter().any(|f| f.lbl.lbl_pos == field.lbl.lbl_pos) {
                            r.insert(
                                0,
                                Field {
                                    pat: self.omega,
                                    ..field.clone()
                                },
                            );
                        }
                    }
                    let desc = Desc::Record {
                        fields: r,
                        closed,
                        has_rest,
                    };
                    acc = self.make_pat_like(desc, head);
                }
                _ => return acc,
            }
        }
        acc
    }

    fn heads(rows: &[Row]) -> Vec<P> {
        rows.iter().filter_map(|row| row.first().copied()).collect()
    }

    /// `read_args xs r` (parmatch.ml:667-673).
    fn read_args(n: usize, r: &[P]) -> (Vec<P>, Vec<P>) {
        if r.len() < n {
            crate::misc::fatal_error("Parmatch.read_args");
        }
        (r[..n].to_vec(), r[n..].to_vec())
    }

    /// `do_set_args erase_mutable q r` (parmatch.ml:675-718).
    fn do_set_args(&mut self, erase_mutable: bool, q: P, r: &[P]) -> Vec<P> {
        let (head, rest) = match self.desc(q).clone() {
            Desc::Tuple(omegas) => {
                let (args, rest) = Self::read_args(omegas.len(), r);
                (self.make_pat_like(Desc::Tuple(args), q), rest)
            }
            Desc::Record {
                fields,
                closed,
                has_rest,
            } => {
                let (args, rest) = Self::read_args(fields.len(), r);
                let omega = self.omega;
                let fields = fields
                    .into_iter()
                    .zip(args)
                    .map(|(field, arg)| {
                        let pat =
                            if erase_mutable && matches!(field.lbl.lbl_mut, MutableFlag::Mutable) {
                                omega
                            } else {
                                arg
                            };
                        Field { pat, ..field }
                    })
                    .collect();
                let desc = Desc::Record {
                    fields,
                    closed,
                    has_rest,
                };
                (self.make_pat_like(desc, q), rest)
            }
            Desc::Construct { lid, cstr, args } => {
                let (args, rest) = Self::read_args(args.len(), r);
                (
                    self.make_pat_like(Desc::Construct { lid, cstr, args }, q),
                    rest,
                )
            }
            Desc::Variant { label, arg } => {
                let (arg, rest) = match (arg, r.split_first()) {
                    (Some(_), Some((a, r))) => (Some(*a), r.to_vec()),
                    (None, _) => (None, r.to_vec()),
                    _ => crate::misc::fatal_error("Parmatch.set_args"),
                };
                (self.make_pat_like(Desc::Variant { label, arg }, q), rest)
            }
            Desc::Array(omegas) => {
                let (args, rest) = Self::read_args(omegas.len(), r);
                (self.make_pat_like(Desc::Array(args), q), rest)
            }
            Desc::Constant(_) | Desc::Interval(..) | Desc::Any => (q, r.to_vec()),
            _ => crate::misc::fatal_error("Parmatch.set_args"),
        };
        let mut result = vec![head];
        result.extend(rest);
        result
    }

    fn set_args(&mut self, q: P, r: &[P]) -> Vec<P> {
        self.do_set_args(false, q, r)
    }

    /// `filter_one q pss` (parmatch.ml:724-737).
    fn filter_one(&mut self, q: P, pss: &[Row]) -> Vec<Row> {
        let mut out = Vec::new();
        let mut stack: Vec<Row> = pss.iter().rev().cloned().collect();
        while let Some(row) = stack.pop() {
            let Some((&p, ps)) = row.split_first() else {
                return out;
            };
            match self.desc(p).clone() {
                Desc::Alias(inner) => stack.push(prepend(inner, ps)),
                Desc::Or(p1, p2) => {
                    stack.push(prepend(p2, ps));
                    stack.push(prepend(p1, ps));
                }
                _ => {
                    if self.simple_match(q, p) {
                        let mut new_row = self.simple_match_args(q, p);
                        new_row.extend_from_slice(ps);
                        out.push(new_row);
                    }
                }
            }
        }
        out
    }

    /// `filter_extra pss` (parmatch.ml:745-756).
    fn filter_extra(&self, pss: &[Row]) -> Vec<Row> {
        let mut out = Vec::new();
        let mut stack: Vec<Row> = pss.iter().rev().cloned().collect();
        while let Some(row) = stack.pop() {
            let Some((&p, ps)) = row.split_first() else {
                continue;
            };
            match self.desc(p) {
                Desc::Alias(inner) => stack.push(prepend(*inner, ps)),
                Desc::Or(p1, p2) => {
                    let (p1, p2) = (*p1, *p2);
                    stack.push(prepend(p2, ps));
                    stack.push(prepend(p1, ps));
                }
                Desc::Any | Desc::Var(_) => out.push(ps.to_vec()),
                _ => {}
            }
        }
        out
    }

    /// `filter_all`'s `same_head`: int and char ranges are grouped by equal
    /// bounds, not by containment as `simple_match` does, so that
    /// `build_other` sees every range.
    fn same_head(&self, q0: P, q: P) -> bool {
        match (self.int_range(q0), self.int_range(q)) {
            (Some(r0), Some(r)) => r0 == r,
            _ => self.simple_match(q0, q),
        }
    }

    /// `filter_all pat0 pss` (parmatch.ml:770-822).
    fn filter_all(&mut self, pat0: P, pss: &[Row]) -> Vec<(P, Vec<Row>)> {
        // Each group's rows are kept newest-first, like OCaml's `::`.
        let mut env: Vec<(P, std::collections::VecDeque<Row>)> =
            if matches!(self.desc(pat0), Desc::Record { .. } | Desc::Tuple(_)) {
                vec![(pat0, std::collections::VecDeque::new())]
            } else {
                Vec::new()
            };
        // filter_rec
        let mut stack: Vec<Row> = pss.iter().rev().cloned().collect();
        while let Some(row) = stack.pop() {
            let Some((&p, ps)) = row.split_first() else {
                break;
            };
            match self.desc(p).clone() {
                Desc::Alias(inner) => stack.push(prepend(inner, ps)),
                Desc::Or(p1, p2) => {
                    stack.push(prepend(p2, ps));
                    stack.push(prepend(p1, ps));
                }
                Desc::Any | Desc::Var(_) => {}
                _ => {
                    // insert p ps: the row goes to the group whose head
                    // matches it; there is at most one such group, since a
                    // group is only created when no other matches.
                    let group = env.iter().position(|(q0, _)| self.same_head(*q0, p));
                    if let Some(group) = group {
                        let q0 = env[group].0;
                        let mut new_row = self.simple_match_args(q0, p);
                        new_row.extend_from_slice(ps);
                        env[group].1.push_front(new_row);
                    } else {
                        let q0 = self.normalize_pat(p);
                        let mut new_row = self.simple_match_args(q0, p);
                        new_row.extend_from_slice(ps);
                        env.push((q0, std::collections::VecDeque::from(vec![new_row])));
                    }
                }
            }
        }
        // filter_omega
        let mut stack: Vec<Row> = pss.iter().rev().cloned().collect();
        while let Some(row) = stack.pop() {
            let Some((&p, ps)) = row.split_first() else {
                continue;
            };
            match self.desc(p).clone() {
                Desc::Alias(inner) => stack.push(prepend(inner, ps)),
                Desc::Or(p1, p2) => {
                    stack.push(prepend(p2, ps));
                    stack.push(prepend(p1, ps));
                }
                Desc::Any | Desc::Var(_) => {
                    let omega = self.omega;
                    for (q, qss) in env.iter_mut() {
                        let mut new_row = self.simple_match_args(*q, omega);
                        new_row.extend_from_slice(ps);
                        qss.push_front(new_row);
                    }
                }
                _ => {}
            }
        }
        env.into_iter()
            .map(|(q, rows)| (q, rows.into_iter().collect()))
            .collect()
    }

    /// `mark_partial pss` (parmatch.ml:833-842).
    fn mark_partial(&self, pss: &[Row]) -> Vec<Row> {
        let mut out = Vec::new();
        let mut stack: Vec<Row> = pss.iter().rev().cloned().collect();
        while let Some(row) = stack.pop() {
            match row.split_first() {
                Some((&p, ps)) if matches!(self.desc(p), Desc::Alias(_)) => {
                    let Desc::Alias(inner) = self.desc(p) else {
                        unreachable!()
                    };
                    stack.push(prepend(*inner, ps));
                }
                Some((&p, ps)) if matches!(self.desc(p), Desc::Or(..)) => {
                    let Desc::Or(p1, p2) = self.desc(p) else {
                        unreachable!()
                    };
                    let (p1, p2) = (*p1, *p2);
                    stack.push(prepend(p2, ps));
                    stack.push(prepend(p1, ps));
                }
                Some((&p, _)) if self.head_is_var(p) => out.push(row),
                _ => {
                    let mut row = row;
                    if let Some(last) = row.last_mut() {
                        *last = self.zero;
                    }
                    out.push(row);
                }
            }
        }
        out
    }

    /// `full_match closing env` (parmatch.ml:903-945).
    fn full_match(&mut self, closing: bool, env: &[(P, Vec<Row>)]) -> bool {
        let Some(&(p, _)) = env.first() else {
            panic!("Parmatch.full_match: empty");
        };
        match self.desc(p).clone() {
            Desc::Construct { cstr, .. } => match cstr.cstr_kind {
                ConstructorKind::Extension(_) => false,
                ConstructorKind::Ordinary(_) => env.len() == self.oracle.variant_length(&cstr),
            },
            Desc::Variant { .. } => {
                let fields: Vec<String> = env
                    .iter()
                    .map(|(q, _)| match self.desc(*q) {
                        Desc::Variant { label, .. } => label.to_string(),
                        _ => panic!("Parmatch.full_match: variant"),
                    })
                    .collect();
                let node = self.node(p);
                let (penv, pty) = (node.env, node.ty.expect("variant pattern type"));
                let row = self.oracle.row_of(penv, pty);
                let ctx = self.oracle.ctx();
                if closing && !crate::types::btype::row_fixed(ctx, &row) {
                    row.row_fields
                        .iter()
                        .all(
                            |(tag, f)| match crate::types::btype::row_field_repr(ctx, f) {
                                RowField::Rabsent | RowField::Reither { matched: false, .. } => {
                                    true
                                }
                                RowField::Reither { matched: true, .. } | RowField::Rpresent(_) => {
                                    fields.iter().any(|t| t == tag.as_str())
                                }
                            },
                        )
                } else {
                    row.row_closed
                        && row.row_fields.iter().all(|(tag, f)| {
                            matches!(
                                crate::types::btype::row_field_repr(ctx, f),
                                RowField::Rabsent
                            ) || fields.iter().any(|t| t == tag.as_str())
                        })
                }
            }
            Desc::Constant(_) | Desc::Interval(..) => false,
            Desc::Tuple(_) | Desc::Record { .. } => true,
            Desc::Array(_) => false,
            _ => panic!("Parmatch.full_match"),
        }
    }

    /// `should_extend ext env` (parmatch.ml:948-963).
    fn should_extend(&mut self, ext: Option<&Path>, env: &[(P, Vec<Row>)]) -> bool {
        let Some(ext) = ext else {
            return false;
        };
        let Some(&(p, _)) = env.first() else {
            panic!("Parmatch.should_extend");
        };
        match self.desc(p) {
            Desc::Construct { cstr, .. } => match cstr.cstr_kind {
                ConstructorKind::Ordinary(_) => {
                    let node = self.node(p);
                    let (penv, pty) = (node.env, node.ty.expect("constructor pattern type"));
                    self.oracle.type_path(penv, pty).same(ext)
                }
                ConstructorKind::Extension(_) => false,
            },
            Desc::Constant(_)
            | Desc::Interval(..)
            | Desc::Tuple(_)
            | Desc::Variant { .. }
            | Desc::Record { .. }
            | Desc::Array(_) => false,
            _ => panic!("Parmatch.should_extend"),
        }
    }

    /// `pat_of_constr ex_pat cstr` (parmatch.ml:967-976).
    fn pat_of_constr(&mut self, ex_pat: P, cstr: ConstructorDescription) -> P {
        let args = self.omegas(cstr.cstr_arity.max(0) as usize);
        self.with_desc(
            ex_pat,
            Desc::Construct {
                lid: None,
                cstr: std::sync::Arc::new(cstr),
                args,
            },
        )
    }

    /// `orify x y`.
    fn orify(&mut self, x: P, y: P) -> P {
        self.make_pat_like(Desc::Or(x, y), x)
    }

    /// `orify_many`: right-nested or-patterns.
    pub fn orify_many(&mut self, xs: &[P]) -> P {
        match xs {
            [] => panic!("Parmatch.orify_many"),
            [x] => *x,
            [x, rest @ ..] => {
                let tail = self.orify_many(rest);
                self.orify(*x, tail)
            }
        }
    }

    fn pat_of_constrs(
        &mut self,
        ex_pat: P,
        cstrs: Vec<ConstructorDescription>,
    ) -> Result<P, Empty> {
        if cstrs.is_empty() {
            return Err(Empty);
        }
        let pats: Vec<P> = cstrs
            .into_iter()
            .map(|cstr| self.pat_of_constr(ex_pat, cstr))
            .collect();
        Ok(self.orify_many(&pats))
    }

    /// `pats_of_type ?always env ty` (parmatch.ml:988-1011).
    pub fn pats_of_type(&mut self, always: bool, env: EnvRef, ty: TypeExprRef) -> Vec<P> {
        match self.oracle.type_shape(env, ty, always) {
            TypeShape::Variant(cstrs) => {
                let ex_pat = self.make_pat(Desc::Any, Some(ty), env);
                cstrs
                    .into_iter()
                    .map(|cstr| self.pat_of_constr(ex_pat, cstr))
                    .collect()
            }
            TypeShape::Record(labels) => {
                let omega = self.omega;
                let fields = labels
                    .into_iter()
                    .map(|lbl| Field {
                        lid: None,
                        lbl: Cow::Owned(lbl),
                        pat: omega,
                        opt: false,
                    })
                    .collect();
                vec![self.make_pat(
                    Desc::Record {
                        fields,
                        closed: ClosedFlag::Closed,
                        has_rest: false,
                    },
                    Some(ty),
                    env,
                )]
            }
            TypeShape::Tuple(n) => {
                let desc = Desc::Tuple(self.omegas(n));
                vec![self.make_pat(desc, Some(ty), env)]
            }
            TypeShape::Other => vec![self.omega],
        }
    }

    /// `complete_constrs p seen_constrs` (parmatch.ml:1014-1028).
    fn complete_constrs(
        &mut self,
        p: P,
        seen: &[ConstructorDescription],
    ) -> Vec<ConstructorDescription> {
        let Desc::Construct { cstr, .. } = self.desc(p).clone() else {
            panic!("Parmatch.complete_constrs");
        };
        let env = self.node(p).env;
        let constrs = self.oracle.variant_constructors(env, cstr.cstr_res);
        let others: Vec<ConstructorDescription> = constrs
            .into_iter()
            .filter(|c| !seen.iter().any(|s| same_constructor(c, s)))
            .collect();
        let (constants, non_constants): (Vec<_>, Vec<_>) =
            others.into_iter().partition(|c| c.cstr_arity == 0);
        constants.into_iter().chain(non_constants).collect()
    }

    /// `build_other_constrs env p` (parmatch.ml:1030-1040).
    fn build_other_constrs(&mut self, env: &[(P, Vec<Row>)], p: P) -> Result<P, Empty> {
        match self.desc(p) {
            Desc::Construct { cstr, .. }
                if matches!(cstr.cstr_kind, ConstructorKind::Ordinary(_)) =>
            {
                let seen: Vec<ConstructorDescription> = env
                    .iter()
                    .map(|(q, _)| match self.desc(*q) {
                        Desc::Construct { cstr, .. } => cstr.as_ref().clone(),
                        _ => crate::misc::fatal_error("Parmatch.get_constr"),
                    })
                    .collect();
                let others = self.complete_constrs(p, &seen);
                self.pat_of_constrs(p, others)
            }
            _ => Ok(self.extra),
        }
    }

    /// `build_other ext env` (parmatch.ml:1052-1166).
    fn build_other(&mut self, ext: Option<&Path>, env: &[(P, Vec<Row>)]) -> Result<P, Empty> {
        let Some(&(p, _)) = env.first() else {
            return Ok(self.omega);
        };
        match self.desc(p).clone() {
            Desc::Construct { lid, cstr, .. }
                if matches!(cstr.cstr_kind, ConstructorKind::Extension(_)) =>
            {
                let ident = self.oracle.create_ident("*extension*");
                let loc = lid.map_or(LocIdx::none(), |lid| lid.loc);
                Ok(self.make_pat(Desc::Var(VarKind::Extension(ident, loc)), None, EnvRef(0)))
            }
            Desc::Construct { .. } => {
                if let Some(ext) = ext {
                    let node = self.node(p);
                    let (penv, pty) = (node.env, node.ty.expect("constructor pattern type"));
                    if ext.same(&self.oracle.type_path(penv, pty)) {
                        return Ok(self.extra);
                    }
                }
                self.build_other_constrs(env, p)
            }
            Desc::Variant { .. } => {
                let tags: Vec<String> = env
                    .iter()
                    .map(|(q, _)| match self.desc(*q) {
                        Desc::Variant { label, .. } => label.to_string(),
                        _ => panic!("Parmatch.build_other: variant"),
                    })
                    .collect();
                let node = self.node(p);
                let (penv, pty) = (node.env, node.ty.expect("variant pattern type"));
                let row = self.oracle.row_of(penv, pty);
                let mut others: Vec<P> = Vec::new();
                for (tag, f) in &row.row_fields {
                    if tags.iter().any(|t| t == tag.as_str()) {
                        continue;
                    }
                    let field = crate::types::btype::row_field_repr(self.oracle.ctx(), f);
                    let constant = match field {
                        RowField::Rabsent => continue,
                        RowField::Reither { constant, .. } => constant,
                        RowField::Rpresent(arg) => arg.is_none(),
                    };
                    let pat = self.make_other_variant(p, tag.as_str(), constant);
                    others.insert(0, pat);
                }
                match others.split_first() {
                    None => Ok(self.make_other_variant(p, SOME_OTHER_TAG, true)),
                    Some((&first, rest)) => {
                        let mut result = first;
                        for &pat in rest {
                            result = self.make_pat_like(Desc::Or(pat, result), p);
                        }
                        Ok(result)
                    }
                }
            }
            // Int and char constants and intervals can share a column; the
            // example is the least value from 0 up that no range covers, else
            // the greatest one below 0, of the kind of the first pattern.
            // Ranges sorted by a bound are skipped in one pass.
            Desc::Constant(_) | Desc::Interval(..) if self.int_range(p).is_some() => {
                let ranges: Vec<(i64, i64)> =
                    env.iter().filter_map(|(q, _)| self.int_range(*q)).collect();
                let mut by_lo = ranges.clone();
                by_lo.sort_by_key(|&(lo, _)| lo);
                let up = by_lo.iter().fold(
                    0i64,
                    |i, &(lo, hi)| {
                        if lo <= i && i <= hi { hi + 1 } else { i }
                    },
                );
                let int32_max = i64::from(i32::MAX);
                let int32_min = i64::from(i32::MIN);
                if up <= int32_max {
                    Ok(self.make_int_range(p, up, up))
                } else {
                    let mut by_hi = ranges;
                    by_hi.sort_by(|(_, hi1), (_, hi2)| hi2.cmp(hi1));
                    let other =
                        by_hi.iter().fold(
                            -1i64,
                            |i, &(lo, hi)| {
                                if lo <= i && i <= hi { lo - 1 } else { i }
                            },
                        );
                    // Every int is covered; ints are never matched
                    // exhaustively.
                    if other < int32_min {
                        Ok(self.omega)
                    } else {
                        Ok(self.make_int_range(p, other, other))
                    }
                }
            }
            Desc::Constant(c) => Ok(match c.as_ref() {
                Constant::Int(_) | Constant::Char(_) => unreachable!("int ranges"),
                Constant::BigInt(..) => {
                    let all: Vec<usize> = env
                        .iter()
                        .filter_map(|(q, _)| match self.desc(*q) {
                            Desc::Constant(c) => match c.as_ref() {
                                Constant::BigInt(sign, digits) => Some(if *sign {
                                    digits.len()
                                } else {
                                    digits.len() + 1
                                }),
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect();
                    let mut i = 0usize;
                    while all.contains(&i) {
                        i += 1;
                    }
                    self.make_pat_like(
                        Desc::Constant(Cow::Owned(Constant::BigInt(true, i.to_string()))),
                        p,
                    )
                }
                Constant::String(..) => {
                    let all: Vec<usize> = env
                        .iter()
                        .filter_map(|(q, _)| match self.desc(*q) {
                            Desc::Constant(c) => match c.as_ref() {
                                Constant::String(s) => Some(
                                    crate::string_literal::utf16_length(s)
                                        .expect("String_literal.utf16_length: Invalid_utf8"),
                                ),
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect();
                    let mut i = 0usize;
                    while all.contains(&i) {
                        i += 1;
                    }
                    self.make_pat_like(
                        Desc::Constant(Cow::Owned(Constant::String("*".repeat(i)))),
                        p,
                    )
                }
                Constant::Float(_) => {
                    let all: Vec<f64> = env
                        .iter()
                        .filter_map(|(q, _)| match self.desc(*q) {
                            Desc::Constant(c) => match c.as_ref() {
                                Constant::Float(f) => Some(parse_ocaml_float(f)),
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect();
                    let mut f = 0.0f64;
                    while all.contains(&f) {
                        f += 1.0;
                    }
                    self.make_pat_like(
                        Desc::Constant(Cow::Owned(Constant::Float(ocaml_string_of_float(f)))),
                        p,
                    )
                }
            }),
            Desc::Array(_) => {
                let all_lengths: Vec<usize> = env
                    .iter()
                    .map(|(q, _)| match self.desc(*q) {
                        Desc::Array(args) => args.len(),
                        _ => panic!("Parmatch.build_other: array"),
                    })
                    .collect();
                let mut l = 0usize;
                while all_lengths.contains(&l) {
                    l += 1;
                }
                let desc = Desc::Array(self.omegas(l));
                Ok(self.make_pat_like(desc, p))
            }
            _ => Ok(self.omega),
        }
    }

    fn make_other_variant(&mut self, p: P, tag: &str, constant: bool) -> P {
        let arg = if constant { None } else { Some(self.omega) };
        self.make_pat_like(
            Desc::Variant {
                label: Cow::Owned(tag.to_string()),
                arg,
            },
            p,
        )
    }

    // ---------------------------------------------------------------------
    // Satisfiability (parmatch.ml:1168-1305)
    // ---------------------------------------------------------------------

    /// `has_instance p` (parmatch.ml:1177-1190).
    fn has_instance(&mut self, p: P) -> bool {
        match self.desc(p).clone() {
            Desc::Variant { label, arg } => {
                if self.is_absent(p, &label) {
                    false
                } else {
                    match arg {
                        None => true,
                        Some(arg) => self.has_instance(arg),
                    }
                }
            }
            Desc::Any | Desc::Var(_) | Desc::Constant(_) | Desc::Interval(..) => true,
            Desc::Alias(p) => self.has_instance(p),
            Desc::Or(p1, p2) => self.has_instance(p1) || self.has_instance(p2),
            Desc::Construct { args: ps, .. } | Desc::Tuple(ps) | Desc::Array(ps) => {
                self.has_instances(&ps)
            }
            Desc::Record { fields, .. } => {
                let ps: Vec<P> = fields.iter().map(|f| f.pat).collect();
                self.has_instances(&ps)
            }
        }
    }

    fn has_instances(&mut self, ps: &[P]) -> bool {
        ps.iter().all(|p| self.has_instance(*p))
    }

    /// `satisfiable pss qs` (parmatch.ml:1207-1243).
    pub fn satisfiable(&mut self, pss: &[Row], qs: &[P]) -> bool {
        if pss.is_empty() {
            return self.has_instances(qs);
        }
        let Some((&q, qs_rest)) = qs.split_first() else {
            return false;
        };
        match self.desc(q).clone() {
            Desc::Or(q1, q2) => {
                self.satisfiable(pss, &prepend(q1, qs_rest))
                    || self.satisfiable(pss, &prepend(q2, qs_rest))
            }
            Desc::Alias(q) => self.satisfiable(pss, &prepend(q, qs_rest)),
            Desc::Any | Desc::Var(_) => {
                let column = self.simplified_first_col(pss);
                if !self.all_coherent(&column) {
                    return false;
                }
                let heads = Self::heads(pss);
                let omega = self.omega;
                let q0 = self.discr_pat(omega, &heads);
                let constrs = self.filter_all(q0, pss);
                if constrs.is_empty() {
                    let extra = self.filter_extra(pss);
                    return self.satisfiable(&extra, qs_rest);
                }
                if self.full_match(false, &constrs) {
                    for (p, pss) in &constrs {
                        if self.is_absent_pat(*p) {
                            continue;
                        }
                        let mut row = self.simple_match_args(*p, omega);
                        row.extend_from_slice(qs_rest);
                        if self.satisfiable(pss, &row) {
                            return true;
                        }
                    }
                    false
                } else {
                    let extra = self.filter_extra(pss);
                    self.satisfiable(&extra, qs_rest)
                }
            }
            Desc::Variant { label, .. } if self.is_absent(q, &label) => false,
            _ => {
                let mut column = vec![q];
                column.extend(self.simplified_first_col(pss));
                if !self.all_coherent(&column) {
                    return false;
                }
                let heads = Self::heads(pss);
                let q0 = self.discr_pat(q, &heads);
                for q0 in self.split_int_range(q0, &column[1..]) {
                    let filtered = self.filter_one(q0, pss);
                    let mut row = self.simple_match_args(q0, q);
                    row.extend_from_slice(qs_rest);
                    if self.satisfiable(&filtered, &row) {
                        return true;
                    }
                }
                false
            }
        }
    }

    /// `satisfiables pss qs` (parmatch.ml:1248-1293).
    pub fn satisfiables(&mut self, pss: &[Row], qs: &[P]) -> Vec<Row> {
        if pss.is_empty() {
            return if self.has_instances(qs) {
                vec![qs.to_vec()]
            } else {
                Vec::new()
            };
        }
        let Some((&q, qs_rest)) = qs.split_first() else {
            return Vec::new();
        };
        match self.desc(q).clone() {
            Desc::Or(q1, q2) => {
                let mut result = self.satisfiables(pss, &prepend(q1, qs_rest));
                result.extend(self.satisfiables(pss, &prepend(q2, qs_rest)));
                result
            }
            Desc::Alias(q) => self.satisfiables(pss, &prepend(q, qs_rest)),
            Desc::Any | Desc::Var(_) => {
                let column = self.simplified_first_col(pss);
                if !self.all_coherent(&column) {
                    return Vec::new();
                }
                let heads = Self::heads(pss);
                let omega = self.omega;
                let q0 = self.discr_pat(omega, &heads);
                let constrs = self.filter_all(q0, pss);
                if constrs.is_empty() {
                    return self.satisfiables_wild(pss, omega, qs_rest);
                }
                let first = constrs[0].0;
                if self.full_match(false, &constrs) {
                    self.satisfiables_for_constrs(&constrs, qs_rest)
                } else if matches!(self.desc(first), Desc::Construct { .. }) {
                    let other = match self.build_other_constrs(&constrs, first) {
                        Ok(other) => other,
                        Err(Empty) => crate::misc::fatal_error("Parmatch.satisfiables"),
                    };
                    let mut result = self.satisfiables_wild(pss, other, qs_rest);
                    result.extend(self.satisfiables_for_constrs(&constrs, qs_rest));
                    result
                } else {
                    self.satisfiables_wild(pss, omega, qs_rest)
                }
            }
            Desc::Variant { label, .. } if self.is_absent(q, &label) => Vec::new(),
            _ => {
                let mut column = vec![q];
                column.extend(self.simplified_first_col(pss));
                if !self.all_coherent(&column) {
                    return Vec::new();
                }
                let heads = Self::heads(pss);
                let q0 = self.discr_pat(q, &heads);
                let mut results = Vec::new();
                for q0 in self.split_int_range(q0, &column[1..]) {
                    let filtered = self.filter_one(q0, pss);
                    let mut row = self.simple_match_args(q0, q);
                    row.extend_from_slice(qs_rest);
                    for r in self.satisfiables(&filtered, &row) {
                        results.push(self.set_args(q0, &r));
                    }
                }
                results
            }
        }
    }

    fn satisfiables_wild(&mut self, pss: &[Row], p: P, qs_rest: &[P]) -> Vec<Row> {
        let extra = self.filter_extra(pss);
        self.satisfiables(&extra, qs_rest)
            .into_iter()
            .map(|qs| prepend(p, &qs))
            .collect()
    }

    fn satisfiables_for_constrs(&mut self, constrs: &[(P, Vec<Row>)], qs_rest: &[P]) -> Vec<Row> {
        let omega = self.omega;
        let mut result = Vec::new();
        for (p, pss) in constrs {
            if self.is_absent_pat(*p) {
                continue;
            }
            let mut row = self.simple_match_args(*p, omega);
            row.extend_from_slice(qs_rest);
            for r in self.satisfiables(pss, &row) {
                result.push(self.set_args(*p, &r));
            }
        }
        result
    }

    // ---------------------------------------------------------------------
    // Exhaustiveness (parmatch.ml:1366-1475)
    // ---------------------------------------------------------------------

    fn exhaust_gadt_aux(
        &mut self,
        count: &mut usize,
        ext: Option<&Path>,
        pss: &[Row],
        n: usize,
    ) -> ExhaustResult {
        if *count > EXHAUST_GADT_LIMIT {
            return None;
        }
        *count += 1;
        if pss.is_empty() {
            return Some(vec![self.omegas(n)]);
        }
        if pss[0].is_empty() {
            return None;
        }
        let column = self.simplified_first_col(pss);
        if !self.all_coherent(&column) {
            return None;
        }
        let heads = Self::heads(pss);
        let omega = self.omega;
        let q0 = self.discr_pat(omega, &heads);
        let constrs = self.filter_all(q0, pss);
        if constrs.is_empty() {
            let extra = self.filter_extra(pss);
            return self
                .exhaust_gadt_aux(count, ext, &extra, n.saturating_sub(1))
                .map(|rows| rows.into_iter().map(|row| prepend(q0, &row)).collect());
        }
        // `try_many_gadt try_non_omega constrs`: results appended in order.
        let mut before: ExhaustResult = None;
        for (p, pss) in &constrs {
            let r = if self.is_absent_pat(*p) {
                None
            } else {
                let arity = self.simple_match_args(*p, omega).len();
                self.exhaust_gadt_aux(count, ext, pss, (arity + n).saturating_sub(1))
                    .map(|rows| {
                        rows.into_iter()
                            .map(|row| self.set_args(*p, &row))
                            .collect()
                    })
            };
            before = rappend(before, r);
        }
        if self.full_match(false, &constrs) && !self.should_extend(ext, &constrs) {
            return before;
        }
        let extra = self.filter_extra(pss);
        match self.exhaust_gadt_aux(count, ext, &extra, n.saturating_sub(1)) {
            None => before,
            Some(r) => {
                let p = match self.build_other(ext, &constrs) {
                    Ok(p) => p,
                    Err(Empty) => crate::misc::fatal_error("Parmatch.exhaust"),
                };
                let dug: Vec<Row> = r.into_iter().map(|tail| prepend(p, &tail)).collect();
                match before {
                    None => Some(dug),
                    Some(mut x) => {
                        x.extend(dug);
                        Some(x)
                    }
                }
            }
        }
    }

    /// `exhaust_gadt ext pss n` (parmatch.ml:1457-1475).
    pub fn exhaust_gadt(&mut self, ext: Option<&Path>, pss: &[Row], n: usize) -> Option<Vec<P>> {
        let mut count = 0;
        match self.exhaust_gadt_aux(&mut count, ext, pss, n) {
            None => None,
            Some(lst) if lst.is_empty() => Some(self.omegas(n)),
            Some(lst) => {
                let singletons: Vec<P> = lst
                    .into_iter()
                    .map(|row| match row.as_slice() {
                        [x] => *x,
                        _ => panic!("Parmatch.exhaust_gadt: singleton"),
                    })
                    .collect();
                Some(vec![self.orify_many(&singletons)])
            }
        }
    }

    // ---------------------------------------------------------------------
    // Variant pressure (parmatch.ml:1477-1515, 1766-1771)
    // ---------------------------------------------------------------------

    fn pressure_variants_rows(&mut self, tdefs: Option<EnvRef>, pss: &[Row]) -> bool {
        if pss.is_empty() {
            return false;
        }
        if pss[0].is_empty() {
            return true;
        }
        let column = self.simplified_first_col(pss);
        if !self.all_coherent(&column) {
            return true;
        }
        let heads = Self::heads(pss);
        let omega = self.omega;
        let q0 = self.discr_pat(omega, &heads);
        let constrs = self.filter_all(q0, pss);
        if constrs.is_empty() {
            let extra = self.filter_extra(pss);
            return self.pressure_variants_rows(tdefs, &extra);
        }
        if self.full_match(tdefs.is_none(), &constrs) {
            return self.pressure_try_non_omega(tdefs, &constrs);
        }
        let Some(env) = tdefs else {
            let extra = self.filter_extra(pss);
            return self.pressure_variants_rows(None, &extra);
        };
        let full = self.full_match(true, &constrs);
        let ok = if full {
            self.pressure_try_non_omega(tdefs, &constrs)
        } else {
            let marked = self.mark_partial(pss);
            let groups = self.filter_all(q0, &marked);
            self.pressure_try_non_omega(tdefs, &groups)
        };
        let first = constrs[0].0;
        if matches!(self.desc(first), Desc::Variant { .. }) {
            let node = self.node(first);
            let (penv, pty) = (node.env, node.ty.expect("variant pattern type"));
            let row = self.oracle.row_of(penv, pty);
            let fixed = crate::types::btype::row_fixed(self.oracle.ctx(), &row);
            let extra = self.filter_extra(pss);
            if !(fixed || self.pressure_variants_rows(None, &extra)) {
                self.oracle.close_variant(env, penv, pty);
            }
        }
        ok
    }

    fn pressure_try_non_omega(&mut self, tdefs: Option<EnvRef>, groups: &[(P, Vec<Row>)]) -> bool {
        let mut all = true;
        for (_, pss) in groups {
            let ok = self.pressure_variants_rows(tdefs, pss);
            all = all && ok;
        }
        all
    }

    /// Exported `pressure_variants tdefs patl` (parmatch.ml:1766-1771).
    pub fn pressure_variants(&mut self, tdefs: EnvRef, patl: &[P]) {
        let omega = self.omega;
        let pss: Vec<Row> = patl.iter().map(|p| vec![*p, omega]).collect();
        self.pressure_variants_rows(Some(tdefs), &pss);
    }
}

/// `exhaust_gadt_limit` (parmatch.ml:1375).
const EXHAUST_GADT_LIMIT: usize = 1000;

fn prepend(p: P, rest: &[P]) -> Row {
    let mut row = Vec::with_capacity(rest.len() + 1);
    row.push(p);
    row.extend_from_slice(rest);
    row
}

/// `rappend r1 r2`.
fn rappend(r1: ExhaustResult, r2: ExhaustResult) -> ExhaustResult {
    match (r1, r2) {
        (None, r) | (r, None) => r,
        (Some(mut l1), Some(l2)) => {
            l1.extend(l2);
            Some(l1)
        }
    }
}

// ---------------------------------------------------------------------------
// Usefulness of clauses (parmatch.ml:1517-1755)
// ---------------------------------------------------------------------------

/// `answer` (parmatch.ml:1525-1528).
#[derive(Debug, Clone)]
enum Answer {
    Used,
    Unused,
    Upartial(Vec<P>),
}

/// `'a row` (parmatch.ml:1534): `no_ors` and `ors` are kept reversed, like
/// OCaml's lists built with `::`.
#[derive(Debug, Clone)]
struct URow {
    no_ors: Vec<P>,
    ors: Vec<P>,
    active: Vec<P>,
}

fn make_row(ps: Vec<P>) -> URow {
    URow {
        no_ors: Vec::new(),
        ors: Vec::new(),
        active: ps,
    }
}

/// `union_res r1 r2`.
/// `pieces_res rs`: an interval split into pieces is used when one of its
/// pieces is. An or-pattern below it is unused when every used piece reports
/// it unused.
fn pieces_res(rs: Vec<Answer>) -> Answer {
    let used: Vec<Answer> = rs
        .into_iter()
        .filter(|r| !matches!(r, Answer::Unused))
        .collect();
    if used.is_empty() {
        return Answer::Unused;
    }
    if used.iter().any(|r| matches!(r, Answer::Used)) {
        return Answer::Used;
    }
    let mut partials = used.into_iter().map(|r| match r {
        Answer::Upartial(u) => u,
        _ => Vec::new(),
    });
    match partials.next() {
        None => Answer::Used,
        Some(u) => {
            let us: Vec<Vec<P>> = partials.collect();
            Answer::Upartial(
                u.into_iter()
                    .filter(|p| us.iter().all(|u| u.contains(p)))
                    .collect(),
            )
        }
    }
}

fn union_res(r1: Answer, r2: Answer) -> Answer {
    match (r1, r2) {
        (Answer::Unused, _) | (_, Answer::Unused) => Answer::Unused,
        (Answer::Used, r) | (r, Answer::Used) => r,
        (Answer::Upartial(mut u1), Answer::Upartial(u2)) => {
            u1.extend(u2);
            Answer::Upartial(u1)
        }
    }
}

impl<'a, O: Oracle> Parmatch<'a, O> {
    fn unalias(&self, p: P) -> P {
        match self.desc(p) {
            Desc::Alias(p) => self.unalias(*p),
            _ => p,
        }
    }

    fn is_var(&self, p: P) -> bool {
        self.head_is_var(self.unalias(p))
    }

    fn is_var_column(&self, rs: &[URow]) -> bool {
        rs.iter().all(|r| self.is_var(r.active[0]))
    }

    fn or_args(&self, p: P) -> (P, P) {
        match self.desc(p) {
            Desc::Or(p1, p2) => (*p1, *p2),
            Desc::Alias(p) => self.or_args(*p),
            _ => panic!("Parmatch.or_args"),
        }
    }

    fn remove(r: &URow) -> URow {
        URow {
            active: r.active[1..].to_vec(),
            ..r.clone()
        }
    }

    fn push_no_or(r: &URow) -> URow {
        let mut no_ors = vec![r.active[0]];
        no_ors.extend_from_slice(&r.no_ors);
        URow {
            no_ors,
            ors: r.ors.clone(),
            active: r.active[1..].to_vec(),
        }
    }

    fn push_or(r: &URow) -> URow {
        let mut ors = vec![r.active[0]];
        ors.extend_from_slice(&r.ors);
        URow {
            no_ors: r.no_ors.clone(),
            ors,
            active: r.active[1..].to_vec(),
        }
    }

    /// `filter_one q rs` on rows (parmatch.ml:1605-1623).
    fn filter_one_rows(&self, q: P, rs: &[URow]) -> Vec<URow> {
        let mut out = Vec::new();
        let mut stack: Vec<URow> = rs.iter().rev().cloned().collect();
        while let Some(r) = stack.pop() {
            let (&p, ps) = r
                .active
                .split_first()
                .expect("Parmatch.filter_one: empty row");
            match self.desc(p) {
                Desc::Alias(inner) => stack.push(URow {
                    active: prepend(*inner, ps),
                    ..r.clone()
                }),
                Desc::Or(p1, p2) => {
                    let (p1, p2) = (*p1, *p2);
                    stack.push(URow {
                        active: prepend(p2, ps),
                        ..r.clone()
                    });
                    stack.push(URow {
                        active: prepend(p1, ps),
                        ..r.clone()
                    });
                }
                _ => {
                    if self.simple_match(q, p) {
                        let mut active = self.simple_match_args(q, p);
                        active.extend_from_slice(ps);
                        out.push(URow {
                            active,
                            ..r.clone()
                        });
                    }
                }
            }
        }
        out
    }

    fn make_vector(r: &URow) -> Vec<P> {
        r.no_ors.iter().rev().copied().collect()
    }

    /// `extract_elements qs` (parmatch.ml:1639-1646).
    fn extract_elements(qs: &URow) -> Vec<URow> {
        let mut out = Vec::new();
        for (i, &q) in qs.ors.iter().enumerate() {
            // List.rev_append seen rem @ qs.no_ors
            let mut no_ors: Vec<P> = qs.ors[..i].iter().rev().copied().collect();
            no_ors.extend_from_slice(&qs.ors[i + 1..]);
            no_ors.extend_from_slice(&qs.no_ors);
            out.push(URow {
                no_ors,
                ors: Vec::new(),
                active: vec![q],
            });
        }
        out
    }

    /// `extract_columns pss qs` (parmatch.ml:1649-1662): one list per or
    /// column, whose rows are in reverse order (`transpose` folds left).
    fn extract_columns(pss: &[URow], qs: &URow) -> Vec<Vec<URow>> {
        if pss.is_empty() {
            return vec![Vec::new(); qs.ors.len()];
        }
        let rows: Vec<Vec<URow>> = pss.iter().map(Self::extract_elements).collect();
        let width = rows[0].len();
        (0..width)
            .map(|j| rows.iter().rev().map(|row| row[j].clone()).collect())
            .collect()
    }

    fn simplified_first_usefulness_col(&self, rows: &[URow]) -> Vec<P> {
        let mut column = Vec::new();
        for row in rows {
            self.simplify_head_pat(row.active[0], &mut column);
        }
        column
    }

    /// `every_satisfiables pss qs` (parmatch.ml:1674-1726).
    fn every_satisfiables(&mut self, pss: &[URow], qs: &URow) -> Answer {
        let Some((&q, rem)) = qs.active.split_first() else {
            if qs.ors.is_empty() {
                let matrix: Vec<Row> = pss.iter().map(Self::make_vector).collect();
                let vector = Self::make_vector(qs);
                return if self.satisfiable(&matrix, &vector) {
                    Answer::Used
                } else {
                    Answer::Unused
                };
            }
            // n or-patterns -> 2n expansions; `fold_right2` visits the last
            // column first.
            let columns = Self::extract_columns(pss, qs);
            let elements = Self::extract_elements(qs);
            let mut r = Answer::Used;
            for (pss, qs) in columns.iter().zip(&elements).rev() {
                if matches!(r, Answer::Unused) {
                    continue;
                }
                let [q] = qs.active.as_slice() else {
                    panic!("Parmatch.every_satisfiables");
                };
                let (q1, q2) = self.or_args(*q);
                let r_loc = self.every_both(pss, qs, q1, q2);
                r = union_res(r, r_loc);
            }
            return r;
        };
        let uq = self.unalias(q);
        match self.desc(uq).clone() {
            Desc::Any | Desc::Var(_) => {
                if self.is_var_column(pss) {
                    let pss: Vec<URow> = pss.iter().map(Self::remove).collect();
                    self.every_satisfiables(&pss, &Self::remove(qs))
                } else {
                    let pss: Vec<URow> = pss.iter().map(Self::push_no_or).collect();
                    self.every_satisfiables(&pss, &Self::push_no_or(qs))
                }
            }
            Desc::Or(q1, q2) => {
                let ghost = self.oracle.is_ghost(self.node(q1).loc)
                    && self.oracle.is_ghost(self.node(q2).loc);
                if ghost {
                    let pss: Vec<URow> = pss.iter().map(Self::push_no_or).collect();
                    self.every_satisfiables(&pss, &Self::push_no_or(qs))
                } else {
                    let pss: Vec<URow> = pss.iter().map(Self::push_or).collect();
                    self.every_satisfiables(&pss, &Self::push_or(qs))
                }
            }
            Desc::Variant { label, .. } if self.is_absent(uq, &label) => Answer::Unused,
            _ => {
                let mut column = vec![uq];
                column.extend(self.simplified_first_usefulness_col(pss));
                if !self.all_coherent(&column) {
                    return Answer::Unused;
                }
                let heads: Vec<P> = pss.iter().map(|r| r.active[0]).collect();
                let q0 = self.discr_pat(q, &heads);
                let piece = |this: &mut Self, q0: P| {
                    let filtered = this.filter_one_rows(q0, pss);
                    let mut active = this.simple_match_args(q0, q);
                    active.extend_from_slice(rem);
                    this.every_satisfiables(
                        &filtered,
                        &URow {
                            active,
                            ..qs.clone()
                        },
                    )
                };
                match self.split_int_range(q0, &column[1..]).as_slice() {
                    [q0] => piece(self, *q0),
                    q0s => {
                        let rs = q0s.iter().map(|q0| piece(self, *q0)).collect();
                        pieces_res(rs)
                    }
                }
            }
        }
    }

    /// `every_both pss qs q1 q2` (parmatch.ml:1737-1754).
    fn every_both(&mut self, pss: &[URow], qs: &URow, q1: P, q2: P) -> Answer {
        let qs1 = URow {
            active: vec![q1],
            ..qs.clone()
        };
        let qs2 = URow {
            active: vec![q2],
            ..qs.clone()
        };
        let r1 = self.every_satisfiables(pss, &qs1);
        let r2 = if self.compat(q1, q2) {
            let mut extended = vec![qs1.clone()];
            extended.extend_from_slice(pss);
            self.every_satisfiables(&extended, &qs2)
        } else {
            self.every_satisfiables(pss, &qs2)
        };
        match r1 {
            Answer::Unused => match r2 {
                Answer::Unused => Answer::Unused,
                Answer::Used => Answer::Upartial(vec![q1]),
                Answer::Upartial(u2) => Answer::Upartial(prepend(q1, &u2)),
            },
            Answer::Used => match r2 {
                Answer::Unused => Answer::Upartial(vec![q2]),
                r2 => r2,
            },
            Answer::Upartial(mut u1) => match r2 {
                Answer::Unused => {
                    u1.push(q2);
                    Answer::Upartial(u1)
                }
                Answer::Used => Answer::Upartial(u1),
                Answer::Upartial(u2) => {
                    u1.extend(u2);
                    Answer::Upartial(u1)
                }
            },
        }
    }

    /// `le_pat p q` (parmatch.ml:1757-1777).
    fn le_pat(&mut self, p: P, q: P) -> bool {
        enum Step {
            Done(bool),
            Pat(P, P),
            Pats(Vec<P>, Vec<P>),
            NotSatisfiable,
        }
        let step = match (self.desc(p), self.desc(q)) {
            (Desc::Var(_) | Desc::Any, _) => Step::Done(true),
            (Desc::Alias(p), _) => Step::Pat(*p, q),
            (_, Desc::Alias(q)) => Step::Pat(p, *q),
            (Desc::Constant(c1), Desc::Constant(c2)) => {
                Step::Done(const_compare(c1, c2) == std::cmp::Ordering::Equal)
            }
            (Desc::Constant(_) | Desc::Interval(..), Desc::Constant(_) | Desc::Interval(..)) => {
                Step::Done(match (self.int_range(p), self.int_range(q)) {
                    (Some((lo1, hi1)), Some((lo2, hi2))) => lo1 <= lo2 && hi2 <= hi1,
                    _ => false,
                })
            }
            (
                Desc::Construct {
                    cstr: c1, args: ps, ..
                },
                Desc::Construct {
                    cstr: c2, args: qs, ..
                },
            ) => {
                if same_constructor(c1, c2) {
                    Step::Pats(ps.clone(), qs.clone())
                } else {
                    Step::Done(false)
                }
            }
            (
                Desc::Variant {
                    label: l1,
                    arg: Some(p1),
                },
                Desc::Variant {
                    label: l2,
                    arg: Some(p2),
                },
            ) => {
                if l1 == l2 {
                    Step::Pat(*p1, *p2)
                } else {
                    Step::Done(false)
                }
            }
            (
                Desc::Variant {
                    label: l1,
                    arg: None,
                },
                Desc::Variant {
                    label: l2,
                    arg: None,
                },
            ) => Step::Done(l1 == l2),
            (Desc::Variant { .. }, Desc::Variant { .. }) => Step::Done(false),
            (Desc::Tuple(ps), Desc::Tuple(qs)) => Step::Pats(ps.clone(), qs.clone()),
            (Desc::Record { fields: l1, .. }, Desc::Record { fields: l2, .. }) => {
                let (ps, qs) = self.records_args(l1, l2);
                Step::Pats(ps, qs)
            }
            (Desc::Array(ps), Desc::Array(qs)) => {
                if ps.len() == qs.len() {
                    Step::Pats(ps.clone(), qs.clone())
                } else {
                    Step::Done(false)
                }
            }
            _ => Step::NotSatisfiable,
        };
        match step {
            Step::Done(result) => result,
            Step::Pat(p, q) => self.le_pat(p, q),
            Step::Pats(ps, qs) => self.le_pats(&ps, &qs),
            Step::NotSatisfiable => !self.satisfiable(&[vec![p]], &[q]),
        }
    }

    fn le_pats(&mut self, ps: &[P], qs: &[P]) -> bool {
        ps.iter().zip(qs).all(|(p, q)| self.le_pat(*p, *q))
    }

    /// `get_mins le_pats ps` (parmatch.ml `get_mins`).
    fn get_mins(&mut self, ps: Vec<Row>) -> Vec<Row> {
        let once = self.select_rec(ps);
        self.select_rec(once)
    }

    /// `select_rec [] ps`: keeps each row not covered by a later row, and
    /// reverses the order.
    fn select_rec(&mut self, pss: Vec<Row>) -> Vec<Row> {
        let mut kept: Vec<usize> = Vec::new();
        for i in (0..pss.len()).rev() {
            let dominated = (i + 1..pss.len()).any(|j| self.le_pats(&pss[j], &pss[i]));
            if !dominated {
                kept.push(i);
            }
        }
        // `kept` holds indices last-to-first, which is the reversed order.
        let mut pss: Vec<Option<Row>> = pss.into_iter().map(Some).collect();
        kept.into_iter()
            .map(|i| pss[i].take().expect("each row is kept once"))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Diagnostics (parmatch.ml:1853-2317)
// ---------------------------------------------------------------------------

impl<'a, O: Oracle> Parmatch<'a, O> {
    /// Import an owned typed pattern (a counter-example), without a source
    /// reference.
    /// Import a counter-example returned by [`Oracle::pred`], whose
    /// sub-patterns are in the oracle's scratch arena, without a source
    /// reference.
    fn import_owned(&mut self, pat: &Pattern) -> P {
        let desc = match &pat.pat_desc {
            PatternDesc::Tpat_any => Desc::Any,
            PatternDesc::Tpat_var(_, _) => Desc::Var(VarKind::Source),
            PatternDesc::Tpat_alias(inner, _, _) => Desc::Alias(self.import_scratch(*inner)),
            PatternDesc::Tpat_constant(c) => Desc::Constant(Cow::Owned(c.clone())),
            PatternDesc::Tpat_interval(lo, hi) => Desc::Interval(lo.constant(), hi.constant()),
            PatternDesc::Tpat_tuple(items) => Desc::Tuple(self.import_scratch_list(*items)),
            PatternDesc::Tpat_construct(lid, cstr, args) => Desc::Construct {
                lid: Some(*lid),
                cstr: std::sync::Arc::clone(cstr),
                args: self.import_scratch_list(*args),
            },
            PatternDesc::Tpat_variant(label, arg, _) => Desc::Variant {
                label: Cow::Owned(label.clone()),
                arg: arg.map(|arg| self.import_scratch(arg)),
            },
            PatternDesc::Tpat_record(fields, closed, rest) => Desc::Record {
                fields: fields
                    .iter()
                    .map(|(lid, lbl, p, opt)| Field {
                        lid: Some(*lid),
                        lbl: Cow::Owned((**lbl).clone()),
                        pat: self.import_scratch(*p),
                        opt: *opt,
                    })
                    .collect(),
                closed: *closed,
                has_rest: rest.is_some(),
            },
            PatternDesc::Tpat_array(items) => Desc::Array(self.import_scratch_list(*items)),
            // Callers lower dict patterns to records first (`Dict_pattern`).
            PatternDesc::Tpat_dict(_) => crate::misc::fatal_error("Parmatch.import: dict pattern"),
            PatternDesc::Tpat_or(left, right, _) => {
                Desc::Or(self.import_scratch(*left), self.import_scratch(*right))
            }
        };
        self.push(desc, Some(pat.pat_type), pat.pat_env, pat.pat_loc, None)
    }

    fn import_scratch(&mut self, pat: TPatIdx) -> P {
        let pat = self.oracle.scratch().pattern(pat).clone();
        self.import_owned(&pat)
    }

    fn import_scratch_list(&mut self, pats: TPatList) -> Vec<P> {
        let pats = self.oracle.scratch().pattern_list(pats).to_vec();
        pats.into_iter()
            .map(|pat| self.import_scratch(pat))
            .collect()
    }

    /// Export a node into the scratch arena.
    fn export_idx(&mut self, p: P) -> TPatIdx {
        let pat = self.export(p);
        self.oracle.scratch_mut().push_pattern(pat)
    }

    fn export_list(&mut self, ps: Vec<P>) -> TPatList {
        let handles: Vec<TPatIdx> = ps.into_iter().map(|p| self.export_idx(p)).collect();
        self.oracle.scratch_mut().push_pattern_list(&handles)
    }

    /// Export a node as a typed-tree pattern (the input of `Conv.conv`).
    /// Its sub-patterns are stored in the oracle's scratch arena.
    pub fn export(&mut self, p: P) -> Pattern {
        let node = self.node(p).clone();
        let ty = match node.ty {
            Some(ty) => ty,
            None => self.oracle.none_type(),
        };
        let desc = match node.desc {
            Desc::Any | Desc::Var(VarKind::Extra) => PatternDesc::Tpat_any,
            Desc::Var(VarKind::Source) => match node.src.map(|src| &src.pat_desc) {
                Some(PatternDesc::Tpat_var(id, name)) => PatternDesc::Tpat_var(*id, name.clone()),
                _ => PatternDesc::Tpat_any,
            },
            Desc::Var(VarKind::Extension(ident, loc)) => PatternDesc::Tpat_var(
                ident,
                crate::parse_arena::Located {
                    txt: "*extension*".to_string(),
                    loc,
                },
            ),
            Desc::Alias(inner) => match node.src.map(|src| &src.pat_desc) {
                Some(PatternDesc::Tpat_alias(_, id, name)) => {
                    PatternDesc::Tpat_alias(self.export_idx(inner), *id, name.clone())
                }
                _ => return self.export(inner),
            },
            Desc::Constant(c) => PatternDesc::Tpat_constant(c.into_owned()),
            Desc::Interval(lo, hi) => PatternDesc::Tpat_interval(crate::types::typedtree::IntervalBound::from_constant(lo), crate::types::typedtree::IntervalBound::from_constant(hi)),
            Desc::Tuple(items) => PatternDesc::Tpat_tuple(self.export_list(items)),
            Desc::Construct { lid, cstr, args } => {
                let lid = lid.unwrap_or_else(|| crate::parse_arena::Located {
                    txt: self.oracle.placeholder_lid(),
                    loc: LocIdx::none(),
                });
                PatternDesc::Tpat_construct(lid, cstr, self.export_list(args))
            }
            Desc::Variant { label, arg } => PatternDesc::Tpat_variant(
                label.into_owned(),
                arg.map(|arg| self.export_idx(arg)),
                crate::types::typedtree::RowDescRef(0),
            ),
            Desc::Record {
                fields,
                closed,
                has_rest,
            } => {
                let rest = if has_rest {
                    match node.src.map(|src| &src.pat_desc) {
                        Some(PatternDesc::Tpat_record(_, _, rest)) => rest.clone(),
                        _ => None,
                    }
                } else {
                    None
                };
                let placeholder = self.oracle.placeholder_lid();
                PatternDesc::Tpat_record(
                    fields
                        .into_iter()
                        .map(|field| {
                            let lid = field.lid.unwrap_or(crate::parse_arena::Located {
                                txt: placeholder,
                                loc: LocIdx::none(),
                            });
                            (
                                lid,
                                std::sync::Arc::new(field.lbl.into_owned()),
                                self.export_idx(field.pat),
                                field.opt,
                            )
                        })
                        .collect(),
                    closed,
                    rest,
                )
            }
            Desc::Array(items) => PatternDesc::Tpat_array(self.export_list(items)),
            Desc::Or(p1, p2) => {
                let p1 = self.export_idx(p1);
                let p2 = self.export_idx(p2);
                PatternDesc::Tpat_or(p1, p2, None)
            }
        };
        let attributes = node
            .src
            .map(|src| self.ta.pat_attributes(src).clone())
            .unwrap_or_default();
        self.oracle
            .scratch_mut()
            .with_pat_attributes(Pattern::new(desc, node.loc, ty, node.env), attributes)
    }

    /// `initial_matrix casel` (parmatch.ml:1783-1787).
    fn initial_matrix(&mut self, casel: &[CaseRef<'a>]) -> Vec<Row> {
        casel
            .iter()
            .filter(|case| !case.guarded)
            // `check_partial_gadt` maps `with_bool_payload_overlaps` over the
            // cases.
            .map(|case| vec![self.import_with_bool_payload_overlaps(case.lhs)])
            .collect()
    }

    /// `do_match pss qs` (parmatch.ml:1835-1856).
    fn do_match(&mut self, pss: Vec<(Row, LocIdx)>, qs: &[P]) -> Option<LocIdx> {
        let Some((&q, qs_rest)) = qs.split_first() else {
            return match pss.first() {
                Some((row, loc)) if row.is_empty() => Some(*loc),
                _ => None,
            };
        };
        match self.desc(q).clone() {
            Desc::Or(q1, q2) => self
                .do_match(pss.clone(), &prepend(q1, qs_rest))
                .or_else(|| self.do_match(pss, &prepend(q2, qs_rest))),
            Desc::Any => {
                // do_filter_var: stops at the first empty row.
                let mut filtered = Vec::new();
                for (row, loc) in pss {
                    let Some((_, ps)) = row.split_first() else {
                        break;
                    };
                    filtered.push((ps.to_vec(), loc));
                }
                self.do_match(filtered, qs_rest)
            }
            _ => {
                let q0 = self.normalize_pat(q);
                let filtered = self.do_filter_one(q0, pss);
                let mut row = self.simple_match_args(q0, q);
                row.extend_from_slice(qs_rest);
                self.do_match(filtered, &row)
            }
        }
    }

    /// `do_filter_one q pss` (parmatch.ml:1821-1833).
    fn do_filter_one(&self, q: P, pss: Vec<(Row, LocIdx)>) -> Vec<(Row, LocIdx)> {
        let mut out = Vec::new();
        let mut stack: Vec<(Row, LocIdx)> = pss.into_iter().rev().collect();
        while let Some((row, loc)) = stack.pop() {
            let Some((&p, ps)) = row.split_first() else {
                return out;
            };
            match self.desc(p) {
                Desc::Alias(inner) => stack.push((prepend(*inner, ps), loc)),
                Desc::Or(p1, p2) => {
                    let (p1, p2) = (*p1, *p2);
                    stack.push((prepend(p2, ps), loc));
                    stack.push((prepend(p1, ps), loc));
                }
                _ => {
                    if self.simple_match(q, p) {
                        let mut new_row = self.simple_match_args(q, p);
                        new_row.extend_from_slice(ps);
                        out.push((new_row, loc));
                    }
                }
            }
        }
        out
    }

    /// `check_partial_all v casel` (parmatch.ml:1858-1862).
    fn check_partial_all(&mut self, v: &Pattern, casel: &[CaseRef<'a>]) -> Option<LocIdx> {
        // initial_all raises NoGuard when no clause has a guard.
        if casel.iter().all(|case| !case.guarded) {
            return None;
        }
        let pss: Vec<(Row, LocIdx)> = casel
            .iter()
            .map(|case| {
                (
                    vec![self.import_with_bool_payload_overlaps(case.lhs)],
                    case.lhs.pat_loc,
                )
            })
            .collect();
        let v = self.import_owned(v);
        self.do_match(pss, &[v])
    }

    /// `do_check_partial ?partial_match_warning_hint ~pred exhaust loc casel pss`
    /// (parmatch.ml:2019-2092).
    fn do_check_partial(
        &mut self,
        hint: Option<&str>,
        loc: LocIdx,
        casel: &[CaseRef<'a>],
        pss: &[Row],
    ) -> Partiality {
        let Some(ps) = pss.first() else {
            if !casel.is_empty() && self.oracle.is_active(&ParmatchWarning::AllClausesGuarded) {
                self.oracle.warn(loc, ParmatchWarning::AllClausesGuarded);
            }
            return Partiality::Partial;
        };
        let n = ps.len();
        match self.exhaust_gadt(None, pss, n) {
            None => Partiality::Total,
            Some(row) if row.len() == 1 => {
                let u = self.export(row[0]);
                let Some(v) = self.oracle.pred(PredKind::Partial, u, None) else {
                    return Partiality::Total;
                };
                if self
                    .oracle
                    .is_active(&ParmatchWarning::PartialMatch(String::new()))
                {
                    let mut errmsg = String::from("| ");
                    errmsg.push_str(&self.oracle.print_pattern(&v));
                    if self.check_partial_all(&v, casel).is_some() {
                        errmsg.push_str("\n(However, some guarded clause may match this value.)");
                    }
                    if contains_extension(self.oracle.scratch(), &v) {
                        errmsg.push_str(
                            "\nMatching over values of extensible variant types (the *extension* above)\nmust include a wild card pattern in order to be exhaustive.",
                        );
                    }
                    if let Some(hint) = hint
                        && !hint.is_empty()
                    {
                        errmsg.push_str("\n\n  ");
                        errmsg.push_str(hint);
                    }
                    self.oracle.warn(loc, ParmatchWarning::PartialMatch(errmsg));
                }
                Partiality::Partial
            }
            Some(_) => crate::misc::fatal_error("Parmatch.check_partial"),
        }
    }

    /// `collect_paths_from_pat r p` (parmatch.ml:2112-2131).
    fn collect_paths_from_pat(&mut self, r: &mut Vec<Path>, p: &Pattern) {
        let ta = self.ta;
        match &p.pat_desc {
            PatternDesc::Tpat_construct(_, cstr, ps) => {
                if matches!(cstr.cstr_kind, ConstructorKind::Ordinary(_)) {
                    let path = self.oracle.type_path(p.pat_env, p.pat_type);
                    if !self.oracle.is_non_extendable_predef_path(&path)
                        && !r.iter().any(|x| x.same(&path))
                    {
                        r.push(path);
                    }
                }
                for p in ta.patterns(*ps) {
                    self.collect_paths_from_pat(r, p);
                }
            }
            PatternDesc::Tpat_any
            | PatternDesc::Tpat_var(..)
            | PatternDesc::Tpat_constant(_)
            | PatternDesc::Tpat_interval(..)
            | PatternDesc::Tpat_variant(_, None, _) => {}
            PatternDesc::Tpat_tuple(ps) | PatternDesc::Tpat_array(ps) => {
                for p in ta.patterns(*ps) {
                    self.collect_paths_from_pat(r, p);
                }
            }
            PatternDesc::Tpat_record(fields, _, _) => {
                for (_, _, p, _) in fields {
                    self.collect_paths_from_pat(r, ta.pattern(*p));
                }
            }
            PatternDesc::Tpat_dict(entries) => {
                for entry in entries {
                    self.collect_paths_from_pat(r, ta.pattern(entry.tdp_pattern));
                }
            }
            PatternDesc::Tpat_variant(_, Some(p), _) | PatternDesc::Tpat_alias(p, _, _) => {
                self.collect_paths_from_pat(r, ta.pattern(*p))
            }
            PatternDesc::Tpat_or(p1, p2, _) => {
                self.collect_paths_from_pat(r, ta.pattern(*p1));
                self.collect_paths_from_pat(r, ta.pattern(*p2));
            }
        }
    }

    /// `do_check_fragile_param exhaust loc casel pss` (parmatch.ml:2139-2155).
    fn do_check_fragile(&mut self, loc: LocIdx, casel: &[CaseRef<'a>], pss: &[Row]) {
        let mut exts = Vec::new();
        for case in casel {
            self.collect_paths_from_pat(&mut exts, case.lhs);
        }
        let Some(ps) = pss.first() else {
            return;
        };
        let n = ps.len();
        for ext in &exts {
            if self.exhaust_gadt(Some(ext), pss, n).is_none() {
                self.oracle
                    .warn(loc, ParmatchWarning::FragileMatch(ext.name()));
            }
        }
    }

    /// `check_partial_gadt ?partial_match_warning_hint pred loc casel`
    /// (parmatch.ml:2243-2257).
    pub fn check_partial(
        &mut self,
        hint: Option<&str>,
        loc: LocIdx,
        casel: &[CaseRef<'a>],
    ) -> Partiality {
        let pss = self.initial_matrix(casel);
        let pss = self.get_mins(pss);
        let total = self.do_check_partial(hint, loc, casel, &pss);
        if total == Partiality::Total
            && self
                .oracle
                .is_active(&ParmatchWarning::FragileMatch(String::new()))
        {
            self.do_check_fragile(loc, casel, &pss);
        }
        total
    }

    /// `is_dict_pattern` (parmatch.ml): a lowered dict pattern, a record
    /// pattern of the `dict` type.
    fn node_has_dict_pattern(&mut self, p: P) -> bool {
        let node = self.node(p);
        let (is_record, ty, env) = (matches!(node.desc, Desc::Record { .. }), node.ty, node.env);
        is_record && ty.is_some_and(|ty| self.oracle.is_dict_type(env, ty))
    }

    /// `contains_dict_pattern` (parmatch.ml:1960-1968) on a node.
    fn contains_dict_pattern(&mut self, p: P) -> bool {
        if self.node_has_dict_pattern(p) {
            return true;
        }
        self.children(p)
            .into_iter()
            .any(|c| self.contains_dict_pattern(c))
    }

    fn children(&self, p: P) -> Vec<P> {
        match self.desc(p) {
            Desc::Any | Desc::Var(_) | Desc::Constant(_) | Desc::Interval(..) => Vec::new(),
            Desc::Alias(p) => vec![*p],
            Desc::Tuple(ps) | Desc::Array(ps) => ps.clone(),
            Desc::Construct { args, .. } => args.clone(),
            Desc::Variant { arg, .. } => arg.iter().copied().collect(),
            Desc::Record { fields, .. } => fields.iter().map(|f| f.pat).collect(),
            Desc::Or(p1, p2) => vec![*p1, *p2],
        }
    }

    /// `opaque_dict_patterns` (parmatch.ml:1970-1978).
    fn opaque_dict_patterns(&mut self, p: P) -> P {
        if self.node_has_dict_pattern(p) {
            let node = self.node(p).clone();
            return self.push(Desc::Any, node.ty, node.env, node.loc, None);
        }
        let desc = match self.desc(p).clone() {
            Desc::Alias(inner) => Desc::Alias(self.opaque_dict_patterns(inner)),
            Desc::Tuple(ps) => Desc::Tuple(
                ps.into_iter()
                    .map(|p| self.opaque_dict_patterns(p))
                    .collect(),
            ),
            Desc::Array(ps) => Desc::Array(
                ps.into_iter()
                    .map(|p| self.opaque_dict_patterns(p))
                    .collect(),
            ),
            Desc::Construct { lid, cstr, args } => Desc::Construct {
                lid,
                cstr,
                args: args
                    .into_iter()
                    .map(|p| self.opaque_dict_patterns(p))
                    .collect(),
            },
            Desc::Variant { label, arg } => Desc::Variant {
                label,
                arg: arg.map(|p| self.opaque_dict_patterns(p)),
            },
            Desc::Record {
                fields,
                closed,
                has_rest,
            } => Desc::Record {
                fields: fields
                    .into_iter()
                    .map(|f| {
                        let pat = self.opaque_dict_patterns(f.pat);
                        Field { pat, ..f }
                    })
                    .collect(),
                closed,
                has_rest,
            },
            Desc::Or(p1, p2) => {
                let (p1, p2) = (self.opaque_dict_patterns(p1), self.opaque_dict_patterns(p2));
                Desc::Or(p1, p2)
            }
            desc => desc,
        };
        self.with_desc(p, desc)
    }

    /// `check_unused pred casel` (parmatch.ml:2159-2232).
    pub fn check_unused(&mut self, casel: &[CaseRef<'a>]) {
        let unused_match = self
            .oracle
            .is_active(&ParmatchWarning::UnusedMatch(String::new()));
        // Shadowed payloads are reported as warning 11 or 12, so they are
        // checked when either is active; the usefulness analysis below only
        // when 11 is.
        if !unused_match
            && !self
                .oracle
                .is_active(&ParmatchWarning::UnusedPat(String::new()))
        {
            return;
        }
        let (dead_cases, already_reported) = self.check_shadowed_payloads(casel);
        if !unused_match {
            return;
        }
        // `pref` is built with `::`, newest case first.
        let mut pref: Vec<Row> = Vec::new();
        for (index, case) in casel.iter().enumerate() {
            // A case that matches nothing cannot make later cases unused.
            if dead_cases.contains(&index) {
                continue;
            }
            let q = self.import(case.lhs);
            let qs = vec![q];
            let compatible: Vec<Row> = pref
                .iter()
                .filter(|ps| self.compats(ps, &qs))
                .cloned()
                .collect();
            let pss = self.get_mins(compatible);
            let rows: Vec<URow> = pss.iter().cloned().map(make_row).collect();
            let mut r = self.every_satisfiables(&rows, &make_row(qs.clone()));
            let skip = matches!(r, Answer::Unused)
                || pref.is_empty()
                || !self.oracle.is_active(&ParmatchWarning::UnreachableCase);
            if !skip {
                let (pss, qs) = if self.contains_dict_pattern(q)
                    || pss
                        .iter()
                        .any(|ps| ps.iter().any(|p| self.contains_dict_pattern(*p)))
                {
                    let pss: Vec<Row> = pss
                        .into_iter()
                        .filter(|ps| !ps.iter().any(|p| self.contains_dict_pattern(*p)))
                        .collect();
                    let qs: Vec<P> = qs.iter().map(|p| self.opaque_dict_patterns(*p)).collect();
                    (pss, qs)
                } else {
                    (pss, qs)
                };
                let sfs = self.satisfiables(&pss, &qs);
                if sfs.is_empty() {
                    r = Answer::Unused;
                } else {
                    let sfs: Vec<P> = sfs
                        .into_iter()
                        .map(|row| match row.as_slice() {
                            [u] => *u,
                            _ => panic!("Parmatch.check_unused"),
                        })
                        .collect();
                    let u = self.orify_many(&sfs);
                    // Retyped even when it cannot fail: typing it expands
                    // the scrutinee's type, which forces signatures in Env
                    // order (parmatch.ml:2206-2210).
                    let exported = self.export(u);
                    if self
                        .oracle
                        .pred(PredKind::Unused, exported, Some(case.lhs.pat_loc))
                        .is_none()
                    {
                        self.oracle
                            .warn(case.lhs.pat_loc, ParmatchWarning::UnreachableCase);
                        r = Answer::Used;
                    }
                }
            }
            match r {
                Answer::Unused => self.oracle.warn(
                    case.lhs.pat_loc,
                    ParmatchWarning::UnusedMatch(String::new()),
                ),
                Answer::Upartial(ps) => {
                    for p in ps {
                        let node = self.node(p);
                        let from_spread = node
                            .src
                            .is_some_and(|src| self.oracle.is_pat_from_variant_spread(self.ta.pat_attributes(src)));
                        let loc = node.loc;
                        if !from_spread && !already_reported.contains(&loc) {
                            self.oracle
                                .warn(loc, ParmatchWarning::UnusedPat(String::new()));
                        }
                    }
                }
                Answer::Used => {}
            }
            if !case.guarded {
                pref.insert(0, vec![q]);
            }
        }
    }
}

/// `contains_extension pat` (parmatch.ml:1950-1958).
pub(crate) fn contains_extension(ta: &TypedArena, pat: &Pattern) -> bool {
    let sub = |p: &TPatIdx| contains_extension(ta, ta.pattern(*p));
    match &pat.pat_desc {
        PatternDesc::Tpat_var(_, name) if name.txt == "*extension*" => true,
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..) => false,
        PatternDesc::Tpat_alias(p, _, _) => sub(p),
        PatternDesc::Tpat_tuple(ps)
        | PatternDesc::Tpat_array(ps)
        | PatternDesc::Tpat_construct(_, _, ps) => ta.pattern_list(*ps).iter().any(sub),
        PatternDesc::Tpat_variant(_, arg, _) => arg.as_ref().is_some_and(sub),
        PatternDesc::Tpat_record(fields, _, _) => fields.iter().any(|(_, _, p, _)| sub(p)),
        PatternDesc::Tpat_dict(entries) => entries.iter().any(|entry| sub(&entry.tdp_pattern)),
        PatternDesc::Tpat_or(p1, p2, _) => sub(p1) || sub(p2),
    }
}

// ---------------------------------------------------------------------------
// Ambiguous variables in or-patterns under guards (parmatch.ml:2317-2581)
// ---------------------------------------------------------------------------

type IdSet = std::collections::BTreeSet<Ident>;

/// `amb_row` (parmatch.ml:2370). `seen` is kept with the most recent
/// binding set last (OCaml conses it on the front).
#[derive(Clone)]
struct AmbRow {
    unseen: Vec<P>,
    seen: Vec<IdSet>,
}

/// A guarded case for [`Parmatch::check_ambiguous_bindings`]: the pattern and
/// `all_rhs_idents` of its guard.
pub(crate) struct AmbiguousCase<'a> {
    pub lhs: &'a Pattern,
    pub guard_idents: Option<IdSet>,
}

impl<'a, O: Oracle> Parmatch<'a, O> {
    fn bound_ident(&self, p: P) -> Option<Ident> {
        match self.node(p).src.map(|src| &src.pat_desc) {
            Some(PatternDesc::Tpat_var(id, _)) | Some(PatternDesc::Tpat_alias(_, id, _)) => {
                Some(*id)
            }
            _ => None,
        }
    }

    /// `do_push r p ps seen k` (parmatch.ml:2374-2381).
    fn amb_do_push(
        &self,
        mut r: IdSet,
        p: P,
        ps: &[P],
        seen: &[IdSet],
        out: &mut Vec<(P, AmbRow)>,
    ) {
        match self.desc(p) {
            Desc::Alias(inner) => {
                if let Some(x) = self.bound_ident(p) {
                    r.insert(x);
                }
                self.amb_do_push(r, *inner, ps, seen, out);
            }
            Desc::Var(_) => {
                if let Some(x) = self.bound_ident(p) {
                    r.insert(x);
                }
                let mut seen = seen.to_vec();
                seen.push(r);
                out.push((
                    self.omega,
                    AmbRow {
                        unseen: ps.to_vec(),
                        seen,
                    },
                ));
            }
            Desc::Or(p1, p2) => {
                let (p1, p2) = (*p1, *p2);
                self.amb_do_push(r.clone(), p1, ps, seen, out);
                self.amb_do_push(r, p2, ps, seen, out);
            }
            _ => {
                let mut seen = seen.to_vec();
                seen.push(r);
                out.push((
                    p,
                    AmbRow {
                        unseen: ps.to_vec(),
                        seen,
                    },
                ));
            }
        }
    }

    /// `push_vars` (parmatch.ml:2383-2387).
    fn amb_push_vars(&self, rows: &[AmbRow]) -> Vec<(P, AmbRow)> {
        let mut out = Vec::new();
        for row in rows {
            let (&p, ps) = row
                .unseen
                .split_first()
                .expect("Parmatch.push_vars: empty row");
            self.amb_do_push(IdSet::new(), p, ps, &row.seen, &mut out);
        }
        out
    }

    /// `collect_stable` (parmatch.ml:2389-2400).
    fn amb_collect_stable(rows: &[AmbRow]) -> IdSet {
        let Some((first, rest)) = rows.split_first() else {
            crate::misc::fatal_error("Parmatch.collect_stable")
        };
        let mut xss = first.seen.clone();
        for row in rest {
            for (x, y) in xss.iter_mut().zip(&row.seen) {
                *x = x.intersection(y).cloned().collect();
            }
        }
        xss.into_iter().fold(IdSet::new(), |mut acc, xs| {
            acc.extend(xs);
            acc
        })
    }

    /// `discr_head` in `filter_all` (parmatch.ml:2428-2437).
    fn amb_discr_head(&mut self, p: P) -> P {
        if let Desc::Record {
            fields,
            closed,
            has_rest,
        } = self.desc(p).clone()
        {
            let fields = self.all_record_args(&fields);
            let q = self.with_desc(
                p,
                Desc::Record {
                    fields,
                    closed,
                    has_rest,
                },
            );
            self.normalize_pat(q)
        } else {
            self.normalize_pat(p)
        }
    }

    /// `filter_all` on ambiguity rows (parmatch.ml:2426-2481).
    fn amb_filter_all(&mut self, rs: &[(P, AmbRow)]) -> Vec<(P, Vec<AmbRow>)> {
        let mut env: Vec<(P, Vec<AmbRow>)> = Vec::new();
        for (p, r) in rs {
            match self.desc(*p) {
                Desc::Var(_) | Desc::Alias(_) | Desc::Or(..) => {
                    crate::misc::fatal_error("Parmatch.filter_all")
                }
                Desc::Any => {}
                _ => {
                    let p = *p;
                    let mut found = None;
                    for (i, (q0, _)) in env.iter().enumerate() {
                        if self.simple_match(*q0, p) {
                            found = Some(i);
                            break;
                        }
                    }
                    match found {
                        Some(i) => {
                            let q0 = env[i].0;
                            let mut unseen = self.simple_match_args(q0, p);
                            unseen.extend_from_slice(&r.unseen);
                            env[i].1.insert(
                                0,
                                AmbRow {
                                    unseen,
                                    seen: r.seen.clone(),
                                },
                            );
                        }
                        None => {
                            let p0 = self.amb_discr_head(p);
                            let mut unseen = self.simple_match_args(p0, p);
                            unseen.extend_from_slice(&r.unseen);
                            env.push((
                                p0,
                                vec![AmbRow {
                                    unseen,
                                    seen: r.seen.clone(),
                                }],
                            ));
                        }
                    }
                }
            }
        }
        for (p, r) in rs {
            if matches!(self.desc(*p), Desc::Any) {
                let omega = self.omega;
                for (q0, rows) in env.iter_mut() {
                    let mut unseen = self.simple_match_args(*q0, omega);
                    unseen.extend_from_slice(&r.unseen);
                    rows.insert(
                        0,
                        AmbRow {
                            unseen,
                            seen: r.seen.clone(),
                        },
                    );
                }
            }
        }
        env
    }

    /// `do_stable rs` (parmatch.ml:2485-2508).
    fn amb_do_stable(&mut self, rs: &[AmbRow]) -> IdSet {
        let Some(first) = rs.first() else {
            crate::misc::fatal_error("Parmatch.do_stable")
        };
        if first.unseen.is_empty() {
            return Self::amb_collect_stable(rs);
        }
        let rs = self.amb_push_vars(rs);
        let column: Vec<P> = rs.iter().map(|(p, _)| *p).collect();
        if !self.all_coherent(&column) {
            let mut acc = IdSet::new();
            for (_, row) in &rs {
                for seen in &row.seen {
                    acc.extend(seen.iter().cloned());
                }
            }
            return acc;
        }
        let groups = self.amb_filter_all(&rs);
        match groups.split_first() {
            None => {
                let rows: Vec<AmbRow> = rs.into_iter().map(|(_, row)| row).collect();
                self.amb_do_stable(&rows)
            }
            Some(((_, first_rows), rest)) => {
                let mut acc = self.amb_do_stable(first_rows);
                for (_, rows) in rest {
                    let st = self.amb_do_stable(rows);
                    acc = acc.intersection(&st).cloned().collect();
                }
                acc
            }
        }
    }

    /// `check_ambiguous_bindings` (parmatch.ml:2563-2581).
    pub fn check_ambiguous_bindings(&mut self, cases: &[AmbiguousCase<'a>]) {
        if !self
            .oracle
            .is_active(&ParmatchWarning::AmbiguousPattern(Vec::new()))
        {
            return;
        }
        for case in cases {
            let Some(guard_idents) = &case.guard_idents else {
                continue;
            };
            let mut vars = IdSet::new();
            pat_bound_idents(self.ta, case.lhs, &mut vars);
            let all: IdSet = vars.intersection(guard_idents).cloned().collect();
            if all.is_empty() {
                continue;
            }
            let p = self.import(case.lhs);
            let st = self.amb_do_stable(&[AmbRow {
                unseen: vec![p],
                seen: Vec::new(),
            }]);
            let ambiguous: Vec<String> = all
                .difference(&st)
                .map(|id| id.name().to_string())
                .collect();
            if !ambiguous.is_empty() {
                self.oracle.warn(
                    case.lhs.pat_loc,
                    ParmatchWarning::AmbiguousPattern(ambiguous),
                );
            }
        }
    }
}

/// `Typedtree.pat_bound_idents` (typedtree.ml:455-477) as a set.
fn pat_bound_idents(ta: &TypedArena, pat: &Pattern, out: &mut IdSet) {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            out.insert(*id);
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            pat_bound_idents(ta, ta.pattern(*p), out);
            out.insert(*id);
        }
        PatternDesc::Tpat_or(p1, _, _) => pat_bound_idents(ta, ta.pattern(*p1), out),
        PatternDesc::Tpat_record(fields, _, rest) => {
            if let Some(rest) = rest {
                out.insert(rest.rest_ident);
            }
            for (_, _, p, _) in fields {
                pat_bound_idents(ta, ta.pattern(*p), out);
            }
        }
        PatternDesc::Tpat_dict(entries) => {
            for entry in entries {
                pat_bound_idents(ta, ta.pattern(entry.tdp_pattern), out);
            }
        }
        PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..) => {}
        PatternDesc::Tpat_tuple(ps) | PatternDesc::Tpat_array(ps) => {
            for p in ta.pattern_list(*ps) {
                pat_bound_idents(ta, ta.pattern(*p), out);
            }
        }
        PatternDesc::Tpat_construct(_, _, ps) => {
            for p in ta.pattern_list(*ps) {
                pat_bound_idents(ta, ta.pattern(*p), out);
            }
        }
        PatternDesc::Tpat_variant(_, arg, _) => {
            if let Some(p) = arg {
                pat_bound_idents(ta, ta.pattern(*p), out);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Payloads shadowed by untagged literals (parmatch.ml)
// ---------------------------------------------------------------------------
//
// An untagged variant tests its literal cases before its payload cases, so in
// `@as("a") A | S(string)` the value "a" is always matched as `A`. A payload
// pattern can therefore never match a value that is also the runtime value of
// a literal case, wherever it appears in the match: `S("a")` is dead.

use crate::types::variant_runtime::{
    Block as RuntimeBlock, BlockType as RuntimeBlockType, ConstructorCase as RuntimeCase,
    LiteralTag,
};

/// parmatch.ml `shadowed_payload`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ShadowedPayload {
    payload_constructor: String,
    value: LiteralTag,
    literal_constructor: String,
}

/// OCaml's polymorphic `compare` on `Variant_runtime.literal_tag`: the
/// constant constructors are immediates, ordered before the blocks, which are
/// ordered by tag and then by their field.
fn compare_literal_tag(a: &LiteralTag, b: &LiteralTag) -> std::cmp::Ordering {
    fn rank(tag: &LiteralTag) -> (u8, u8) {
        match tag {
            LiteralTag::Null => (0, 0),
            LiteralTag::Undefined => (0, 1),
            LiteralTag::String(_) => (1, 0),
            LiteralTag::Int(_) => (1, 1),
            LiteralTag::Float(_) => (1, 2),
            LiteralTag::BigInt(_) => (1, 3),
            LiteralTag::Bool(_) => (1, 4),
        }
    }
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (LiteralTag::String(x), LiteralTag::String(y))
        | (LiteralTag::Float(x), LiteralTag::Float(y))
        | (LiteralTag::BigInt(x), LiteralTag::BigInt(y)) => x.as_bytes().cmp(y.as_bytes()),
        (LiteralTag::Int(x), LiteralTag::Int(y)) => x.cmp(y),
        (LiteralTag::Bool(x), LiteralTag::Bool(y)) => x.cmp(y),
        _ => std::cmp::Ordering::Equal,
    })
}

fn compare_shadowed(a: &ShadowedPayload, b: &ShadowedPayload) -> std::cmp::Ordering {
    a.payload_constructor
        .as_bytes()
        .cmp(b.payload_constructor.as_bytes())
        .then_with(|| compare_literal_tag(&a.value, &b.value))
        .then_with(|| {
            a.literal_constructor
                .as_bytes()
                .cmp(b.literal_constructor.as_bytes())
        })
}

/// parmatch.ml `payload_liveness`.
pub(crate) enum PayloadLiveness<'p> {
    NeverMatches(Vec<ShadowedPayload>),
    /// The pattern can match, except for these dead or-pattern alternatives.
    Matches(Vec<(&'p Pattern, Vec<ShadowedPayload>)>),
}

fn is_type_path(ctx: &TypeContext, path: &Path, ty: TypeExprRef) -> bool {
    matches!(&*ctx.get_desc(ctx.repr(ty)), TypeDesc::Tconstr { path: p, .. } if p.same(path))
}

/// parmatch.ml `pattern_literal`: the runtime value of the only value `p`
/// matches, when it is a literal.
fn pattern_literal(ctx: &TypeContext, ta: &TypedArena, p: &Pattern) -> Option<LiteralTag> {
    match &p.pat_desc {
        PatternDesc::Tpat_constant(Constant::String(s)) => Some(LiteralTag::String(s.clone())),
        PatternDesc::Tpat_constant(Constant::Int(i)) => Some(LiteralTag::Int(*i)),
        PatternDesc::Tpat_constant(Constant::Char(i)) => Some(LiteralTag::Int(i64::from(*i))),
        PatternDesc::Tpat_constant(Constant::Float(f)) => Some(LiteralTag::Float(f.clone())),
        PatternDesc::Tpat_constant(Constant::BigInt(sign, digits)) => {
            // `Bigint_utils.to_string sign digits`.
            Some(LiteralTag::BigInt(if *sign {
                digits.clone()
            } else {
                format!("-{digits}")
            }))
        }
        PatternDesc::Tpat_alias(p, _, _) => pattern_literal(ctx, ta, ta.pattern(*p)),
        PatternDesc::Tpat_variant(label, None, _) => {
            // A polymorphic variant is its name, or the number its name
            // spells, as in `Lambda.const_polyvar`.
            if is_valid_hash_number(label) {
                // `Ext_string.hash_number_as_i32_exn` is `Int32.of_string`.
                label
                    .parse::<i32>()
                    .ok()
                    .map(|i| LiteralTag::Int(i64::from(i)))
            } else {
                Some(LiteralTag::String(label.clone()))
            }
        }
        PatternDesc::Tpat_construct(_, cstr, args)
            if args.is_empty()
                && is_type_path(ctx, &crate::types::predef::path_bool(), cstr.cstr_res) =>
        {
            Some(LiteralTag::Bool(cstr.cstr_name == "true"))
        }
        PatternDesc::Tpat_construct(_, cstr, _)
            if [
                crate::types::predef::path_unit(),
                crate::types::predef::path_list(),
                crate::types::predef::path_option(),
            ]
            .iter()
            .any(|path| is_type_path(ctx, path, cstr.cstr_res)) =>
        {
            None
        }
        PatternDesc::Tpat_construct(_, cstr, args) => match &cstr.cstr_kind {
            ConstructorKind::Ordinary(r) => match (r.representation(ctx), ta.pattern_list(*args)) {
                (RuntimeCase::Constant(tag), []) => Some(tag.literal),
                // An untagged payload is represented by the payload itself.
                (RuntimeCase::Block(RuntimeBlock::Untagged { .. }), [arg]) => {
                    pattern_literal(ctx, ta, ta.pattern(*arg))
                }
                _ => None,
            },
            ConstructorKind::Extension(_) => None,
        },
        _ => None,
    }
}

/// `Ext_string.is_valid_hash_number`.
fn is_valid_hash_number(value: &str) -> bool {
    match value.as_bytes() {
        [] => false,
        [b'0'..=b'9'] => true,
        [b'1'..=b'9', rest @ ..] => rest.iter().all(u8::is_ascii_digit),
        _ => false,
    }
}

fn is_untagged_payload(ctx: &TypeContext, cd: &ConstructorDescription) -> bool {
    match &cd.cstr_kind {
        ConstructorKind::Ordinary(r) => matches!(
            r.representation(ctx),
            RuntimeCase::Block(RuntimeBlock::Untagged { .. })
        ),
        ConstructorKind::Extension(_) => false,
    }
}

/// parmatch.ml `shadowing_literal_cases`: the literal cases that take
/// precedence over an untagged payload constructor.
fn shadowing_literal_cases(ctx: &TypeContext, cd: &ConstructorDescription) -> Vec<ShadowedPayload> {
    match &cd.cstr_kind {
        ConstructorKind::Ordinary(r) if is_untagged_payload(ctx, cd) => {
            ctx.with_variant_layout(r.variant, |layout| {
                layout
                    .constructors
                    .iter()
                    .filter_map(|case| match case {
                        RuntimeCase::Constant(tag) => Some(ShadowedPayload {
                            payload_constructor: cd.cstr_name.clone(),
                            value: tag.literal.clone(),
                            literal_constructor: tag.name.clone(),
                        }),
                        RuntimeCase::Block(_) => None,
                    })
                    .collect()
            })
        }
        _ => Vec::new(),
    }
}

fn or_liveness<'p>(
    liveness: impl Fn(&'p Pattern) -> PayloadLiveness<'p>,
    p1: &'p Pattern,
    p2: &'p Pattern,
) -> PayloadLiveness<'p> {
    use PayloadLiveness::{Matches, NeverMatches};
    match (liveness(p1), liveness(p2)) {
        (NeverMatches(mut s1), NeverMatches(s2)) => {
            s1.extend(s2);
            NeverMatches(s1)
        }
        (Matches(mut d1), NeverMatches(s2)) => {
            d1.push((p2, s2));
            Matches(d1)
        }
        (NeverMatches(s1), Matches(d2)) => {
            let mut d = vec![(p1, s1)];
            d.extend(d2);
            Matches(d)
        }
        (Matches(mut d1), Matches(d2)) => {
            d1.extend(d2);
            Matches(d1)
        }
    }
}

/// parmatch.ml `payload_liveness`.
pub(crate) fn payload_liveness<'p>(ctx: &TypeContext, ta: &'p TypedArena, p: &'p Pattern) -> PayloadLiveness<'p> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => or_liveness(|p| payload_liveness(ctx, ta, p), ta.pattern(*p1), ta.pattern(*p2)),
        PatternDesc::Tpat_construct(_, cd, args) if args.len() == 1 => {
            let shadowing = shadowing_literal_cases(ctx, cd);
            if shadowing.is_empty() {
                subpatterns_liveness(ctx, ta, p)
            } else {
                shadowed_argument_liveness(ctx, ta, &shadowing, ta.pattern(ta.pattern_list(*args)[0]))
            }
        }
        _ => subpatterns_liveness(ctx, ta, p),
    }
}

/// `Typedtree.iter_pattern_desc`'s children, in its order.
fn pattern_children<'p>(ta: &'p TypedArena, p: &'p Pattern) -> Vec<&'p Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_alias(p, _, _) => vec![ta.pattern(*p)],
        PatternDesc::Tpat_tuple(ps) | PatternDesc::Tpat_array(ps) => ta.patterns(*ps).collect(),
        PatternDesc::Tpat_construct(_, _, ps) => ta.patterns(*ps).collect(),
        PatternDesc::Tpat_variant(_, arg, _) => arg.iter().map(|p| ta.pattern(*p)).collect(),
        PatternDesc::Tpat_record(fields, _, _) => fields.iter().map(|(_, _, p, _)| ta.pattern(*p)).collect(),
        PatternDesc::Tpat_dict(entries) => entries.iter().map(|e| ta.pattern(e.tdp_pattern)).collect(),
        PatternDesc::Tpat_or(p1, p2, _) => vec![ta.pattern(*p1), ta.pattern(*p2)],
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..) => vec![],
    }
}

/// A pattern that is not an or-pattern matches nothing as soon as one of its
/// subpatterns matches nothing.
fn subpatterns_liveness<'p>(ctx: &TypeContext, ta: &'p TypedArena, p: &'p Pattern) -> PayloadLiveness<'p> {
    let mut result = PayloadLiveness::Matches(Vec::new());
    for sub in pattern_children(ta, p) {
        if let PayloadLiveness::NeverMatches(_) = result {
            continue;
        }
        match payload_liveness(ctx, ta, sub) {
            dead @ PayloadLiveness::NeverMatches(_) => result = dead,
            PayloadLiveness::Matches(d2) => {
                if let PayloadLiveness::Matches(d1) = &mut result {
                    d1.extend(d2);
                }
            }
        }
    }
    result
}

/// `shadowing` lists the literal cases that take precedence over the value
/// `arg` matches, outermost first.
fn shadowed_argument_liveness<'p>(
    ctx: &TypeContext,
    ta: &'p TypedArena,
    shadowing: &[ShadowedPayload],
    arg: &'p Pattern,
) -> PayloadLiveness<'p> {
    match &arg.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            or_liveness(|p| shadowed_argument_liveness(ctx, ta, shadowing, p), ta.pattern(*p1), ta.pattern(*p2))
        }
        PatternDesc::Tpat_alias(p, _, _) => shadowed_argument_liveness(ctx, ta, shadowing, ta.pattern(*p)),
        PatternDesc::Tpat_construct(_, cd, inner)
            if inner.len() == 1 && is_untagged_payload(ctx, cd) =>
        {
            // An untagged payload is the value itself, so the literal cases
            // around it still take precedence, before its own.
            let mut shadowing = shadowing.to_vec();
            shadowing.extend(shadowing_literal_cases(ctx, cd));
            shadowed_argument_liveness(ctx, ta, &shadowing, ta.pattern(ta.pattern_list(*inner)[0]))
        }
        _ => {
            let shadowing_case = pattern_literal(ctx, ta, arg).and_then(|value| {
                shadowing.iter().find(|shadowed| {
                    crate::types::variant_runtime::same_literal_value(&value, &shadowed.value)
                })
            });
            match shadowing_case {
                Some(shadowed) => PayloadLiveness::NeverMatches(vec![shadowed.clone()]),
                None => payload_liveness(ctx, ta, arg),
            }
        }
    }
}

/// parmatch.ml `literal_to_string`.
fn literal_to_string(value: &LiteralTag) -> String {
    match value {
        LiteralTag::String(s) => format!("\"{s}\""),
        LiteralTag::Int(i) => i.to_string(),
        LiteralTag::Float(f) => f.clone(),
        LiteralTag::BigInt(b) => format!("{b}n"),
        LiteralTag::Bool(b) => b.to_string(),
        LiteralTag::Null => "null".to_string(),
        LiteralTag::Undefined => "undefined".to_string(),
    }
}

/// parmatch.ml `shadowed_payload_reason`.
fn shadowed_payload_reason(shadowed: &[ShadowedPayload]) -> String {
    let mut shadowed = shadowed.to_vec();
    shadowed.sort_by(compare_shadowed);
    shadowed.dedup_by(|a, b| compare_shadowed(a, b) == std::cmp::Ordering::Equal);
    shadowed
        .iter()
        .map(|s| {
            format!(
                "{} is the runtime value of constructor {}, so it is always matched as {}, never as {}.",
                literal_to_string(&s.value),
                s.literal_constructor,
                s.literal_constructor,
                s.payload_constructor
            )
        })
        .collect::<Vec<_>>()
        // OCaml joins with "\n  "; the Rust warning printer indents every
        // line of a message itself (see `Warning::PartialMatch`).
        .join("\n")
}

/// Whether `payload_liveness` reports anything for the pattern, so the
/// unused-case check cannot be skipped as trivial.
pub(crate) fn has_shadowed_payloads(ctx: &TypeContext, ta: &TypedArena, p: &Pattern) -> bool {
    !matches!(payload_liveness(ctx, ta, p), PayloadLiveness::Matches(d) if d.is_empty())
}

impl<'a, O: Oracle> Parmatch<'a, O> {
    /// parmatch.ml `check_shadowed_payloads`: report cases and or-pattern
    /// alternatives that can never match because of `payload_liveness`.
    /// Returns the indices of the cases that match nothing, and the
    /// locations of the reported sub-patterns.
    fn check_shadowed_payloads(&mut self, casel: &[CaseRef<'a>]) -> (Vec<usize>, Vec<LocIdx>) {
        let mut reported = Vec::new();
        let mut dead_cases = Vec::new();
        for (index, case) in casel.iter().enumerate() {
            let liveness = payload_liveness(self.oracle.ctx(), self.ta, case.lhs);
            match liveness {
                PayloadLiveness::NeverMatches(shadowed) => {
                    let reason = shadowed_payload_reason(&shadowed);
                    self.oracle
                        .warn(case.lhs.pat_loc, ParmatchWarning::UnusedMatch(reason));
                    dead_cases.push(index);
                }
                PayloadLiveness::Matches(dead_alternatives) => {
                    for (p, shadowed) in dead_alternatives {
                        reported.push(p.pat_loc);
                        let reason = shadowed_payload_reason(&shadowed);
                        self.oracle
                            .warn(p.pat_loc, ParmatchWarning::UnusedPat(reason));
                    }
                }
            }
        }
        (dead_cases, reported)
    }

    /// parmatch.ml `with_bool_payload_overlaps`, applied while importing a
    /// case for the exhaustiveness check: a literal case of an untagged
    /// variant also covers the payload values equal to its runtime value.
    /// This matters for a bool payload, whose values can all be covered, as
    /// in `@as(true) Yes | Ans(bool)` where `Yes | Ans(false)` is exhaustive.
    fn import_with_bool_payload_overlaps(&mut self, pat: &'a Pattern) -> P {
        let ta = self.ta;
        if let PatternDesc::Tpat_construct(_, cstr, args) = &pat.pat_desc
            && args.is_empty()
            && let ConstructorKind::Ordinary(r) = &cstr.cstr_kind
        {
            let representation = r.representation(self.oracle.ctx());
            let p = self.import(pat);
            if let RuntimeCase::Constant(tag) = representation
                && let LiteralTag::Bool(b) = tag.literal
            {
                let (env, ty) = (pat.pat_env, pat.pat_type);
                let constructors = self.oracle.variant_constructors(env, ty);
                // The payload type must be `bool` itself: a
                // `@typeOf("boolean")` type has boolean values, but no `true`
                // and `false` patterns.
                let payload_cd = constructors.into_iter().find(|cd| {
                    let (ConstructorKind::Ordinary(r), [arg]) =
                        (&cd.cstr_kind, cd.cstr_args.as_slice())
                    else {
                        return false;
                    };
                    let is_boolean_payload = matches!(
                        r.representation(self.oracle.ctx()),
                        RuntimeCase::Block(RuntimeBlock::Untagged {
                            block_type: RuntimeBlockType::Boolean,
                            ..
                        })
                    );
                    is_boolean_payload && {
                        let expanded = self.oracle.expand_head(env, *arg);
                        is_type_path(
                            self.oracle.ctx(),
                            &crate::types::predef::path_bool(),
                            expanded,
                        )
                    }
                });
                if let Some(payload_cd) = payload_cd {
                    let bool_ty = self.oracle.ctx().predef_bool();
                    let name = if b { "true" } else { "false" };
                    let bool_cd = self
                        .oracle
                        .variant_constructors(env, bool_ty)
                        .into_iter()
                        .find(|cd| cd.cstr_name == name)
                        .expect("Parmatch.with_bool_payload_overlaps: bool constructor");
                    let bool_pat = self.make_pat(
                        Desc::Construct {
                            lid: None,
                            cstr: std::sync::Arc::new(bool_cd),
                            args: vec![],
                        },
                        Some(bool_ty),
                        env,
                    );
                    let payload_pat = self.make_pat(
                        Desc::Construct {
                            lid: None,
                            cstr: std::sync::Arc::new(payload_cd),
                            args: vec![bool_pat],
                        },
                        Some(ty),
                        env,
                    );
                    return self.orify(p, payload_pat);
                }
            }
            return p;
        }
        // `{p with pat_desc = Typedtree.map_pattern_desc ...}`.
        let desc = match &pat.pat_desc {
            PatternDesc::Tpat_alias(inner, _, _) => {
                Desc::Alias(self.import_with_bool_payload_overlaps(ta.pattern(*inner)))
            }
            PatternDesc::Tpat_tuple(items) => Desc::Tuple(
                ta.patterns(*items)
                    .map(|item| self.import_with_bool_payload_overlaps(item))
                    .collect(),
            ),
            PatternDesc::Tpat_construct(lid, cstr, args) => Desc::Construct {
                lid: Some(*lid),
                cstr: std::sync::Arc::clone(cstr),
                args: ta.patterns(*args)
                    .map(|arg| self.import_with_bool_payload_overlaps(arg))
                    .collect(),
            },
            PatternDesc::Tpat_variant(label, arg, _) => Desc::Variant {
                label: Cow::Borrowed(label.as_str()),
                arg: arg.as_ref().map(|arg| ta.pattern(*arg))
                    .map(|arg| self.import_with_bool_payload_overlaps(arg)),
            },
            PatternDesc::Tpat_record(fields, closed, rest) => Desc::Record {
                fields: fields
                    .iter()
                    .map(|(lid, lbl, p, opt)| Field {
                        lid: Some(*lid),
                        lbl: Cow::Borrowed(lbl),
                        pat: self.import_with_bool_payload_overlaps(ta.pattern(*p)),
                        opt: *opt,
                    })
                    .collect(),
                closed: *closed,
                has_rest: rest.is_some(),
            },
            PatternDesc::Tpat_array(items) => Desc::Array(
                ta.patterns(*items)
                    .map(|item| self.import_with_bool_payload_overlaps(item))
                    .collect(),
            ),
            PatternDesc::Tpat_or(left, right, _) => Desc::Or(
                self.import_with_bool_payload_overlaps(ta.pattern(*left)),
                self.import_with_bool_payload_overlaps(ta.pattern(*right)),
            ),
            PatternDesc::Tpat_any
            | PatternDesc::Tpat_var(..)
            | PatternDesc::Tpat_constant(_)
            | PatternDesc::Tpat_interval(..)
            | PatternDesc::Tpat_dict(_) => return self.import(pat),
        };
        self.push(
            desc,
            Some(pat.pat_type),
            pat.pat_env,
            pat.pat_loc,
            Some(pat),
        )
    }
}
