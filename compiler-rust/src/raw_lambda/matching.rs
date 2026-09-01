//! Pattern matching compilation — Layer 1: Core types and infrastructure.
//!
//! This is a 1:1 port of OCaml's `matching.ml` lines 1-374.
//! It defines the core data structures (matrix, context, jumps, pattern_matching)
//! and the operations on them used by the pattern matching compiler.

#![allow(dead_code)]

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt::Write as _;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};

use crate::ident::{Ident, IdentFlags};
use crate::lambda::LetKind;
use crate::lambda::lam_constant::PointerInfo;
use crate::lambda::lam_primitive::Mutable;
use crate::lambda::{Comparison, FieldDbgInfo, Primitive, TagInfo};
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::raw_lambda::typeopt::{
    constructor_has_optional_shape, find_type_decl_pub, has_untagged,
    type_cannot_contain_undefined, type_cannot_contain_undefined_no_env, type_is_builtin_object,
};
use crate::raw_lambda::{RawApply, RawLambda, RawLambdaSwitch, RawPrimInfo};
use crate::types::asttypes::MutableFlag;
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, ConstructorDescription, ConstructorKind, LabelDescription,
    RecordRepresentation, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::type_expr::TypeExprRef;
use crate::types::type_expr::{RowDesc, RowField, TypeDesc};
use crate::types::typedtree::Partial;
use crate::types::typedtree::{Constant, EnvRef, Pattern, PatternDesc};

/// Terminal action graph shared by pattern-matrix transformations.
///
/// `Bind` is the delayed representation of OCaml `Lambda.bind` inside a case
/// action. General match-result control flow remains owned by `MatchCode`.
#[derive(Clone)]
struct MatchAction(Arc<MatchActionData>);

struct MatchActionData {
    kind: MatchActionKind,
    normalized_key: OnceLock<Option<String>>,
}

enum MatchActionKind {
    Raw(RawLambda),
    Bind {
        kind: LetKind,
        id: Ident,
        arg: RawLambda,
        action: MatchAction,
    },
}

impl MatchAction {
    fn new(action: RawLambda) -> Self {
        match action {
            RawLambda::Llet(LetKind::Alias, id, arg, body) => {
                Self::from_kind(MatchActionKind::Bind {
                    kind: LetKind::Alias,
                    id,
                    arg: *arg,
                    action: Self::new(*body),
                })
            }
            raw => Self::from_kind(MatchActionKind::Raw(raw)),
        }
    }

    fn from_kind(kind: MatchActionKind) -> Self {
        Self(Arc::new(MatchActionData {
            kind,
            normalized_key: OnceLock::new(),
        }))
    }

    fn clone_to_raw_uninstrumented(&self) -> RawLambda {
        match &self.0.kind {
            MatchActionKind::Raw(raw) => raw.clone(),
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => RawLambda::Llet(
                *kind,
                id.clone(),
                Box::new(arg.clone()),
                Box::new(action.clone_to_raw_uninstrumented()),
            ),
        }
    }

    #[track_caller]
    fn to_raw(&self) -> RawLambda {
        if crate::perf_counters::enabled() {
            let (nodes, estimated_bytes) = match_action_clone_footprint(self);
            let references = Arc::strong_count(&self.0);
            let started = std::time::Instant::now();
            let raw = self.clone_to_raw_uninstrumented();
            crate::perf_counters::record_match_action_clone(
                std::panic::Location::caller(),
                nodes,
                estimated_bytes,
                started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
                references,
            );
            raw
        } else {
            self.clone_to_raw_uninstrumented()
        }
    }

    #[track_caller]
    fn into_raw(self) -> RawLambda {
        match Arc::try_unwrap(self.0) {
            Ok(data) => data.into_raw(),
            Err(shared) => MatchAction(shared).to_raw(),
        }
    }

    fn normalized_key(&self) -> Option<&str> {
        self.0
            .normalized_key
            .get_or_init(|| make_key_string_action(self))
            .as_deref()
    }

    fn is_guarded(&self) -> bool {
        match &self.0.kind {
            MatchActionKind::Raw(raw) => is_guarded(raw),
            MatchActionKind::Bind { action, .. } => action.is_guarded(),
        }
    }

    #[track_caller]
    fn patch_guarded(&self, patch: RawLambda) -> RawLambda {
        if crate::perf_counters::enabled() {
            let nodes = match_action_patch_clone_nodes(self);
            let started = std::time::Instant::now();
            let raw = self.patch_guarded_uninstrumented(patch);
            crate::perf_counters::record_match_action_clone(
                std::panic::Location::caller(),
                nodes,
                nodes * std::mem::size_of::<RawLambda>(),
                started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
                Arc::strong_count(&self.0),
            );
            raw
        } else {
            self.patch_guarded_uninstrumented(patch)
        }
    }

    fn patch_guarded_uninstrumented(&self, patch: RawLambda) -> RawLambda {
        match &self.0.kind {
            MatchActionKind::Raw(raw) => patch_guarded(patch, raw),
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => RawLambda::Llet(
                *kind,
                id.clone(),
                Box::new(arg.clone()),
                Box::new(action.patch_guarded_uninstrumented(patch)),
            ),
        }
    }

    fn bind(self, kind: LetKind, id: Ident, arg: RawLambda) -> Self {
        match &arg {
            RawLambda::Lvar(v) if v.same(&id) => self,
            _ => Self::from_kind(MatchActionKind::Bind {
                kind,
                id,
                arg,
                action: self,
            }),
        }
    }

    fn free_variables(&self) -> IdentSet {
        match &self.0.kind {
            MatchActionKind::Raw(raw) => raw_lambda_free_variables(raw),
            MatchActionKind::Bind {
                id, arg, action, ..
            } => {
                let mut free = raw_lambda_free_variables(arg);
                let mut action_free = action.free_variables();
                action_free.remove(id);
                free.extend(action_free);
                free
            }
        }
    }
}

impl MatchActionData {
    #[track_caller]
    fn into_raw(self) -> RawLambda {
        match self.kind {
            MatchActionKind::Raw(raw) => raw,
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => RawLambda::Llet(kind, id, Box::new(arg), Box::new(action.into_raw())),
        }
    }
}

/// Owned code assembled around shared terminal actions.
enum MatchCode {
    Action(MatchAction),
    If {
        condition: RawLambda,
        ifso: Box<MatchCode>,
        ifnot: Box<MatchCode>,
    },
    StaticCatch {
        body: Box<MatchCode>,
        exit: (i32, Vec<Ident>),
        handler: Box<MatchCode>,
    },
    Bind {
        kind: LetKind,
        id: Ident,
        arg: RawLambda,
        body: Box<MatchCode>,
    },
}

impl MatchCode {
    fn raw(action: RawLambda) -> Self {
        Self::Action(MatchAction::new(action))
    }

    #[track_caller]
    fn into_raw(self) -> RawLambda {
        match self {
            Self::Action(action) => action.into_raw(),
            Self::If {
                condition,
                ifso,
                ifnot,
            } => RawLambda::LifThenElse(
                Box::new(condition),
                Box::new(ifso.into_raw()),
                Box::new(ifnot.into_raw()),
            ),
            Self::StaticCatch {
                body,
                exit,
                handler,
            } => RawLambda::LstaticCatch(
                Box::new(body.into_raw()),
                exit,
                Box::new(handler.into_raw()),
            ),
            Self::Bind {
                kind,
                id,
                arg,
                body,
            } => RawLambda::Llet(kind, id, Box::new(arg), Box::new(body.into_raw())),
        }
    }

    fn bind(self, kind: LetKind, id: Ident, arg: RawLambda) -> Self {
        match &arg {
            RawLambda::Lvar(v) if v.same(&id) => self,
            _ => Self::Bind {
                kind,
                id,
                arg,
                body: Box::new(self),
            },
        }
    }

    fn if_then_else(condition: RawLambda, ifso: Self, ifnot: Self) -> Self {
        Self::If {
            condition,
            ifso: Box::new(ifso),
            ifnot: Box::new(ifnot),
        }
    }

    fn static_catch(body: Self, exit: (i32, Vec<Ident>), handler: Self) -> Self {
        Self::StaticCatch {
            body: Box::new(body),
            exit,
            handler: Box::new(handler),
        }
    }

    fn normalized_key(&self) -> Option<String> {
        match self {
            Self::Action(action) => action.normalized_key().map(str::to_owned),
            _ => make_key_string_code(self),
        }
    }

    fn is_guarded(&self) -> bool {
        match self {
            Self::Action(action) => action.is_guarded(),
            Self::If { ifnot, .. } => ifnot.is_guarded(),
            Self::StaticCatch { .. } => false,
            Self::Bind { body, .. } => body.is_guarded(),
        }
    }

    fn free_variables(&self) -> IdentSet {
        match self {
            Self::Action(action) => action.free_variables(),
            Self::If {
                condition,
                ifso,
                ifnot,
            } => {
                let mut fv = raw_lambda_free_variables(condition);
                fv.extend(ifso.free_variables());
                fv.extend(ifnot.free_variables());
                fv
            }
            Self::StaticCatch {
                body,
                exit: (_, vars),
                handler,
            } => {
                let mut fv = body.free_variables();
                let mut handler_fv = handler.free_variables();
                for var in vars {
                    handler_fv.remove(var);
                }
                fv.extend(handler_fv);
                fv
            }
            Self::Bind { id, arg, body, .. } => {
                let mut fv = raw_lambda_free_variables(arg);
                let mut body_fv = body.free_variables();
                body_fv.remove(id);
                fv.extend(body_fv);
                fv
            }
        }
    }

    #[track_caller]
    fn clone_to_raw(&self) -> RawLambda {
        fn clone_uninstrumented(code: &MatchCode) -> RawLambda {
            match code {
                MatchCode::Action(action) => action.clone_to_raw_uninstrumented(),
                MatchCode::If {
                    condition,
                    ifso,
                    ifnot,
                } => RawLambda::LifThenElse(
                    Box::new(condition.clone()),
                    Box::new(clone_uninstrumented(ifso)),
                    Box::new(clone_uninstrumented(ifnot)),
                ),
                MatchCode::StaticCatch {
                    body,
                    exit,
                    handler,
                } => RawLambda::LstaticCatch(
                    Box::new(clone_uninstrumented(body)),
                    exit.clone(),
                    Box::new(clone_uninstrumented(handler)),
                ),
                MatchCode::Bind {
                    kind,
                    id,
                    arg,
                    body,
                } => RawLambda::Llet(
                    *kind,
                    id.clone(),
                    Box::new(arg.clone()),
                    Box::new(clone_uninstrumented(body)),
                ),
            }
        }

        if crate::perf_counters::enabled() {
            let (nodes, bytes, fanout) = match_code_clone_footprint(self);
            let started = std::time::Instant::now();
            let raw = clone_uninstrumented(self);
            crate::perf_counters::record_match_action_clone(
                std::panic::Location::caller(),
                nodes,
                bytes,
                started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
                fanout,
            );
            raw
        } else {
            clone_uninstrumented(self)
        }
    }

    #[cfg(test)]
    fn clone_to_raw_for_test(&self) -> RawLambda {
        self.clone_to_raw()
    }

    fn normalized_static_raise(&self) -> Option<(i32, Vec<RawLambda>)> {
        match make_key(&self.clone_to_raw()) {
            Some(RawLambda::LstaticRaise(exit, args)) => Some((exit, args)),
            _ => None,
        }
    }
}

/// Count the RawLambda nodes copied when a shared terminal action is materialized.
fn raw_lambda_clone_footprint(raw: &RawLambda) -> (usize, usize) {
    fn nodes(raw: &RawLambda) -> usize {
        let children = match raw {
            RawLambda::Lvar(_)
            | RawLambda::LglobalModule(_, _)
            | RawLambda::Lconst(_)
            | RawLambda::Lbreak
            | RawLambda::Lcontinue => 0,
            RawLambda::Lapply(apply) => {
                nodes(&apply.ap_func) + apply.ap_args.iter().map(nodes).sum::<usize>()
            }
            RawLambda::Lfunction(function) => nodes(&function.body),
            RawLambda::Llet(_, _, value, body)
            | RawLambda::Lsequence(value, body)
            | RawLambda::Lwhile(value, body)
            | RawLambda::Lfor_of(_, value, body)
            | RawLambda::Lfor_await_of(_, value, body) => nodes(value) + nodes(body),
            RawLambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .map(|(_, value)| nodes(value))
                    .sum::<usize>()
                    + nodes(body)
            }
            RawLambda::Lprim(info) => info.args.iter().map(nodes).sum(),
            RawLambda::Lswitch(scrutinee, switch, _) => {
                nodes(scrutinee)
                    + switch
                        .sw_consts
                        .iter()
                        .map(|(_, action)| nodes(action))
                        .sum::<usize>()
                    + switch
                        .sw_blocks
                        .iter()
                        .map(|(_, action)| nodes(action))
                        .sum::<usize>()
                    + switch.sw_failaction.as_deref().map(nodes).unwrap_or(0)
            }
            RawLambda::LstringSwitch(scrutinee, cases, default) => {
                nodes(scrutinee)
                    + cases.iter().map(|(_, action)| nodes(action)).sum::<usize>()
                    + default.as_deref().map(nodes).unwrap_or(0)
            }
            RawLambda::LstaticRaise(_, args) => args.iter().map(nodes).sum(),
            RawLambda::LstaticCatch(body, _, handler) | RawLambda::LtryWith(body, _, handler) => {
                nodes(body) + nodes(handler)
            }
            RawLambda::LifThenElse(condition, ifso, ifnot) => {
                nodes(condition) + nodes(ifso) + nodes(ifnot)
            }
            RawLambda::Lfor(_, start, end, _, body) => nodes(start) + nodes(end) + nodes(body),
            RawLambda::Lassign(_, value) | RawLambda::Lsend(_, value, _) => nodes(value),
        };
        1 + children
    }
    let nodes = nodes(raw);
    (nodes, nodes * std::mem::size_of::<RawLambda>())
}

fn match_action_clone_footprint(action: &MatchAction) -> (usize, usize) {
    let nodes = match &action.0.kind {
        MatchActionKind::Raw(raw) => raw_lambda_clone_footprint(raw).0,
        MatchActionKind::Bind { arg, action, .. } => {
            1 + raw_lambda_clone_footprint(arg).0 + match_action_clone_footprint(action).0
        }
    };
    (nodes, nodes * std::mem::size_of::<RawLambda>())
}

fn match_action_patch_clone_nodes(action: &MatchAction) -> usize {
    match &action.0.kind {
        MatchActionKind::Raw(raw) => patch_guarded_clone_nodes(raw),
        MatchActionKind::Bind { arg, action, .. } => {
            1 + raw_lambda_clone_footprint(arg).0 + match_action_patch_clone_nodes(action)
        }
    }
}

fn match_code_clone_footprint(code: &MatchCode) -> (usize, usize, usize) {
    fn visit(code: &MatchCode) -> (usize, usize) {
        match code {
            MatchCode::Action(action) => (
                match_action_clone_footprint(action).0,
                Arc::strong_count(&action.0),
            ),
            MatchCode::If {
                condition,
                ifso,
                ifnot,
            } => {
                let (ifso_nodes, ifso_fanout) = visit(ifso);
                let (ifnot_nodes, ifnot_fanout) = visit(ifnot);
                (
                    1 + raw_lambda_clone_footprint(condition).0 + ifso_nodes + ifnot_nodes,
                    ifso_fanout.max(ifnot_fanout),
                )
            }
            MatchCode::StaticCatch { body, handler, .. } => {
                let (body_nodes, body_fanout) = visit(body);
                let (handler_nodes, handler_fanout) = visit(handler);
                (
                    1 + body_nodes + handler_nodes,
                    body_fanout.max(handler_fanout),
                )
            }
            MatchCode::Bind { arg, body, .. } => {
                let (body_nodes, fanout) = visit(body);
                (1 + raw_lambda_clone_footprint(arg).0 + body_nodes, fanout)
            }
        }
    }
    let (nodes, fanout) = visit(code);
    (nodes, nodes * std::mem::size_of::<RawLambda>(), fanout)
}

fn patch_guarded_clone_nodes(action: &RawLambda) -> usize {
    match action {
        RawLambda::LifThenElse(condition, body, _) => {
            1 + raw_lambda_clone_footprint(condition).0 + raw_lambda_clone_footprint(body).0
        }
        RawLambda::Llet(_, _, value, body) => {
            1 + raw_lambda_clone_footprint(value).0 + patch_guarded_clone_nodes(body)
        }
        _ => panic!("patch_guarded: unexpected lambda"),
    }
}

type Clause = (Vec<Pattern>, MatchAction);

/// Shared match arguments used while compiling pattern matrices.
///
/// OCaml `compiler/ml/matching.ml:814-1090` passes immutable `args` lists
/// through `split_or`, `precompile_var`, and `precompile_or`; constructing a
/// `Pm`/`PmOr` node shares that list. Rust used `Vec<(RawLambda, LetKind)>`
/// directly, so every `args.to_vec()` recursively cloned raw-lambda scrutinees.
/// Store the backing vector once and represent OCaml tail lists with a start
/// offset to preserve the same functional sharing.
#[derive(Clone)]
pub struct MatchArgs {
    values: Arc<Vec<(RawLambda, LetKind)>>,
    start: usize,
}

impl MatchArgs {
    fn new(values: Vec<(RawLambda, LetKind)>) -> Self {
        Self {
            values: Arc::new(values),
            start: 0,
        }
    }

    fn tail(&self, count: usize) -> Self {
        assert!(
            self.start + count <= self.values.len(),
            "MatchArgs::tail past end"
        );
        Self {
            values: Arc::clone(&self.values),
            start: self.start + count,
        }
    }

    fn as_slice(&self) -> &[(RawLambda, LetKind)] {
        &self.values[self.start..]
    }
}

impl Deref for MatchArgs {
    type Target = [(RawLambda, LetKind)];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

// ============================================================================
// Omega (wildcard) helpers — ported from parmatch.ml
// ============================================================================

/// Create a wildcard pattern (`_`).
/// Equivalent to OCaml's `omega = make_pat Tpat_any Ctype.none Env.empty`.
fn omega() -> Pattern {
    Pattern::new(
        PatternDesc::Tpat_any,
        LocIdx::none(),
        TypeExprRef(0),
        EnvRef(0),
        Attributes::new(),
    )
}

/// Create a list of n wildcard patterns.
/// Equivalent to OCaml's `omegas n`.
fn omegas(n: usize) -> Vec<Pattern> {
    (0..n).map(|_| omega()).collect()
}

/// Create a list of wildcards with the same length as `l`.
fn omega_list(l: &[Pattern]) -> Vec<Pattern> {
    l.iter().map(|_| omega()).collect()
}

fn bump_raise_count(next_raise_count: &mut i32, _label: &str) -> i32 {
    *next_raise_count += 1;
    *next_raise_count
}

// ============================================================================
// Pattern helper functions — ported from parmatch.ml
// ============================================================================

/// Make a pattern with given desc, type, and env.
fn make_pat(desc: PatternDesc, ty: TypeExprRef, env: EnvRef) -> Pattern {
    Pattern::new(desc, LocIdx::none(), ty, env, Attributes::new())
}

/// Compare two typed constants.
/// Equivalent to OCaml's `const_compare`.
fn const_compare(c1: &Constant, c2: &Constant) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    fn normalize_bigint_digits(digits: &str) -> &str {
        let trimmed = digits.trim_start_matches('0');
        if trimmed.is_empty() { "0" } else { trimmed }
    }

    fn compare_bigint(positive1: bool, digits1: &str, positive2: bool, digits2: &str) -> Ordering {
        if positive1 != positive2 {
            return if positive1 {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }

        let digits1 = normalize_bigint_digits(digits1);
        let digits2 = normalize_bigint_digits(digits2);
        let abs_cmp = digits1
            .len()
            .cmp(&digits2.len())
            .then_with(|| digits1.cmp(digits2));
        if positive1 {
            abs_cmp
        } else {
            abs_cmp.reverse()
        }
    }

    match (c1, c2) {
        (Constant::Float(f1), Constant::Float(f2)) => {
            let v1: f64 = f1.parse().unwrap_or(0.0);
            let v2: f64 = f2.parse().unwrap_or(0.0);
            v1.partial_cmp(&v2).unwrap_or(Ordering::Equal)
        }
        (Constant::BigInt(s1, b1), Constant::BigInt(s2, b2)) => compare_bigint(*s1, b1, *s2, b2),
        (Constant::String(s1, _), Constant::String(s2, _)) => s1.cmp(s2),
        (Constant::Int(i1), Constant::Int(i2)) => i1.cmp(i2),
        (Constant::Char(c1), Constant::Char(c2)) => c1.cmp(c2),
        _ => {
            // Fall back to debug-based comparison for mixed types.
            let d1 = format!("{:?}", c1);
            let d2 = format!("{:?}", c2);
            d1.cmp(&d2)
        }
    }
}

fn same_constructor(c1: &ConstructorDescription, c2: &ConstructorDescription) -> bool {
    crate::types::same_constructor(c1, c2)
}

type RecordPatternField = (
    crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    crate::types::LabelDescription,
    Pattern,
    bool,
);

fn records_args_for_le_pats(
    l1: &[RecordPatternField],
    l2: &[RecordPatternField],
) -> (Vec<Pattern>, Vec<Pattern>) {
    let mut ps = Vec::new();
    let mut qs = Vec::new();
    let mut i = 0;
    let mut j = 0;

    // OCaml `Parmatch.records_args` aligns already-sorted record fields by
    // `lbl_pos`, filling absent fields with omega (compiler/ml/parmatch.ml:267-283).
    while i < l1.len() || j < l2.len() {
        match (l1.get(i), l2.get(j)) {
            (Some((_, lbl1, p1, _)), Some((_, lbl2, p2, _))) => {
                if lbl1.lbl_pos < lbl2.lbl_pos {
                    ps.push(p1.clone());
                    qs.push(omega());
                    i += 1;
                } else if lbl1.lbl_pos > lbl2.lbl_pos {
                    ps.push(omega());
                    qs.push(p2.clone());
                    j += 1;
                } else {
                    ps.push(p1.clone());
                    qs.push(p2.clone());
                    i += 1;
                    j += 1;
                }
            }
            (Some((_, _, p1, _)), None) => {
                ps.push(p1.clone());
                qs.push(omega());
                i += 1;
            }
            (None, Some((_, _, p2, _))) => {
                ps.push(omega());
                qs.push(p2.clone());
                j += 1;
            }
            (None, None) => break,
        }
    }

    (ps, qs)
}

/// Check if one pattern is less specific than another (le_pat p q means
/// everything matched by q is also matched by p).
/// Equivalent to OCaml's `le_pat`.
fn le_pat(p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_var(..) | PatternDesc::Tpat_any, _) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => le_pat(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => le_pat(p, q),
        // OCaml reaches or-pattern implication through the `satisfiable`
        // fallback in `Parmatch.le_pat` (compiler/ml/parmatch.ml:1772-1791).
        (PatternDesc::Tpat_or(_, _, _), PatternDesc::Tpat_or(q1, q2, _)) => {
            le_pat(p, q1) && le_pat(p, q2)
        }
        (PatternDesc::Tpat_or(p1, p2, _), _) => le_pat(p1, q) || le_pat(p2, q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => le_pat(p, q1) && le_pat(p, q2),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (PatternDesc::Tpat_construct(_, c1, ps), PatternDesc::Tpat_construct(_, c2, qs)) => {
            same_constructor(c1, c2) && le_pats(ps, qs)
        }
        (
            PatternDesc::Tpat_variant(l1, Some(p1), _),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) => l1 == l2 && le_pat(p1, p2),
        (PatternDesc::Tpat_variant(l1, None, _), PatternDesc::Tpat_variant(l2, None, _)) => {
            l1 == l2
        }
        (PatternDesc::Tpat_variant(..), PatternDesc::Tpat_variant(..)) => false,
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => le_pats(ps, qs),
        (PatternDesc::Tpat_record(l1, _, _), PatternDesc::Tpat_record(l2, _, _)) => {
            let (ps, qs) = records_args_for_le_pats(l1, l2);
            le_pats(&ps, &qs)
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && le_pats(ps, qs)
        }
        // OCaml falls back to `not (satisfiable [[p]] [q])` here
        // (compiler/ml/parmatch.ml:1772-1791). Keep the remaining fallback
        // conservative until that enumeration path is ported.
        _ => false,
    }
}

/// Check if patterns ps are pairwise le_pat to qs.
fn le_pats(ps: &[Pattern], qs: &[Pattern]) -> bool {
    match (ps.first(), qs.first()) {
        (Some(p), Some(q)) => le_pat(p, q) && le_pats(&ps[1..], &qs[1..]),
        _ => true,
    }
}

/// Get minimal elements under a partial order `le`.
/// Equivalent to OCaml's `get_mins`.
fn get_mins<T: Clone>(le: impl Fn(&T, &T) -> bool, ps: Vec<T>) -> Vec<T> {
    fn select_rec<T: Clone>(le: &impl Fn(&T, &T) -> bool, r: Vec<T>, ps: &[T]) -> Vec<T> {
        match ps.split_first() {
            None => r,
            Some((p, rest)) => {
                if rest.iter().any(|p0| le(p0, p)) {
                    select_rec(le, r, rest)
                } else {
                    let mut new_r = vec![p.clone()];
                    new_r.extend(r);
                    select_rec(le, new_r, rest)
                }
            }
        }
    }
    let first_pass = select_rec(&le, Vec::new(), &ps);
    select_rec(&le, Vec::new(), &first_pass)
}

/// Raised when patterns are incompatible in lub.
struct Empty;

/// Least upper bound of two patterns (the most specific pattern that
/// matches everything matched by either p or q).
/// Returns Err(Empty) when p and q are incompatible.
fn lub(p: &Pattern, q: &Pattern) -> Result<Pattern, Empty> {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_alias(p, _, _), _) => lub(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => lub(p, q),
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _) => Ok(q.clone()),
        (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => Ok(p.clone()),
        (PatternDesc::Tpat_or(p1, p2, _), _) => orlub(p1, p2, q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => orlub(q1, q2, p),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2))
            if const_compare(c1, c2) == std::cmp::Ordering::Equal =>
        {
            Ok(p.clone())
        }
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => {
            let rs = lubs(ps, qs)?;
            Ok(make_pat(PatternDesc::Tpat_tuple(rs), p.pat_type, p.pat_env))
        }
        (PatternDesc::Tpat_construct(lid, c1, ps1), PatternDesc::Tpat_construct(_, c2, ps2))
            if same_constructor(c1, c2) =>
        {
            let rs = lubs(ps1, ps2)?;
            Ok(make_pat(
                PatternDesc::Tpat_construct(lid.clone(), c1.clone(), rs),
                p.pat_type,
                p.pat_env,
            ))
        }
        (
            PatternDesc::Tpat_variant(l1, Some(p1), row),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) if l1 == l2 => {
            let r = lub(p1, p2)?;
            Ok(make_pat(
                PatternDesc::Tpat_variant(l1.clone(), Some(Box::new(r)), *row),
                p.pat_type,
                p.pat_env,
            ))
        }
        (PatternDesc::Tpat_variant(l1, None, _), PatternDesc::Tpat_variant(l2, None, _))
            if l1 == l2 =>
        {
            Ok(p.clone())
        }
        (PatternDesc::Tpat_record(l1, closed, _), PatternDesc::Tpat_record(l2, _, _)) => {
            let rs = record_lubs(l1, l2)?;
            Ok(make_pat(
                PatternDesc::Tpat_record(rs, *closed, None),
                p.pat_type,
                p.pat_env,
            ))
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) if ps.len() == qs.len() => {
            let rs = lubs(ps, qs)?;
            Ok(make_pat(PatternDesc::Tpat_array(rs), p.pat_type, p.pat_env))
        }
        _ => Err(Empty),
    }
}

fn orlub(p1: &Pattern, p2: &Pattern, q: &Pattern) -> Result<Pattern, Empty> {
    match lub(p1, q) {
        Ok(r1) => match lub(p2, q) {
            Ok(r2) => Ok(Pattern {
                pat_desc: PatternDesc::Tpat_or(Box::new(r1), Box::new(r2), None),
                ..q.clone()
            }),
            Err(Empty) => Ok(r1),
        },
        Err(Empty) => lub(p2, q),
    }
}

/// Record field lub.
fn record_lubs(
    l1: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )],
    l2: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )],
) -> Result<
    Vec<(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )>,
    Empty,
> {
    type RecordField = (
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    );

    fn lub_rec(l1: &[RecordField], l2: &[RecordField]) -> Result<Vec<RecordField>, Empty> {
        match (l1.split_first(), l2.split_first()) {
            (None, _) => Ok(l2.to_vec()),
            (_, None) => Ok(l1.to_vec()),
            (Some(((lid1, lbl1, p1, o1), rem1)), Some(((lid2, lbl2, p2, o2), rem2))) => {
                if lbl1.lbl_pos < lbl2.lbl_pos {
                    let mut rest = lub_rec(rem1, l2)?;
                    rest.insert(0, (lid1.clone(), lbl1.clone(), p1.clone(), *o1));
                    Ok(rest)
                } else if lbl2.lbl_pos < lbl1.lbl_pos {
                    let mut rest = lub_rec(l1, rem2)?;
                    rest.insert(0, (lid2.clone(), lbl2.clone(), p2.clone(), *o2));
                    Ok(rest)
                } else {
                    if o1 != o2 {
                        return Err(Empty);
                    }
                    let p = lub(p1, p2)?;
                    let mut rest = lub_rec(rem1, rem2)?;
                    rest.insert(0, (lid1.clone(), lbl1.clone(), p, *o1));
                    Ok(rest)
                }
            }
        }
    }
    lub_rec(l1, l2)
}

fn lubs(ps: &[Pattern], qs: &[Pattern]) -> Result<Vec<Pattern>, Empty> {
    match (ps.split_first(), qs.split_first()) {
        (Some((p, ps_rest)), Some((q, qs_rest))) => {
            let head = lub(p, q)?;
            let mut tail = lubs(ps_rest, qs_rest)?;
            tail.insert(0, head);
            Ok(tail)
        }
        _ => Ok(Vec::new()),
    }
}

/// Normalize a pattern: replace all sub-pattern arguments with omega.
/// Equivalent to OCaml's `normalize_pat`.
fn normalize_pat(q: &Pattern) -> Pattern {
    match &q.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) => q.clone(),
        PatternDesc::Tpat_var(..) => make_pat(PatternDesc::Tpat_any, q.pat_type, q.pat_env),
        PatternDesc::Tpat_alias(p, _, _) => normalize_pat(p),
        PatternDesc::Tpat_tuple(args) => make_pat(
            PatternDesc::Tpat_tuple(omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_construct(lid, c, args) => make_pat(
            PatternDesc::Tpat_construct(lid.clone(), c.clone(), omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_variant(l, arg, row) => make_pat(
            PatternDesc::Tpat_variant(l.clone(), arg.as_ref().map(|_| Box::new(omega())), *row),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_array(args) => make_pat(
            PatternDesc::Tpat_array(omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_record(largs, closed, _) => make_pat(
            PatternDesc::Tpat_record(
                largs
                    .iter()
                    .map(|(lid, lbl, _, opt)| (lid.clone(), lbl.clone(), omega(), *opt))
                    .collect(),
                *closed,
                None,
            ),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_or(..) => {
            panic!("Parmatch.normalize_pat: Tpat_or")
        }
    }
}

/// Read n arguments from `r`, returning (args, rest).
fn read_args<T: Clone>(xs: &[T], r: &[Pattern]) -> (Vec<Pattern>, Vec<Pattern>) {
    if xs.is_empty() {
        return (Vec::new(), r.to_vec());
    }
    assert!(!r.is_empty(), "Parmatch.read_args: not enough arguments");
    let (mut args, rest) = read_args(&xs[1..], &r[1..]);
    args.insert(0, r[0].clone());
    (args, rest)
}

/// Set the arguments of a normalized pattern, optionally erasing mutable fields.
/// Equivalent to OCaml's `do_set_args`.
fn do_set_args(erase_mutable: bool, q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    match &q.pat_desc {
        PatternDesc::Tpat_tuple(pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_tuple(args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_record(fields, closed, _) => {
            let (args, rest) = read_args(fields.as_slice(), r);
            let new_fields: Vec<_> = fields
                .iter()
                .zip(args.iter())
                .map(|((lid, lbl, _, opt), arg)| {
                    if erase_mutable && matches!(lbl.lbl_mut, MutableFlag::Mutable) {
                        (lid.clone(), lbl.clone(), omega(), *opt)
                    } else {
                        (lid.clone(), lbl.clone(), arg.clone(), *opt)
                    }
                })
                .collect();
            let mut result = vec![make_pat(
                PatternDesc::Tpat_record(new_fields, *closed, None),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_construct(lid, c, pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_construct(lid.clone(), c.clone(), args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_variant(l, opt_omega, row) => {
            let (arg, rest) = match (opt_omega, r) {
                (Some(_), [a, rest @ ..]) => (Some(Box::new(a.clone())), rest.to_vec()),
                (None, _) => (None, r.to_vec()),
                _ => panic!("Parmatch.set_args: variant"),
            };
            let mut result = vec![make_pat(
                PatternDesc::Tpat_variant(l.clone(), arg, *row),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_array(pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_array(args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_any => {
            let mut result = vec![q.clone()];
            result.extend_from_slice(r);
            result
        }
        _ => panic!("Parmatch.set_args"),
    }
}

/// `set_args q r` — set actual arguments of the matching pattern.
fn set_args(q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    do_set_args(false, q, r)
}

/// `set_args_erase_mutable q r` — like set_args but replaces mutable fields with omega.
fn set_args_erase_mutable(q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    do_set_args(true, q, r)
}

fn untagged_payload_type_cannot_be_undefined(
    ctx_ref: &TypeContext,
    env_ref: EnvRef,
    ty: TypeExprRef,
) -> bool {
    let Some(env) = ctx_ref.get_typed_env(env_ref) else {
        return false;
    };
    let ty = crate::types::ctype::expand_head(ctx_ref, env.as_ref(), ty);
    match &*ctx_ref.get_desc(ty) {
        crate::types::type_expr::TypeDesc::Tconstr { path, .. } => {
            path.same(&crate::types::predef::path_string())
                || path.same(&crate::types::predef::path_int())
                || path.same(&crate::types::predef::path_float())
                || path.same(&crate::types::predef::path_bigint())
                || path.same(&crate::types::predef::path_bool())
                || path.same(&crate::types::predef::path_array())
                || matches!(path, crate::types::path::Path::Pident(id) if id.name() == "dict")
                || matches!(path.name().as_str(), "Js.Dict.t" | "Js_dict.t")
        }
        crate::types::type_expr::TypeDesc::Tarrow { .. }
        | crate::types::type_expr::TypeDesc::Ttuple(_) => true,
        _ => false,
    }
}

fn can_strip_optional_construct_wrapper(
    ctx_ref: &TypeContext,
    pat_env: EnvRef,
    cstr: &ConstructorDescription,
) -> bool {
    if !has_untagged(&cstr.cstr_attributes) {
        return false;
    }

    if cstr.cstr_inlined.is_some() {
        return true;
    }

    match cstr.cstr_args.as_slice() {
        [] => false,
        [arg] => untagged_payload_type_cannot_be_undefined(ctx_ref, pat_env, *arg),
        [_, _, ..] => true,
    }
}

/// Expand record pattern to all fields (filling missing with omega).
/// OCaml's `all_record_args` uses `lbl_all` to get ALL labels, then fills
/// missing ones with omega. Since Rust's `lbl_all` is a placeholder, we
/// resolve via the TypeContext when available.
fn strip_optional_record_pattern_wrapper(
    ctx_ref: Option<&TypeContext>,
    lbl: &LabelDescription,
    pat: &Pattern,
) -> Pattern {
    if !lbl.lbl_optional || matches!(lbl.lbl_repres, RecordRepresentation::RecordInlined { .. }) {
        return pat.clone();
    }

    match &pat.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, args)
            if cstr.cstr_name == "Some" && args.len() == 1 =>
        {
            match &args[0].pat_desc {
                PatternDesc::Tpat_constant(_) => args[0].clone(),
                PatternDesc::Tpat_construct(_, inner_cstr, _) => match ctx_ref {
                    Some(ctx_ref)
                        if can_strip_optional_construct_wrapper(
                            ctx_ref,
                            args[0].pat_env,
                            inner_cstr,
                        ) =>
                    {
                        args[0].clone()
                    }
                    _ => pat.clone(),
                },
                _ => pat.clone(),
            }
        }
        _ => pat.clone(),
    }
}

fn all_record_args(
    ctx_ref: Option<&TypeContext>,
    pat_type: TypeExprRef,
    pat_env: EnvRef,
    lbls: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )],
) -> Vec<(
    crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    crate::types::LabelDescription,
    Pattern,
    bool,
)> {
    if lbls.is_empty() {
        return Vec::new();
    }

    let first_lbl = &lbls[0].1;
    let first_opt = lbls[0].3;

    // OCaml expands through the typed label's own `lbl_all` array, not by
    // guessing another record declaration with compatible positions. See
    // compiler/ml/matching.ml:218-224 and 540-563.
    let all_labels = ctx_ref.and_then(|ctx| {
        resolve_labels_from_type(ctx, first_lbl.lbl_res, pat_env)
            .filter(|labels| record_labels_cover_pattern_fields(labels, lbls))
            .or_else(|| {
                resolve_labels_from_type(ctx, pat_type, pat_env)
                    .filter(|labels| record_labels_cover_pattern_fields(labels, lbls))
            })
            .or_else(|| {
                let cached = ctx.get_dict_pattern_labels();
                if cached.is_empty() {
                    return None;
                }
                let matches_cached = lbls.iter().all(|(_, lbl, _, _)| {
                    cached
                        .iter()
                        .any(|(name, pos, _, _, _)| name == &lbl.lbl_name && *pos == lbl.lbl_pos)
                });
                if !matches_cached {
                    return None;
                }
                Some(
                    cached
                        .into_iter()
                        .map(|(name, pos, mutflag, repr, attrs)| LabelDescription {
                            lbl_name: name,
                            lbl_res: TypeExprRef(0),
                            lbl_arg: TypeExprRef(0),
                            lbl_mut: mutflag,
                            lbl_optional: true,
                            lbl_pos: pos,
                            lbl_all: crate::types::decl::LabelArrayRef(0),
                            lbl_repres: repr,
                            lbl_private: crate::types::asttypes::PrivateFlag::Public,
                            lbl_loc: crate::location::Location::none(),
                            lbl_attributes: attrs,
                        })
                        .collect(),
                )
            })
    });

    match all_labels {
        Some(all_labels) => {
            // Build a full array with omega for missing fields
            let dummy_loc = crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0),
                loc: LocIdx::none(),
            };
            let mut result: Vec<_> = all_labels
                .iter()
                .map(|lbl| (dummy_loc.clone(), lbl.clone(), omega(), first_opt))
                .collect();
            // Fill in the actual patterns from the provided fields
            for (id, lbl, pat, opt) in lbls {
                if (lbl.lbl_pos as usize) < result.len() {
                    let rewritten_pat = strip_optional_record_pattern_wrapper(ctx_ref, lbl, pat);
                    result[lbl.lbl_pos as usize] = (id.clone(), lbl.clone(), rewritten_pat, *opt);
                }
            }
            result
        }
        None => {
            // Fallback: return fields as-is (old behavior)
            lbls.to_vec()
        }
    }
}

/// Check if two constructors may be equal (considering extension types).
fn may_equal_constr(
    c1: &crate::types::ConstructorDescription,
    c2: &crate::types::ConstructorDescription,
) -> bool {
    crate::types::may_equal_constructor(c1, c2)
}

/// Compatibility predicate: may_compat p q returns false when p and q
/// never admit a common instance.
fn may_compat(p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _)
        | (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => may_compat(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => may_compat(p, q),
        (PatternDesc::Tpat_or(p1, p2, _), _) => may_compat(p1, q) || may_compat(p2, q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => may_compat(p, q1) || may_compat(p, q2),
        (PatternDesc::Tpat_construct(_, c1, ps1), PatternDesc::Tpat_construct(_, c2, ps2)) => {
            may_equal_constr(c1, c2) && may_compats(ps1, ps2)
        }
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (PatternDesc::Tpat_variant(l1, op1, _), PatternDesc::Tpat_variant(l2, op2, _)) => {
            l1 == l2
                && match (op1, op2) {
                    (Some(p1), Some(p2)) => may_compat(p1, p2),
                    (None, None) => true,
                    _ => false,
                }
        }
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => may_compats(ps, qs),
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && may_compats(ps, qs)
        }
        (PatternDesc::Tpat_record(l1, _, _), PatternDesc::Tpat_record(l2, _, _)) => {
            // Check compatible fields only
            may_compats_record(l1, l2)
        }
        // OCaml's Parmatch.Compat.compat rejects cross-shape pairs here.
        _ => false,
    }
}

fn may_compats(ps: &[Pattern], qs: &[Pattern]) -> bool {
    ps.iter().zip(qs.iter()).all(|(p, q)| may_compat(p, q))
}

fn may_compats_record(
    l1: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )],
    l2: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        crate::types::LabelDescription,
        Pattern,
        bool,
    )],
) -> bool {
    // For each field present in both, check compatibility
    for (_, lbl1, p1, _) in l1 {
        for (_, lbl2, p2, _) in l2 {
            if lbl1.lbl_pos == lbl2.lbl_pos && !may_compat(p1, p2) {
                return false;
            }
        }
    }
    true
}

// ============================================================================
// Matrix type — pattern list list
// ============================================================================

/// A pattern matrix: each row is a list of patterns.
pub type Matrix = Vec<Vec<Pattern>>;

/// Prepend an omega (wildcard) column to each row of a matrix.
pub fn add_omega_column(pss: &Matrix) -> Matrix {
    pss.iter()
        .map(|ps| {
            let mut row = vec![omega()];
            row.extend(ps.iter().cloned());
            row
        })
        .collect()
}

// ============================================================================
// Context type
// ============================================================================

/// A context: a pair of pattern lists (left, right) where columns are
/// partitioned into left and right parts.
#[derive(Debug, Clone)]
pub struct Ctx {
    pub left: Vec<Pattern>,
    pub right: Vec<Pattern>,
}

/// Check if context c1 is less-or-equal to c2.
pub fn le_ctx(c1: &Ctx, c2: &Ctx) -> bool {
    le_pats(&c1.left, &c2.left) && le_pats(&c1.right, &c2.right)
}

/// Shift the first element of `right` to the front of `left`.
pub fn lshift(ctx: &Ctx) -> Ctx {
    match ctx.right.split_first() {
        Some((x, xs)) => Ctx {
            left: {
                let mut l = vec![x.clone()];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lshift: empty right"),
    }
}

/// Shift an omega to the front of `left`, dropping the first element of `right`.
pub fn lforget(ctx: &Ctx) -> Ctx {
    match ctx.right.split_first() {
        Some((_, xs)) => Ctx {
            left: {
                let mut l = vec![omega()];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lforget: empty right"),
    }
}

/// Check if a slice is small enough (length <= n).
fn small_enough(n: usize, slice: &[Ctx]) -> bool {
    slice.len() <= n
}

/// Shift left for a list of contexts, with pruning when too large.
pub fn ctx_lshift(ctx: &[Ctx]) -> Vec<Ctx> {
    if small_enough(31, ctx) {
        ctx.iter().map(lshift).collect()
    } else {
        // Context pruning
        let forgotten: Vec<Ctx> = ctx.iter().map(lforget).collect();
        get_mins(le_ctx, forgotten)
    }
}

/// Shift the first element of `left` to the front of `right`.
pub fn rshift(ctx: &Ctx) -> Ctx {
    match ctx.left.split_first() {
        Some((p, ps)) => Ctx {
            left: ps.to_vec(),
            right: {
                let mut r = vec![p.clone()];
                r.extend(ctx.right.iter().cloned());
                r
            },
        },
        None => panic!("rshift: empty left"),
    }
}

/// Right-shift all contexts.
pub fn ctx_rshift(ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(rshift).collect()
}

/// Split off the first n elements from a pattern list.
/// Returns (first_n, rest).
fn nchars(n: usize, ps: &[Pattern]) -> (Vec<Pattern>, Vec<Pattern>) {
    if n == 0 {
        return (Vec::new(), ps.to_vec());
    }
    match ps.split_first() {
        Some((p, rem)) => {
            let (mut chars, cdrs) = nchars(n - 1, rem);
            chars.insert(0, p.clone());
            (chars, cdrs)
        }
        None => panic!("nchars: not enough patterns"),
    }
}

/// Right-shift n elements from left to right.
pub fn rshift_num(n: usize, ctx: &Ctx) -> Ctx {
    let (shifted, left) = nchars(n, &ctx.left);
    let mut right = shifted;
    right.extend(ctx.right.iter().cloned());
    Ctx { left, right }
}

/// Right-shift n elements for all contexts.
pub fn ctx_rshift_num(n: usize, ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(|c| rshift_num(n, c)).collect()
}

/// Recombination of contexts: take the first element from left,
/// and set its arguments from right, erasing mutable fields.
/// e.g. `(_,_)::p1::p2::rem -> (p1,p2)::rem`
pub fn combine(ctx: &Ctx) -> Ctx {
    match ctx.left.split_first() {
        Some((p, ps)) => {
            let result = set_args_erase_mutable(p, &ctx.right);
            // The first element of result is the combined pattern;
            // the rest is the remaining right.
            Ctx {
                left: ps.to_vec(),
                right: result,
            }
        }
        None => panic!("combine: empty left"),
    }
}

/// Combine all contexts.
pub fn ctx_combine(ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(combine).collect()
}

/// Number of columns in a matrix (length of first row, or 0 if empty).
pub fn ncols(pss: &Matrix) -> usize {
    match pss.first() {
        Some(ps) => ps.len(),
        None => 0,
    }
}

// ============================================================================
// NoMatch / OrPat exceptions (represented as Result/enum in Rust)
// ============================================================================

/// Errors that can occur during pattern matching filtering.
enum MatchError {
    /// Pattern doesn't match.
    NoMatch,
    /// Pattern is an or-pattern that needs expansion.
    OrPat,
}

// ============================================================================
// filter_matrix — filter a matrix according to a matcher function
// ============================================================================

/// Filter a pattern matrix using a matcher function.
/// The matcher takes a pattern and the rest of the row, and returns
/// the filtered row or an error.
///
/// Equivalent to OCaml's `filter_matrix`.
pub fn filter_matrix(
    matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
    pss: &Matrix,
) -> Matrix {
    fn filter_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
        pss: &[Vec<Pattern>],
    ) -> Matrix {
        match pss.split_first() {
            None => Vec::new(),
            Some((row, rem)) => {
                if row.is_empty() {
                    // Empty rows shouldn't appear here — fatal error in OCaml.
                    panic!("Matching.filter_matrix: empty row");
                }
                let p = &row[0];
                let ps = &row[1..];
                match &p.pat_desc {
                    PatternDesc::Tpat_alias(p_inner, _, _) => {
                        let mut new_row = vec![(**p_inner).clone()];
                        new_row.extend(ps.iter().cloned());
                        let mut new_pss = vec![new_row];
                        new_pss.extend(rem.iter().cloned());
                        filter_rec(matcher, &new_pss)
                    }
                    PatternDesc::Tpat_var(..) => {
                        let mut new_row = vec![omega()];
                        new_row.extend(ps.iter().cloned());
                        let mut new_pss = vec![new_row];
                        new_pss.extend(rem.iter().cloned());
                        filter_rec(matcher, &new_pss)
                    }
                    _ => {
                        let mut rest = filter_rec(matcher, rem);
                        match matcher(p, ps) {
                            Ok(filtered_row) => {
                                rest.insert(0, filtered_row);
                                rest
                            }
                            Err(MatchError::NoMatch) => rest,
                            Err(MatchError::OrPat) => match &p.pat_desc {
                                PatternDesc::Tpat_or(p1, p2, _) => {
                                    let mut row1 = vec![(**p1).clone()];
                                    row1.extend(ps.iter().cloned());
                                    let mut row2 = vec![(**p2).clone()];
                                    row2.extend(ps.iter().cloned());
                                    let mut expanded = filter_rec(matcher, &[row1, row2]);
                                    expanded.extend(rest);
                                    expanded
                                }
                                _ => panic!("filter_matrix: OrPat on non-or pattern"),
                            },
                        }
                    }
                }
            }
        }
    }
    filter_rec(matcher, pss)
}

// ============================================================================
// make_default — build default environment by filtering
// ============================================================================

/// Default environment entry: (matrix, exit_number).
pub type DefaultEnv = Vec<(Matrix, i32)>;

/// Build default environment by filtering each matrix with the given matcher.
/// Equivalent to OCaml's `make_default`.
pub fn make_default(
    matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
    env: &DefaultEnv,
) -> DefaultEnv {
    fn make_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
        env: &[(Matrix, i32)],
    ) -> DefaultEnv {
        match env.split_first() {
            None => Vec::new(),
            Some(((pss, i), rem)) => {
                // Check for terminal: [[]] case
                if pss.len() == 1 && pss[0].is_empty() {
                    return vec![(vec![Vec::new()], *i)];
                }
                let rest = make_rec(matcher, rem);
                let filtered = filter_matrix(matcher, pss);
                if filtered.is_empty() {
                    rest
                } else if !filtered.is_empty() && filtered.iter().any(|row| row.is_empty()) {
                    let mut result = vec![(vec![Vec::new()], *i)];
                    result.extend(rest);
                    result
                } else {
                    let mut result = vec![(filtered, *i)];
                    result.extend(rest);
                    result
                }
            }
        }
    }
    make_rec(matcher, env)
}

// ============================================================================
// ctx_matcher — build a context matcher from a pattern
// ============================================================================

/// Build a matcher function from a pattern, for use with filter_ctx.
/// Returns a closure that, given a pattern q and remaining patterns,
/// returns (to_left_pattern, expanded_right) or Err(NoMatch).
///
/// Equivalent to OCaml's `ctx_matcher`.
pub fn ctx_matcher<'a>(
    ctx_ref: Option<&'a TypeContext>,
    p: &Pattern,
) -> Box<dyn Fn(&Pattern, &[Pattern]) -> Result<(Pattern, Vec<Pattern>), MatchError> + 'a> {
    let p = normalize_pat(p);
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, pats) => {
            let cstr = cstr.clone();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_construct(_, cstr2, args) if may_equal_constr(&cstr, cstr2) => {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_constant(cst) => {
            let cst = cst.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_constant(cst2)
                    if const_compare(&cst, cst2) == std::cmp::Ordering::Equal =>
                {
                    Ok((p.clone(), rem.to_vec()))
                }
                PatternDesc::Tpat_any => Ok((p.clone(), rem.to_vec())),
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_variant(lab, Some(omega_pat), _) => {
            let lab = lab.clone();
            let omega_pat = (**omega_pat).clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, Some(arg), _) if lab == *lab2 => {
                    let mut result = vec![(**arg).clone()];
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = vec![omega_pat.clone()];
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_variant(lab, None, _) => {
            let lab = lab.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, None, _) if lab == *lab2 => {
                    Ok((p.clone(), rem.to_vec()))
                }
                PatternDesc::Tpat_any => Ok((p.clone(), rem.to_vec())),
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_array(pats) => {
            let len = pats.len();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_array(args) if args.len() == len => {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_tuple(pats) => {
            let len = pats.len();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_tuple(args) if args.len() == len => {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_record(fields, _, _) if !fields.is_empty() => {
            let fields = fields.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_record(fields2, _, _) if !fields2.is_empty() => {
                    let expanded = all_record_args(ctx_ref, q.pat_type, q.pat_env, fields2);
                    let mut result: Vec<Pattern> =
                        expanded.iter().map(|(_, _, p, _)| p.clone()).collect();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result: Vec<Pattern> =
                        fields.iter().map(|(_, _, p, _)| p.clone()).collect();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        _ => panic!("Matching.ctx_matcher: unsupported pattern"),
    }
}

// ============================================================================
// filter_ctx — filter a context list using a ctx_matcher
// ============================================================================

/// Filter contexts using a matcher built from pattern q.
/// Equivalent to OCaml's `filter_ctx`.
pub fn filter_ctx<'a>(ctx_ref: Option<&'a TypeContext>, q: &Pattern, ctx: &[Ctx]) -> Vec<Ctx> {
    let matcher = ctx_matcher(ctx_ref, q);

    fn filter_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<(Pattern, Vec<Pattern>), MatchError>,
        ctx: &[Ctx],
    ) -> Vec<Ctx> {
        match ctx.split_first() {
            None => Vec::new(),
            Some((l, rem)) => match l.right.split_first() {
                None => panic!("Matching.filter_ctx: empty right"),
                Some((p, ps)) => match &p.pat_desc {
                    PatternDesc::Tpat_or(p1, p2, _) => {
                        let ctx1 = Ctx {
                            left: l.left.clone(),
                            right: {
                                let mut r = vec![(**p1).clone()];
                                r.extend(ps.iter().cloned());
                                r
                            },
                        };
                        let ctx2 = Ctx {
                            left: l.left.clone(),
                            right: {
                                let mut r = vec![(**p2).clone()];
                                r.extend(ps.iter().cloned());
                                r
                            },
                        };
                        let mut expanded = vec![ctx1, ctx2];
                        expanded.extend(rem.iter().cloned());
                        filter_rec(matcher, &expanded)
                    }
                    PatternDesc::Tpat_alias(p_inner, _, _) => {
                        let ctx_new = Ctx {
                            left: l.left.clone(),
                            right: {
                                let mut r = vec![(**p_inner).clone()];
                                r.extend(ps.iter().cloned());
                                r
                            },
                        };
                        let mut expanded = vec![ctx_new];
                        expanded.extend(rem.iter().cloned());
                        filter_rec(matcher, &expanded)
                    }
                    PatternDesc::Tpat_var(..) => {
                        let ctx_new = Ctx {
                            left: l.left.clone(),
                            right: {
                                let mut r = vec![omega()];
                                r.extend(ps.iter().cloned());
                                r
                            },
                        };
                        let mut expanded = vec![ctx_new];
                        expanded.extend(rem.iter().cloned());
                        filter_rec(matcher, &expanded)
                    }
                    _ => {
                        let mut rest = filter_rec(matcher, rem);
                        match matcher(p, ps) {
                            Ok((to_left, right)) => {
                                let mut left = vec![to_left];
                                left.extend(l.left.iter().cloned());
                                rest.insert(0, Ctx { left, right });
                                rest
                            }
                            Err(_) => rest,
                        }
                    }
                },
            },
        }
    }

    filter_rec(&*matcher, ctx)
}

// ============================================================================
// select_columns, ctx_lub, ctx_match
// ============================================================================

/// Select columns from pattern rows and combine with context.
/// Equivalent to OCaml's `select_columns`.
pub fn select_columns(pss: &Matrix, ctx: &[Ctx]) -> Vec<Ctx> {
    let n = ncols(pss);
    let mut result = Vec::new();
    for ps in pss.iter().rev() {
        for c in ctx.iter().rev() {
            let (transfert, right) = nchars(n, &c.right);
            match lubs_checked(&transfert, ps) {
                Ok(lub_result) => {
                    let mut left = lub_result;
                    left.extend(c.left.iter().cloned());
                    result.push(Ctx { left, right });
                }
                Err(Empty) => { /* skip incompatible */ }
            }
        }
    }
    result.reverse();
    result
}

/// Helper: lubs that returns Result.
fn lubs_checked(ps: &[Pattern], qs: &[Pattern]) -> Result<Vec<Pattern>, Empty> {
    lubs(ps, qs)
}

/// Least upper bound of a pattern with contexts.
/// Equivalent to OCaml's `ctx_lub`.
pub fn ctx_lub(p: &Pattern, ctx: &[Ctx]) -> Vec<Ctx> {
    let mut result = Vec::new();
    for c in ctx.iter().rev() {
        match c.right.split_first() {
            Some((q, rem)) => match lub(p, q) {
                Ok(r) => {
                    let mut right = vec![r];
                    right.extend(rem.iter().cloned());
                    result.push(Ctx {
                        left: c.left.clone(),
                        right,
                    });
                }
                Err(Empty) => { /* skip */ }
            },
            None => panic!("Matching.ctx_lub: empty right"),
        }
    }
    result.reverse();
    result
}

/// Check if any context's right side may be compatible with any row in pss.
/// Equivalent to OCaml's `ctx_match`.
pub fn ctx_match(ctx: &[Ctx], pss: &Matrix) -> bool {
    ctx.iter()
        .any(|c| pss.iter().any(|ps| may_compats(&c.right, ps)))
}

// ============================================================================
// Jumps — mapping from exit numbers to context lists
// ============================================================================

/// Jump table: sorted list of (exit_number, context_list) pairs,
/// sorted in descending order by exit number.
pub type Jumps = Vec<(i32, Vec<Ctx>)>;

/// Extract the contexts for exit number i, returning (extracted, remaining).
pub fn jumps_extract(i: i32, jumps: &Jumps) -> (Vec<Ctx>, Jumps) {
    match jumps.split_first() {
        None => (Vec::new(), Vec::new()),
        Some(((j, pss), rem)) => {
            if i == *j {
                (pss.clone(), rem.to_vec())
            } else if *j < i {
                (Vec::new(), jumps.to_vec())
            } else {
                let (r, mut remaining) = jumps_extract(i, &rem.to_vec());
                remaining.insert(0, (*j, pss.clone()));
                (r, remaining)
            }
        }
    }
}

/// Remove the entry for exit number i.
pub fn jumps_remove(i: i32, jumps: &Jumps) -> Jumps {
    match jumps.split_first() {
        None => Vec::new(),
        Some(((j, _), rem)) if i == *j => rem.to_vec(),
        Some((x, rem)) => {
            let mut result = vec![x.clone()];
            result.extend(jumps_remove(i, &rem.to_vec()));
            result
        }
    }
}

/// Empty jump table.
pub fn jumps_empty() -> Jumps {
    Vec::new()
}

/// Check if a jump table is empty.
pub fn jumps_is_empty(jumps: &Jumps) -> bool {
    jumps.is_empty()
}

/// Create a singleton jump table (or empty if ctx is empty).
pub fn jumps_singleton(i: i32, ctx: Vec<Ctx>) -> Jumps {
    if ctx.is_empty() {
        Vec::new()
    } else {
        vec![(i, ctx)]
    }
}

/// Add contexts for exit number i to the jump table.
/// Maintains descending sort order and merges with get_mins when
/// the exit number already exists.
pub fn jumps_add(i: i32, pss: Vec<Ctx>, mut jumps: Jumps) -> Jumps {
    if pss.is_empty() {
        return jumps;
    }
    fn add(i: i32, pss: Vec<Ctx>, jumps: &[(i32, Vec<Ctx>)]) -> Jumps {
        match jumps.split_first() {
            None => vec![(i, pss)],
            Some(((j, qss), rem)) => {
                if *j > i {
                    let mut result = vec![(j.clone(), qss.clone())];
                    result.extend(add(i, pss, rem));
                    result
                } else if *j < i {
                    let mut result = vec![(i, pss)];
                    result.extend(jumps.to_vec());
                    result
                } else {
                    // Same exit number: merge with get_mins
                    let mut combined = pss;
                    combined.extend(qss.iter().cloned());
                    let mut result = vec![(i, get_mins(le_ctx, combined))];
                    result.extend(rem.to_vec());
                    result
                }
            }
        }
    }
    add(i, pss, &jumps)
}

/// Union of two jump tables.
/// Maintains descending sort order and merges contexts with get_mins.
pub fn jumps_union(env1: &Jumps, env2: &Jumps) -> Jumps {
    match (env1.split_first(), env2.split_first()) {
        (None, _) => env2.clone(),
        (_, None) => env1.clone(),
        (Some(((i1, pss1), rem1)), Some(((i2, pss2), rem2))) => {
            if i1 == i2 {
                let mut combined = pss1.clone();
                combined.extend(pss2.iter().cloned());
                let mut result = vec![(*i1, get_mins(le_ctx, combined))];
                result.extend(jumps_union(&rem1.to_vec(), &rem2.to_vec()));
                result
            } else if i1 > i2 {
                let mut result = vec![(*i1, pss1.clone())];
                result.extend(jumps_union(&rem1.to_vec(), env2));
                result
            } else {
                let mut result = vec![(*i2, pss2.clone())];
                result.extend(jumps_union(env1, &rem2.to_vec()));
                result
            }
        }
    }
}

/// Merge adjacent pairs of jump tables (used by jumps_unions).
fn merge(envs: Vec<Jumps>) -> Vec<Jumps> {
    if envs.len() < 2 {
        return envs;
    }
    let mut result = Vec::new();
    let mut iter = envs.into_iter();
    loop {
        match (iter.next(), iter.next()) {
            (Some(e1), Some(e2)) => result.push(jumps_union(&e1, &e2)),
            (Some(e1), None) => {
                result.push(e1);
                break;
            }
            (None, _) => break,
        }
    }
    result
}

/// Union of a list of jump tables (using balanced merge).
pub fn jumps_unions(envs: Vec<Jumps>) -> Jumps {
    match envs.len() {
        0 => Vec::new(),
        1 => envs.into_iter().next().unwrap(),
        _ => jumps_unions(merge(envs)),
    }
}

/// Map a function over the context lists in a jump table.
pub fn jumps_map(f: impl Fn(Vec<Ctx>) -> Vec<Ctx>, env: &Jumps) -> Jumps {
    env.iter().map(|(i, pss)| (*i, f(pss.clone()))).collect()
}

// ============================================================================
// Pattern matching before compilation
// ============================================================================

/// Pattern matching before any compilation.
/// Equivalent to OCaml's `pattern_matching`.
#[derive(Clone)]
pub struct PatternMatching {
    /// Cases: list of (pattern_row, action).
    cases: Vec<Clause>,
    /// Arguments to match against: (expression, let_kind).
    pub args: MatchArgs,
    /// Default: mapping from matrices to exit numbers.
    pub default: DefaultEnv,
}

// ============================================================================
// Pattern matching after or-pat and mixture rule application
// ============================================================================

/// Pattern matching after application of both the or-pat rule and the
/// mixture rule.
#[derive(Clone)]
pub struct PmOrCompiled {
    /// The body pattern matching.
    pub body: PatternMatching,
    /// Handlers for or-patterns: (matrix, exit_number, idents, pattern_matching).
    pub handlers: Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>,
    /// The or-pattern matrix.
    pub or_matrix: Matrix,
}

/// Half-compiled pattern matching.
#[derive(Clone)]
pub enum PmHalfCompiled {
    /// Or-pattern compiled.
    PmOr(PmOrCompiled),
    /// Variable case.
    PmVar(PmVarCompiled),
    /// Simple pattern matching.
    Pm(PatternMatching),
}

/// Variable case in half-compiled pattern matching.
#[derive(Clone)]
pub struct PmVarCompiled {
    /// The inner half-compiled pattern matching.
    pub inside: Box<PmHalfCompiled>,
    /// The variable argument.
    pub var_arg: RawLambda,
}

/// Half-compiled pattern matching with associated info.
pub struct PmHalfCompiledInfo {
    /// The half-compiled pattern matching.
    pub me: PmHalfCompiled,
    /// The associated matrix.
    pub matrix: Matrix,
    /// The top-level default environment.
    pub top_default: DefaultEnv,
}

// ============================================================================
// Layer 2: Catch/exit and action sharing
// ============================================================================
// Ported from OCaml's matching.ml lines 442-587.

// ============================================================================
// Lambda.make_key — normalize a RawLambda for structural comparison
// ============================================================================

/// Maximum size for make_key normalization (matches OCaml's max_raw = 32).
const MAX_RAW: i32 = 32;

fn charge_logical_record_fields(
    count: &mut i32,
    primitive: &Primitive,
    actual_arg_count: usize,
) -> Option<()> {
    let Primitive::Pmakeblock(
        tag_info @ (TagInfo::Record { .. } | TagInfo::RecordInlined { .. }),
        _,
    ) = primitive
    else {
        return Some(());
    };

    let logical_count = tag_info.logical_field_count();
    if logical_count > actual_arg_count {
        *count += (logical_count - actual_arg_count) as i32;
        if *count > MAX_RAW {
            return None;
        }
    }
    Some(())
}

/// Normalize a RawLambda for structural comparison.
/// - Alias lets are substituted (variable replaced by its definition)
/// - Other let-bound variables get sequential normalized names
/// - Locations are cleared
/// Returns None if the lambda is too complex (functions, letrec, loops, etc.)
///
/// Equivalent to OCaml's `Lambda.make_key`.
fn make_key(e: &RawLambda) -> Option<RawLambda> {
    let mut count = 0i32;
    type KeyEnv = Vec<(Ident, RawLambda)>;
    fn tr_rec(
        env: &mut KeyEnv,
        e: &RawLambda,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<RawLambda> {
        *count += 1;
        if *count > MAX_RAW {
            return None; // Too big
        }
        match e {
            RawLambda::Lvar(id) => {
                if let Some((_, replacement)) = env.iter().rev().find(|(key, _)| key.same(id)) {
                    Some(replacement.clone())
                } else {
                    Some(e.clone())
                }
            }
            RawLambda::Lconst(crate::lambda::Constant::String { .. }) => {
                // Mutable constants are not shared
                None
            }
            RawLambda::Lconst(_) => Some(e.clone()),
            RawLambda::LglobalModule(_, _) => Some(e.clone()),
            RawLambda::Lapply(ap) => {
                let func = tr_rec(env, &ap.ap_func, count, next_id)?;
                let args = tr_recs(env, &ap.ap_args, count, next_id)?;
                Some(RawLambda::Lapply(RawApply {
                    ap_func: Box::new(func),
                    ap_args: args,
                    ap_info: crate::lambda::ApInfo {
                        loc: Location::none(),
                        ..ap.ap_info.clone()
                    },
                    ap_transformed_jsx: ap.ap_transformed_jsx,
                }))
            }
            RawLambda::Llet(LetKind::Alias, x, ex, body) => {
                // Ignore aliases -> substitute
                let ex = tr_rec(env, ex, count, next_id)?;
                env.push((x.clone(), ex));
                let result = tr_rec(env, body, count, next_id);
                env.pop();
                result
            }
            RawLambda::Llet(kind, x, ex, body)
                if matches!(
                    (kind, body.as_ref()),
                    (LetKind::Strict | LetKind::StrictOpt, RawLambda::Lvar(v)) if v.same(x)
                ) =>
            {
                // Llet (Strict|StrictOpt, x, ex, Lvar v) when v same x -> tr_rec ex
                tr_rec(env, ex, count, next_id)
            }
            RawLambda::Llet(kind, x, ex, body) => {
                // Because of side effects, keep other lets with normalized names
                let ex_norm = tr_rec(env, ex, count, next_id)?;
                let y = Ident::new(x.name(), *next_id, IdentFlags::NONE);
                *next_id += 1;
                env.push((x.clone(), RawLambda::Lvar(y.clone())));
                let body_norm = tr_rec(env, body, count, next_id)?;
                env.pop();
                Some(RawLambda::Llet(
                    *kind,
                    y,
                    Box::new(ex_norm),
                    Box::new(body_norm),
                ))
            }
            RawLambda::Lprim(info) => {
                charge_logical_record_fields(count, &info.primitive, info.args.len())?;
                let args = tr_recs(env, &info.args, count, next_id)?;
                Some(RawLambda::Lprim(RawPrimInfo {
                    primitive: info.primitive.clone(),
                    args,
                    loc: Location::none(),
                }))
            }
            RawLambda::Lswitch(scrut, sw, loc) => {
                let scrut_norm = tr_rec(env, scrut, count, next_id)?;
                let sw_norm = tr_sw(env, sw, count, next_id)?;
                Some(RawLambda::Lswitch(
                    Box::new(scrut_norm),
                    sw_norm,
                    loc.clone(),
                ))
            }
            RawLambda::LstringSwitch(scrut, cases, default) => {
                let scrut_norm = tr_rec(env, scrut, count, next_id)?;
                let mut norm_cases = Vec::new();
                for (s, act) in cases {
                    norm_cases.push((s.clone(), tr_rec(env, act, count, next_id)?));
                }
                let norm_default = tr_opt(env, default.as_deref(), count, next_id)?;
                Some(RawLambda::LstringSwitch(
                    Box::new(scrut_norm),
                    norm_cases,
                    norm_default.map(Box::new),
                ))
            }
            RawLambda::LstaticRaise(i, es) => {
                let args = tr_recs(env, es, count, next_id)?;
                Some(RawLambda::LstaticRaise(*i, args))
            }
            RawLambda::LstaticCatch(e1, xs, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::LstaticCatch(
                    Box::new(e1_norm),
                    xs.clone(),
                    Box::new(e2_norm),
                ))
            }
            RawLambda::LtryWith(e1, x, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::LtryWith(
                    Box::new(e1_norm),
                    x.clone(),
                    Box::new(e2_norm),
                ))
            }
            RawLambda::LifThenElse(cond, ifso, ifnot) => {
                let cond_norm = tr_rec(env, cond, count, next_id)?;
                let ifso_norm = tr_rec(env, ifso, count, next_id)?;
                let ifnot_norm = tr_rec(env, ifnot, count, next_id)?;
                Some(RawLambda::LifThenElse(
                    Box::new(cond_norm),
                    Box::new(ifso_norm),
                    Box::new(ifnot_norm),
                ))
            }
            RawLambda::Lsequence(e1, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::Lsequence(Box::new(e1_norm), Box::new(e2_norm)))
            }
            RawLambda::Lassign(x, e) => {
                let e_norm = tr_rec(env, e, count, next_id)?;
                Some(RawLambda::Lassign(x.clone(), Box::new(e_norm)))
            }
            RawLambda::Lsend(m, e1, _loc) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                Some(RawLambda::Lsend(
                    m.clone(),
                    Box::new(e1_norm),
                    Location::none(),
                ))
            }
            // OCaml `Lambda.make_key` after #8348:
            // `Lbreak -> Lbreak | Lcontinue -> Lcontinue`.
            RawLambda::Lbreak => Some(RawLambda::Lbreak),
            RawLambda::Lcontinue => Some(RawLambda::Lcontinue),
            // Functions, letrec, loops are not simple
            RawLambda::Lletrec(..)
            | RawLambda::Lfunction(..)
            | RawLambda::Lfor(..)
            | RawLambda::Lfor_of(..)
            | RawLambda::Lfor_await_of(..)
            | RawLambda::Lwhile(..) => None,
        }
    }

    fn tr_recs(
        env: &mut KeyEnv,
        es: &[RawLambda],
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<Vec<RawLambda>> {
        es.iter().map(|e| tr_rec(env, e, count, next_id)).collect()
    }

    fn tr_sw(
        env: &mut KeyEnv,
        sw: &RawLambdaSwitch,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<RawLambdaSwitch> {
        let mut consts = Vec::new();
        for (tag, act) in &sw.sw_consts {
            consts.push((tag.clone(), tr_rec(env, act, count, next_id)?));
        }
        let mut blocks = Vec::new();
        for (tag, act) in &sw.sw_blocks {
            blocks.push((tag.clone(), tr_rec(env, act, count, next_id)?));
        }
        let fail = tr_opt(env, sw.sw_failaction.as_deref(), count, next_id)?;
        Some(RawLambdaSwitch {
            sw_numconsts: sw.sw_numconsts,
            sw_consts_full: sw.sw_consts_full,
            sw_consts: consts,
            sw_numblocks: sw.sw_numblocks,
            sw_blocks_full: sw.sw_blocks_full,
            sw_blocks: blocks,
            sw_failaction: fail.map(Box::new),
            sw_dispatch: sw.sw_dispatch.clone(),
        })
    }

    fn tr_opt(
        env: &mut KeyEnv,
        e: Option<&RawLambda>,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<Option<RawLambda>> {
        match e {
            None => Some(None),
            Some(e) => Some(Some(tr_rec(env, e, count, next_id)?)),
        }
    }

    let mut next_id = 0i32;
    // OCaml's `Lambda.make_key` extends a tiny identifier environment with
    // `Ident.add` while capped by `max_raw = 32`
    // (`compiler/ml/lambda.ml:432-466`). Use a stack of bindings here instead
    // of cloning a hash table for every normalized `let`.
    tr_rec(&mut Vec::new(), e, &mut count, &mut next_id)
}

/// Convert a RawLambda to a string key for comparison purposes.
/// Returns None if the lambda cannot be normalized.
fn make_key_string(e: &RawLambda) -> Option<String> {
    let mut writer = MakeKeyWriter::new();
    let mut out = String::with_capacity(128);
    writer.write_raw(e, &mut out)?;
    Some(out)
}

/// Compute the same structural key as `Lambda.make_key` directly over owned
/// match code, without materializing shared terminal leaves.
fn make_key_string_action(action: &MatchAction) -> Option<String> {
    let mut writer = MakeKeyWriter::new();
    let mut out = String::with_capacity(128);
    writer.write_action(action, &mut out)?;
    Some(out)
}

fn make_key_string_code(code: &MatchCode) -> Option<String> {
    let mut writer = MakeKeyWriter::new();
    let mut out = String::with_capacity(128);
    writer.write_code(code, &mut out)?;
    Some(out)
}

enum KeyBody<'a> {
    Raw(&'a RawLambda),
    Action(&'a MatchAction),
    Code(&'a MatchCode),
}

struct MakeKeyWriter {
    count: i32,
    next_id: i32,
    env: Vec<(Ident, String)>,
}

impl MakeKeyWriter {
    fn new() -> Self {
        Self {
            count: 0,
            next_id: 0,
            env: Vec::new(),
        }
    }

    fn write_raw(&mut self, e: &RawLambda, out: &mut String) -> Option<()> {
        self.count += 1;
        if self.count > MAX_RAW {
            return None;
        }
        self.write_raw_after_count(e, out)
    }

    fn write_action(&mut self, action: &MatchAction, out: &mut String) -> Option<()> {
        self.count += 1;
        if self.count > MAX_RAW {
            return None;
        }
        self.write_action_after_count(action, out)
    }

    fn write_action_after_count(&mut self, action: &MatchAction, out: &mut String) -> Option<()> {
        match &action.0.kind {
            MatchActionKind::Raw(raw) => self.write_raw_after_count(raw, out),
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => self.write_let(*kind, id, arg, KeyBody::Action(action), out),
        }
    }

    fn write_code(&mut self, code: &MatchCode, out: &mut String) -> Option<()> {
        self.count += 1;
        if self.count > MAX_RAW {
            return None;
        }
        match code {
            MatchCode::Action(action) => self.write_action_after_count(action, out),
            MatchCode::If {
                condition,
                ifso,
                ifnot,
            } => {
                out.push_str("LifThenElse(");
                self.write_raw(condition, out)?;
                out.push(',');
                self.write_code(ifso, out)?;
                out.push(',');
                self.write_code(ifnot, out)?;
                out.push(')');
                Some(())
            }
            MatchCode::StaticCatch {
                body,
                exit,
                handler,
            } => {
                out.push_str("LstaticCatch(");
                self.write_code(body, out)?;
                write!(out, ",({},[", exit.0).ok()?;
                for (index, var) in exit.1.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    write_ident_key(out, var);
                }
                out.push_str("]),");
                self.write_code(handler, out)?;
                out.push(')');
                Some(())
            }
            MatchCode::Bind {
                kind,
                id,
                arg,
                body,
            } => self.write_let(*kind, id, arg, KeyBody::Code(body), out),
        }
    }

    fn write_body(&mut self, body: KeyBody<'_>, out: &mut String) -> Option<()> {
        match body {
            KeyBody::Raw(raw) => self.write_raw(raw, out),
            KeyBody::Action(action) => self.write_action(action, out),
            KeyBody::Code(code) => self.write_code(code, out),
        }
    }

    fn write_raw_after_count(&mut self, e: &RawLambda, out: &mut String) -> Option<()> {
        match e {
            RawLambda::Lvar(id) => {
                if let Some((_, replacement)) = self.env.iter().rev().find(|(key, _)| key.same(id))
                {
                    out.push_str(replacement);
                } else {
                    out.push_str("Lvar(");
                    write_ident_key(out, id);
                    out.push(')');
                }
                Some(())
            }
            RawLambda::Lconst(crate::lambda::Constant::String { .. }) => None,
            RawLambda::Lconst(c) => {
                write!(out, "Lconst({c:?})").ok()?;
                Some(())
            }
            RawLambda::LglobalModule(id, dynamic_import) => {
                out.push_str("LglobalModule(");
                write_ident_key(out, id);
                write!(out, ",{dynamic_import})").ok()?;
                Some(())
            }
            RawLambda::Lapply(ap) => {
                out.push_str("Lapply(");
                self.write_raw(&ap.ap_func, out)?;
                out.push_str(",[");
                self.write_raw_list(&ap.ap_args, out)?;
                write!(
                    out,
                    "],{:?},{:?},{})",
                    ap.ap_info.inlined, ap.ap_info.status, ap.ap_transformed_jsx
                )
                .ok()?;
                Some(())
            }
            RawLambda::Llet(kind, x, ex, body) => {
                self.write_let(*kind, x, ex, KeyBody::Raw(body), out)
            }
            RawLambda::Lprim(info) => {
                charge_logical_record_fields(&mut self.count, &info.primitive, info.args.len())?;
                write!(out, "Lprim({:?},[", info.primitive).ok()?;
                self.write_raw_list(&info.args, out)?;
                out.push_str("])");
                Some(())
            }
            RawLambda::Lswitch(scrut, sw, loc) => {
                out.push_str("Lswitch(");
                self.write_raw(scrut, out)?;
                write!(
                    out,
                    ",numc={},fullc={},consts=[",
                    sw.sw_numconsts, sw.sw_consts_full
                )
                .ok()?;
                for (idx, (tag, act)) in sw.sw_consts.iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write!(out, "{tag}:").ok()?;
                    self.write_raw(act, out)?;
                }
                write!(
                    out,
                    "],numb={},fullb={},blocks=[",
                    sw.sw_numblocks, sw.sw_blocks_full
                )
                .ok()?;
                for (idx, (tag, act)) in sw.sw_blocks.iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write!(out, "{tag}:").ok()?;
                    self.write_raw(act, out)?;
                }
                out.push_str("],fail=");
                self.write_raw_opt(sw.sw_failaction.as_deref(), out)?;
                write!(out, ",names={:?},loc={loc:?})", sw.sw_dispatch).ok()?;
                Some(())
            }
            RawLambda::LstringSwitch(scrut, cases, default) => {
                out.push_str("LstringSwitch(");
                self.write_raw(scrut, out)?;
                out.push_str(",[");
                for (idx, (label, act)) in cases.iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write!(out, "{label:?}:").ok()?;
                    self.write_raw(act, out)?;
                }
                out.push_str("],");
                self.write_raw_opt(default.as_deref(), out)?;
                out.push(')');
                Some(())
            }
            RawLambda::LstaticRaise(i, args) => {
                write!(out, "LstaticRaise({i},[").ok()?;
                self.write_raw_list(args, out)?;
                out.push_str("])");
                Some(())
            }
            RawLambda::LstaticCatch(e1, (i, vars), e2) => {
                write!(out, "LstaticCatch(").ok()?;
                self.write_raw(e1, out)?;
                write!(out, ",({i},[").ok()?;
                for (idx, var) in vars.iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write_ident_key(out, var);
                }
                out.push_str("]),");
                self.write_raw(e2, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::LtryWith(e1, x, e2) => {
                out.push_str("LtryWith(");
                self.write_raw(e1, out)?;
                out.push(',');
                write_ident_key(out, x);
                out.push(',');
                self.write_raw(e2, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::LifThenElse(cond, ifso, ifnot) => {
                out.push_str("LifThenElse(");
                self.write_raw(cond, out)?;
                out.push(',');
                self.write_raw(ifso, out)?;
                out.push(',');
                self.write_raw(ifnot, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::Lsequence(e1, e2) => {
                out.push_str("Lsequence(");
                self.write_raw(e1, out)?;
                out.push(',');
                self.write_raw(e2, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::Lassign(x, e) => {
                out.push_str("Lassign(");
                write_ident_key(out, x);
                out.push(',');
                self.write_raw(e, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::Lsend(m, e1, _loc) => {
                write!(out, "Lsend({m:?},").ok()?;
                self.write_raw(e1, out)?;
                out.push(')');
                Some(())
            }
            RawLambda::Lbreak => {
                out.push_str("Lbreak");
                Some(())
            }
            RawLambda::Lcontinue => {
                out.push_str("Lcontinue");
                Some(())
            }
            RawLambda::Lletrec(..)
            | RawLambda::Lfunction(..)
            | RawLambda::Lfor(..)
            | RawLambda::Lfor_of(..)
            | RawLambda::Lfor_await_of(..)
            | RawLambda::Lwhile(..) => None,
        }
    }

    fn write_let(
        &mut self,
        kind: LetKind,
        x: &Ident,
        ex: &RawLambda,
        body: KeyBody<'_>,
        out: &mut String,
    ) -> Option<()> {
        if kind == LetKind::Alias {
            let ex_key = self.raw_to_string(ex)?;
            self.env.push((x.clone(), ex_key));
            let result = self.write_body(body, out);
            self.env.pop();
            return result;
        }

        if matches!(kind, LetKind::Strict | LetKind::StrictOpt) && same_var_body(&body, x) {
            return self.write_raw(ex, out);
        }

        out.push_str("Llet(");
        write!(out, "{kind:?},").ok()?;
        let synthetic_stamp = self.next_id;
        self.next_id += 1;
        write_synthetic_ident_key(out, x.name(), synthetic_stamp);
        out.push(',');
        self.write_raw(ex, out)?;
        out.push(',');
        let mut replacement = String::with_capacity(x.name().len() + 16);
        replacement.push_str("Lvar(");
        write_synthetic_ident_key(&mut replacement, x.name(), synthetic_stamp);
        replacement.push(')');
        self.env.push((x.clone(), replacement));
        let result = self.write_body(body, out);
        self.env.pop();
        result?;
        out.push(')');
        Some(())
    }

    fn raw_to_string(&mut self, e: &RawLambda) -> Option<String> {
        let mut out = String::with_capacity(64);
        self.write_raw(e, &mut out)?;
        Some(out)
    }

    fn write_raw_list(&mut self, items: &[RawLambda], out: &mut String) -> Option<()> {
        for (idx, item) in items.iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            self.write_raw(item, out)?;
        }
        Some(())
    }

    fn write_raw_opt(&mut self, item: Option<&RawLambda>, out: &mut String) -> Option<()> {
        match item {
            None => out.push_str("None"),
            Some(item) => {
                out.push_str("Some(");
                self.write_raw(item, out)?;
                out.push(')');
            }
        }
        Some(())
    }
}

fn same_var_body(body: &KeyBody<'_>, id: &Ident) -> bool {
    match body {
        KeyBody::Raw(RawLambda::Lvar(v)) => v.same(id),
        KeyBody::Action(action) => {
            matches!(&action.0.kind, MatchActionKind::Raw(RawLambda::Lvar(v)) if v.same(id))
        }
        KeyBody::Code(MatchCode::Action(action)) => {
            matches!(&action.0.kind, MatchActionKind::Raw(RawLambda::Lvar(v)) if v.same(id))
        }
        _ => false,
    }
}

fn write_ident_key(out: &mut String, id: &Ident) {
    match id.stamp() {
        0 => {
            out.push_str(id.name());
            out.push('!');
        }
        -1 => {
            out.push_str(id.name());
            out.push('#');
        }
        stamp => write_synthetic_ident_key_with_global(out, id.name(), stamp, id.is_global()),
    }
}

fn write_synthetic_ident_key(out: &mut String, name: &str, stamp: i32) {
    write_synthetic_ident_key_with_global(out, name, stamp, false);
}

fn write_synthetic_ident_key_with_global(
    out: &mut String,
    name: &str,
    stamp: i32,
    is_global: bool,
) {
    if stamp == 0 {
        out.push_str(name);
        out.push('!');
    } else if stamp == -1 {
        out.push_str(name);
        out.push('#');
    } else {
        out.push_str(name);
        write!(out, "/{stamp}").expect("writing to String cannot fail");
        if is_global {
            out.push('g');
        }
    }
}

// ============================================================================
// StoreExp — Action deduplication using make_key
// ============================================================================
// Ported from OCaml's Switch.Store, specialized for lambda/RawLambda.

/// Whether an action should be shared or is a singleton.
#[derive(Debug, Clone)]
pub enum SharedAction {
    Shared(RawLambda),
    Single(RawLambda),
}

/// Action store for deduplicating lambda actions.
/// Equivalent to OCaml's `StoreExp` (Switch.Store specialized for lambda).
///
/// Uses string keys (from `make_key` normalization) for comparison,
/// since RawLambda doesn't implement PartialEq/Ord.
pub struct StoreExp {
    /// Map from normalized key string -> (shared, index).
    ///
    /// OCaml uses `AMap` for lookup in `Switch.Store.store`
    /// (`compiler/ml/switch.ml:55-65`) and iterates it only to mark shared
    /// action slots (`compiler/ml/switch.ml:67-76`). That iteration order does
    /// not feed the generated lambda, so Rust can keep the same semantics with
    /// a hash map and avoid tree rotations/comparisons in the hot store path.
    map: HashMap<String, (bool, usize)>,
    /// Next index to assign.
    next: usize,
    /// Accumulated actions in reverse order: (must_share, action).
    acts: Vec<(bool, RawLambda)>,
}

impl StoreExp {
    /// Create a new empty store.
    /// Equivalent to OCaml's `mk_store`.
    pub fn mk_store() -> Self {
        StoreExp {
            map: HashMap::new(),
            next: 0,
            acts: Vec::new(),
        }
    }

    /// Internal: add an action unconditionally (no dedup).
    fn add(&mut self, must_share: bool, act: RawLambda) -> usize {
        let i = self.next;
        self.acts.push((must_share, act));
        self.next = i + 1;
        i
    }

    /// Internal: store an action, deduplicating if possible.
    fn store(&mut self, must_share: bool, act: RawLambda) -> usize {
        match make_key_string(&act) {
            Some(key) => {
                if let Some(&(shared, i)) = self.map.get(&key) {
                    if !shared {
                        self.map.insert(key, (true, i));
                    }
                    i
                } else {
                    let i = self.add(must_share, act);
                    self.map.insert(key, (must_share, i));
                    i
                }
            }
            None => self.add(must_share, act),
        }
    }

    /// Store an action (not forced shared).
    /// Equivalent to OCaml's `act_store`.
    pub fn act_store(&mut self, act: RawLambda) -> usize {
        self.store(false, act)
    }

    /// Store an action that must be shared.
    /// Equivalent to OCaml's `act_store_shared`.
    pub fn act_store_shared(&mut self, act: RawLambda) -> usize {
        self.store(true, act)
    }

    /// Get the actions array with sharing info.
    /// Actions that were stored multiple times or marked as must-share
    /// are wrapped in `Shared`; others are `Single`.
    /// Equivalent to OCaml's `act_get_shared`.
    pub fn act_get_shared(self) -> Vec<SharedAction> {
        // OCaml's store closes over the action list and returns those actions
        // directly when `act_get_shared` is called (compiler/ml/switch.ml:55-67).
        // Rust callers consume the store at the same point, so move the raw
        // lambda actions into the result instead of recursively cloning them.
        let StoreExp { map, acts, .. } = self;
        let mut share_flags: Vec<bool> = acts.iter().map(|(shared, _)| *shared).collect();

        // Mark any action that was found in the map as shared (even if not must_share)
        for (_, (shared, i)) in map {
            if shared {
                if let Some(flag) = share_flags.get_mut(i) {
                    *flag = true;
                }
            }
        }

        acts.into_iter()
            .zip(share_flags)
            .map(|((_, act), shared)| {
                if shared {
                    SharedAction::Shared(act)
                } else {
                    SharedAction::Single(act)
                }
            })
            .collect()
    }
}

enum StoredMatchCode {
    Shared(MatchCode),
    Single(MatchCode),
}

/// Owned action store at OCaml's local sharing boundaries.
struct MatchCodeStore {
    map: HashMap<String, (bool, usize)>,
    acts: Vec<(bool, MatchCode)>,
}

impl MatchCodeStore {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            acts: Vec::new(),
        }
    }

    fn store(&mut self, must_share: bool, code: MatchCode) -> usize {
        if let Some(key) = code.normalized_key() {
            if let Some(&(shared, index)) = self.map.get(&key) {
                if !shared {
                    self.map.insert(key, (true, index));
                }
                return index;
            }
            let index = self.acts.len();
            self.acts.push((must_share, code));
            self.map.insert(key, (must_share, index));
            index
        } else {
            let index = self.acts.len();
            self.acts.push((must_share, code));
            index
        }
    }

    fn get(self) -> Vec<StoredMatchCode> {
        let Self { map, acts } = self;
        let mut flags: Vec<_> = acts.iter().map(|(flag, _)| *flag).collect();
        for (_, (shared, index)) in map {
            if shared {
                flags[index] = true;
            }
        }
        acts.into_iter()
            .zip(flags)
            .map(|((_, code), shared)| {
                if shared {
                    StoredMatchCode::Shared(code)
                } else {
                    StoredMatchCode::Single(code)
                }
            })
            .collect()
    }
}

#[track_caller]
fn materialize_resolved_action(
    resolved_acts: &mut [Option<RawLambda>],
    use_counts: &[usize],
    idx: usize,
) -> RawLambda {
    // OCaml's switch store shares immutable action pointers
    // (`compiler/ml/switch.ml:55-76`, used from
    // `compiler/ml/matching.ml:1609-1659,1761-1833`). Once Rust has decided
    // which actions are truly shared, single-use actions can be moved into the
    // output switch instead of recursively cloning their raw-lambda bodies.
    if use_counts[idx] == 1 {
        resolved_acts[idx]
            .take()
            .expect("single-use resolved action should still be available")
    } else {
        let action = resolved_acts[idx]
            .as_ref()
            .expect("shared resolved action should still be available");
        if crate::perf_counters::enabled() {
            let (nodes, bytes) = raw_lambda_clone_footprint(action);
            let started = std::time::Instant::now();
            let cloned = action.clone();
            crate::perf_counters::record_match_action_clone(
                std::panic::Location::caller(),
                nodes,
                bytes,
                started.elapsed().as_nanos().min(u64::MAX as u128) as u64,
                use_counts[idx],
            );
            cloned
        } else {
            action.clone()
        }
    }
}

// ============================================================================
// make_exit — Lstaticraise(i, [])
// ============================================================================

/// Create a static raise with no arguments.
/// Equivalent to OCaml's `make_exit`.
pub fn make_exit(i: i32) -> RawLambda {
    RawLambda::LstaticRaise(i, Vec::new())
}

// ============================================================================
// make_catch — Introduce catch if worth it
// ============================================================================

/// Introduce a catch around `k(d)`, if `d` is not already a simple exit.
/// If `d` is already `Lstaticraise(_, [])`, just returns `k(d)`.
/// Otherwise, allocates a new exit number, returns `Lstaticcatch(k(exit(e)), (e,[]), d)`.
///
/// Equivalent to OCaml's `make_catch`.
pub fn make_catch(
    d: RawLambda,
    next_raise_count: &mut i32,
    k: impl FnOnce(RawLambda) -> RawLambda,
) -> RawLambda {
    match &d {
        RawLambda::LstaticRaise(_, args) if args.is_empty() => k(d),
        _ => {
            let e = bump_raise_count(next_raise_count, "matching::make_catch");
            RawLambda::LstaticCatch(Box::new(k(make_exit(e))), (e, Vec::new()), Box::new(d))
        }
    }
}

// ============================================================================
// as_simple_exit — Check if lambda is just an exit
// ============================================================================

/// Check if a lambda is just a static raise (possibly wrapped in alias lets).
/// Returns the exit number if so.
///
/// Equivalent to OCaml's `as_simple_exit`.
pub fn as_simple_exit(lam: &RawLambda) -> Option<i32> {
    match lam {
        RawLambda::LstaticRaise(i, args) if args.is_empty() => Some(*i),
        RawLambda::Llet(LetKind::Alias, _, _, e) => as_simple_exit(e),
        _ => None,
    }
}

// ============================================================================
// make_catch_delayed — Delayed catch with next_raise_count
// ============================================================================

/// Create a delayed catch: returns (exit_number, wrapper_fn).
/// If the handler is already a simple exit, the wrapper is the identity.
/// Otherwise, allocates a new exit number and returns a wrapper that
/// wraps the body in `Lstaticcatch(body, (i,[]), handler)` (or just returns
/// `handler` if body is `Lstaticraise(i, _)`).
///
/// Equivalent to OCaml's `make_catch_delayed`.
pub fn make_catch_delayed(
    handler: RawLambda,
    next_raise_count: &mut i32,
) -> (i32, Box<dyn FnOnce(RawLambda) -> RawLambda>) {
    match as_simple_exit(&handler) {
        Some(i) => (i, Box::new(|act| act)),
        None => {
            let i = bump_raise_count(next_raise_count, "matching::make_catch_delayed");
            (
                i,
                Box::new(move |body: RawLambda| match &body {
                    RawLambda::LstaticRaise(j, _) if *j == i => handler,
                    _ => {
                        RawLambda::LstaticCatch(Box::new(body), (i, Vec::new()), Box::new(handler))
                    }
                }),
            )
        }
    }
}

// ============================================================================
// raw_static_raise — Borrow the raw action only for the static-raise test
// ============================================================================

enum StaticRaiseArgs<'a> {
    Borrowed(&'a [RawLambda]),
    Owned(Vec<RawLambda>),
}

impl StaticRaiseArgs<'_> {
    fn iter(&self) -> std::slice::Iter<'_, RawLambda> {
        match self {
            StaticRaiseArgs::Borrowed(args) => args.iter(),
            StaticRaiseArgs::Owned(args) => args.iter(),
        }
    }
}

/// Return the raw action's static-raise shape without cloning the fallback.
fn raw_static_raise(l: &RawLambda) -> Option<(i32, StaticRaiseArgs<'_>)> {
    match make_key(l) {
        Some(RawLambda::LstaticRaise(i, args)) => Some((i, StaticRaiseArgs::Owned(args))),
        Some(_) => None,
        None => match l {
            // OCaml `compiler/ml/matching.ml:479-482` returns the original
            // lambda when `make_key` fails. Borrow that original static raise
            // instead of cloning the whole raw lambda tree.
            RawLambda::LstaticRaise(i, args) => Some((*i, StaticRaiseArgs::Borrowed(args))),
            _ => None,
        },
    }
}

// ============================================================================
// tr_raw — Transform raw action with catch (raises on failure)
// ============================================================================

/// Normalize a lambda action. Returns None if normalization fails
/// (equivalent to OCaml's `tr_raw` which raises Exit on failure).
fn tr_raw(act: &RawLambda) -> Option<RawLambda> {
    make_key(act)
}

/// Convert a normalized RawLambda to a structural key for comparison.
///
/// OCaml `same_actions` compares `Lambda.make_key` results structurally
/// (`compiler/ml/matching.ml:489-500`). Do not use the raw lambda pretty-printer
/// here: `Printlambda` intentionally renders some constants ambiguously in
/// `-drawlambda` output, so it is not a safe equality key.
fn lambda_to_string(lam: &RawLambda) -> String {
    format!("{lam:?}")
}

// ============================================================================
// same_actions — Check if all actions in a list are the same
// ============================================================================

/// Check if all actions in a case list are the same lambda.
/// Returns `Some(act)` with the first action if all are equal,
/// `None` otherwise.
///
/// Equivalent to OCaml's `same_actions`.
pub fn same_actions(cases: &[Clause]) -> Option<RawLambda> {
    match cases {
        [] => None,
        [(_, act)] => Some(act.to_raw()),
        [(_, act0), rem @ ..] => {
            let raw_act0_str = act0.normalized_key()?;
            for (_, act) in rem {
                if act.normalized_key()? != raw_act0_str {
                    return None;
                }
            }
            Some(act0.to_raw())
        }
    }
}

// ============================================================================
// up_ok_action — Check if swapping two actions is safe
// ============================================================================

/// Check if two actions are equivalent (safe to swap).
/// Returns true if both can be normalized and their normalized forms are equal.
///
/// Equivalent to OCaml's `up_ok_action`.
fn up_ok_action(act1: &MatchAction, act2: &MatchAction) -> bool {
    match (act1.normalized_key(), act2.normalized_key()) {
        (Some(raw1), Some(raw2)) => raw1 == raw2,
        _ => false,
    }
}

// ============================================================================
// up_ok — Check if swapping two clauses is safe
// ============================================================================

/// Check if a clause `(ps, act_p)` can be moved past all clauses in `l`.
/// Safe to swap if either the actions are equivalent or the patterns
/// are incompatible.
///
/// Equivalent to OCaml's `up_ok`.
fn up_ok(ps: &[Pattern], act_p: &MatchAction, l: &[Clause]) -> bool {
    up_ok_iter(ps, act_p, l.iter())
}

fn up_ok_iter<'a>(
    ps: &[Pattern],
    act_p: &MatchAction,
    mut clauses: impl Iterator<Item = &'a Clause>,
) -> bool {
    clauses.all(|(qs, act_q)| up_ok_action(act_p, act_q) || !may_compats(ps, qs))
}

// ============================================================================
// simplify_or — Simplify or-patterns
// ============================================================================

/// Exception used internally by simplify_or to propagate variable patterns up.
enum VarPat {
    Var(Pattern),
}

/// Simplify an or-pattern:
/// - `_|p` becomes `_` (propagated as Var)
/// - Records are expanded to all fields
/// - Aliases are preserved around or-patterns
///
/// Equivalent to OCaml's `simplify_or`.
fn simplify_or(ctx_ref: Option<&TypeContext>, p: &Pattern) -> Pattern {
    fn simpl_rec(ctx_ref: Option<&TypeContext>, p: &Pattern) -> Result<Pattern, VarPat> {
        match &p.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => Err(VarPat::Var(p.clone())),
            PatternDesc::Tpat_alias(q, id, s) => match simpl_rec(ctx_ref, q) {
                Ok(q_simplified) => Ok(Pattern {
                    pat_desc: PatternDesc::Tpat_alias(
                        Box::new(q_simplified),
                        id.clone(),
                        s.clone(),
                    ),
                    ..p.clone()
                }),
                Err(VarPat::Var(q_var)) => Err(VarPat::Var(Pattern {
                    pat_desc: PatternDesc::Tpat_alias(Box::new(q_var), id.clone(), s.clone()),
                    ..p.clone()
                })),
            },
            PatternDesc::Tpat_or(p1, p2, o) => {
                let q1 = simpl_rec(ctx_ref, p1)?; // propagates Var if p1 is variable
                match simpl_rec(ctx_ref, p2) {
                    Ok(q2) => Ok(Pattern {
                        pat_desc: PatternDesc::Tpat_or(Box::new(q1), Box::new(q2), o.clone()),
                        ..p.clone()
                    }),
                    Err(VarPat::Var(q2)) => Err(VarPat::Var(Pattern {
                        pat_desc: PatternDesc::Tpat_or(Box::new(q1), Box::new(q2), o.clone()),
                        ..p.clone()
                    })),
                }
            }
            PatternDesc::Tpat_record(lbls, closed, rest) => {
                let all_lbls = all_record_args(ctx_ref, p.pat_type, p.pat_env, lbls);
                Ok(Pattern {
                    pat_desc: PatternDesc::Tpat_record(all_lbls, *closed, rest.clone()),
                    ..p.clone()
                })
            }
            _ => Ok(p.clone()),
        }
    }

    match simpl_rec(ctx_ref, p) {
        Ok(p) => p,
        Err(VarPat::Var(p)) => p,
    }
}

// ============================================================================
// simplify_cases — Simplify all cases (swap optimization)
// ============================================================================

/// Bind a variable to an argument in an action.
/// Equivalent to OCaml's `Lambda.bind Alias id arg action`.
fn bind(kind: LetKind, id: &Ident, arg: &RawLambda, action: RawLambda) -> RawLambda {
    match arg {
        RawLambda::Lvar(v) if v.same(id) => action,
        _ => RawLambda::Llet(kind, id.clone(), Box::new(arg.clone()), Box::new(action)),
    }
}

/// Simplify the first column of a match:
/// - Variables are replaced with omega and bound in the action
/// - Aliases are removed and replaced by bindings in actions
/// - Records are expanded to all fields
/// - Or-patterns are simplified (but not removed)
///
/// Equivalent to OCaml's `simplify_cases`.
pub fn simplify_cases(
    ctx_ref: Option<&TypeContext>,
    args: &[(RawLambda, LetKind)],
    cls: Vec<Clause>,
) -> Vec<Clause> {
    assert!(!args.is_empty(), "simplify_cases: empty args");

    let (ref arg, _) = args[0];

    fn simplify(ctx_ref: Option<&TypeContext>, arg: &RawLambda, cls: Vec<Clause>) -> Vec<Clause> {
        let mut pending: VecDeque<Clause> = cls.into();
        let mut result = Vec::with_capacity(pending.len());
        while let Some((pats, action)) = pending.pop_front() {
            assert!(!pats.is_empty(), "simplify_cases: empty pattern row");

            let pat = &pats[0];
            let patl = &pats[1..];

            match &pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => {
                    let new_action = action.bind(LetKind::Alias, id.clone(), arg.clone());
                    let mut row = vec![omega()];
                    row.extend(patl.iter().cloned());
                    result.push((row, new_action));
                }
                PatternDesc::Tpat_any => {
                    result.push((pats, action));
                }
                PatternDesc::Tpat_alias(p, id, _) => {
                    let new_action = action.bind(LetKind::Alias, id.clone(), arg.clone());
                    let mut new_pats = vec![(**p).clone()];
                    new_pats.extend(patl.iter().cloned());
                    // OCaml `compiler/ml/matching.ml:565-566` immediately
                    // reprocesses the peeled alias row by recursing on
                    // `(p :: patl, bind Alias id arg action) :: rem`. A deque
                    // keeps that same order without shifting the whole Rust Vec.
                    pending.push_front((new_pats, new_action));
                }
                PatternDesc::Tpat_record(lbls, _, rest) if lbls.is_empty() => {
                    let action = match rest {
                        Some(rest) => action.bind(
                            LetKind::Strict,
                            rest.rest_ident.clone(),
                            RawLambda::prim(
                                Primitive::PrecordRest(rest.excluded_runtime_labels.clone()),
                                vec![arg.clone()],
                                Location::none(),
                            ),
                        ),
                        None => action,
                    };
                    let mut row = vec![omega()];
                    row.extend(patl.iter().cloned());
                    result.push((row, action));
                }
                PatternDesc::Tpat_record(lbls, closed, rest) => {
                    let action = match rest {
                        Some(rest) => action.bind(
                            LetKind::Strict,
                            rest.rest_ident.clone(),
                            RawLambda::prim(
                                Primitive::PrecordRest(rest.excluded_runtime_labels.clone()),
                                vec![arg.clone()],
                                Location::none(),
                            ),
                        ),
                        None => action,
                    };
                    let all_lbls = all_record_args(ctx_ref, pat.pat_type, pat.pat_env, lbls);
                    let full_pat = Pattern {
                        pat_desc: PatternDesc::Tpat_record(all_lbls, *closed, None),
                        ..pat.clone()
                    };
                    let mut row = vec![full_pat];
                    row.extend(patl.iter().cloned());
                    result.push((row, action));
                }
                PatternDesc::Tpat_or(..) => {
                    let pat_simple = simplify_or(ctx_ref, pat);
                    match &pat_simple.pat_desc {
                        PatternDesc::Tpat_or(..) => {
                            let mut row = vec![pat_simple];
                            row.extend(patl.iter().cloned());
                            result.push((row, action));
                        }
                        _ => {
                            // OCaml `compiler/ml/matching.ml:577-580` also
                            // reprocesses an or-pattern that simplified away.
                            let mut new_pats = vec![pat_simple];
                            new_pats.extend(patl.iter().cloned());
                            pending.push_front((new_pats, action));
                        }
                    }
                }
                _ => {
                    result.push((pats, action));
                }
            }
        }
        result
    }

    simplify(ctx_ref, arg, cls)
}

// ============================================================================
// what_is_cases — Determine what kind of patterns are in cases
// ============================================================================

/// Determine what kind of pattern the first non-wildcard case has.
/// Returns the first non-wildcard pattern, or omega if all are wildcards.
///
/// Equivalent to OCaml's `what_is_cases`.
pub fn what_is_cases(cases: &[Clause]) -> Pattern {
    match cases.split_first() {
        None => omega(),
        Some(((pats, _), rem)) => {
            assert!(!pats.is_empty(), "what_is_cases: empty pattern row");
            match &pats[0].pat_desc {
                PatternDesc::Tpat_any => what_is_cases(rem),
                PatternDesc::Tpat_var(..)
                | PatternDesc::Tpat_or(..)
                | PatternDesc::Tpat_alias(..) => {
                    panic!("what_is_cases: applies to simplified matchings only")
                }
                _ => pats[0].clone(),
            }
        }
    }
}

// ============================================================================
// as_matrix, cons_default, default_compat — Default environment helpers
// ============================================================================
// Ported from OCaml's matching.ml lines 588-607.

/// Convert cases to a pattern matrix (taking the minimal rows under le_pats).
/// Equivalent to OCaml's `as_matrix`.
pub fn as_matrix(cases: &[Clause]) -> Matrix {
    let rows: Vec<Vec<Pattern>> = cases.iter().map(|(ps, _)| ps.clone()).collect();
    get_mins(|a: &Vec<Pattern>, b: &Vec<Pattern>| le_pats(a, b), rows)
}

/// Prepend a matrix entry to the default environment, skipping empty matrices.
/// Equivalent to OCaml's `cons_default`.
pub fn cons_default(matrix: Matrix, raise_num: i32, default: DefaultEnv) -> DefaultEnv {
    if matrix.is_empty() {
        default
    } else {
        let mut result = vec![(matrix, raise_num)];
        result.extend(default);
        result
    }
}

/// Filter a default environment for entries compatible with pattern p.
/// For each entry (pss, i), keep only rows whose first pattern is compatible
/// with p, and drop the first column.
///
/// Equivalent to OCaml's `default_compat`.
pub fn default_compat(p: &Pattern, def: &DefaultEnv) -> DefaultEnv {
    def.iter().rev().fold(Vec::new(), |r, (pss, i)| {
        let qss: Vec<Vec<Pattern>> = pss
            .iter()
            .filter_map(|qs| match qs.split_first() {
                Some((q, rem)) if may_compat(p, q) => Some(rem.to_vec()),
                _ => None,
            })
            .collect();
        if qss.is_empty() {
            r
        } else {
            let mut result = vec![(qss, *i)];
            result.extend(r);
            result
        }
    })
}

// ============================================================================
// Layer 3: Default environments and or-patterns
// Ported from OCaml's matching.ml lines 612-657
// ============================================================================

/// Type alias for the set of identifiers (equivalent to OCaml's IdentSet).
type IdentSet = BTreeSet<Ident>;

/// Recursively extract all variables bound in a pattern.
/// Equivalent to OCaml's `extract_vars`.
pub fn extract_vars(r: IdentSet, p: &Pattern) -> IdentSet {
    match &p.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            let mut r = r;
            r.insert(id.clone());
            r
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            let mut r = r;
            r.insert(id.clone());
            extract_vars(r, p)
        }
        PatternDesc::Tpat_tuple(pats) => pats.iter().fold(r, |r, p| extract_vars(r, p)),
        PatternDesc::Tpat_record(lpats, _, rest) => {
            let mut r = r;
            if let Some(rest) = rest {
                r.insert(rest.rest_ident.clone());
            }
            lpats.iter().fold(r, |r, (_, _, p, _)| extract_vars(r, p))
        }
        PatternDesc::Tpat_construct(_, _, pats) => pats.iter().fold(r, |r, p| extract_vars(r, p)),
        PatternDesc::Tpat_array(pats) => pats.iter().fold(r, |r, p| extract_vars(r, p)),
        PatternDesc::Tpat_variant(_, Some(p), _) => extract_vars(r, p),
        PatternDesc::Tpat_or(p, _, _) => extract_vars(r, p),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => r,
    }
}

/// Boolean form of `extract_vars IdentSet.empty p |> IdentSet.is_empty`.
/// Mirrors OCaml's `extract_vars` branches (compiler/ml/matching.ml:613-624)
/// but avoids allocating an IdentSet for the hot no-variable test in
/// `insert_or_append` (compiler/ml/matching.ml:738-740).
fn pattern_binds_vars(p: &Pattern) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_alias(_, _, _) => true,
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => pats.iter().any(pattern_binds_vars),
        PatternDesc::Tpat_record(lpats, _, rest) => {
            rest.is_some() || lpats.iter().any(|(_, _, pat, _)| pattern_binds_vars(pat))
        }
        PatternDesc::Tpat_variant(_, Some(p), _) | PatternDesc::Tpat_or(p, _, _) => {
            pattern_binds_vars(p)
        }
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => false,
    }
}

/// Error raised when an or-pattern cannot be flattened because
/// an aliased variable needs a binding but no argument is available.
/// Equivalent to OCaml's `Cannot_flatten` exception.
#[derive(Debug)]
pub struct CannotFlatten;

/// Create an alpha-renaming environment mapping each id in `ids` to either
/// the match argument (if id is in aliases) or a fresh ident with the same name.
/// Raises `CannotFlatten` if an alias id has no argument.
/// Equivalent to OCaml's `mk_alpha_env`.
pub fn mk_alpha_env(
    ctx_ref: Option<&TypeContext>,
    arg: &Option<Ident>,
    aliases: &[Ident],
    ids: &IdentSet,
) -> Result<Vec<(Ident, Ident)>, CannotFlatten> {
    ids.iter()
        .map(|id| {
            let new_id = if aliases.contains(id) {
                match arg {
                    Some(v) => v.clone(),
                    None => return Err(CannotFlatten),
                }
            } else {
                ctx_ref
                    .map(|ctx_ref| ctx_ref.create_ident(id.name()))
                    .unwrap_or_else(|| Ident::create_local(id.name()))
            };
            Ok((id.clone(), new_id))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Alpha-renaming for patterns (local copy, mirrors Typedtree.alpha_pat)
// ---------------------------------------------------------------------------

/// Look up an identifier in the alpha-renaming environment.
fn alpha_pat_id<'a>(env: &'a [(Ident, Ident)], id: &Ident) -> Option<&'a Ident> {
    env.iter()
        .find_map(|(from, to)| if from.same(id) { Some(to) } else { None })
}

/// Apply an alpha-renaming environment to a pattern.
/// Equivalent to OCaml's `Typedtree.alpha_pat`.
fn alpha_pat(env: &[(Ident, Ident)], pat: &Pattern) -> Pattern {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, name) => {
            let pat_desc = alpha_pat_id(env, id)
                .map(|new_id| PatternDesc::Tpat_var(new_id.clone(), name.clone()))
                .unwrap_or(PatternDesc::Tpat_any);
            Pattern {
                pat_desc,
                ..pat.clone()
            }
        }
        PatternDesc::Tpat_alias(inner, id, name) => {
            let new_inner = alpha_pat(env, inner);
            if let Some(new_id) = alpha_pat_id(env, id) {
                Pattern {
                    pat_desc: PatternDesc::Tpat_alias(
                        Box::new(new_inner),
                        new_id.clone(),
                        name.clone(),
                    ),
                    ..pat.clone()
                }
            } else {
                new_inner
            }
        }
        PatternDesc::Tpat_tuple(items) => Pattern {
            pat_desc: PatternDesc::Tpat_tuple(
                items.iter().map(|item| alpha_pat(env, item)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_construct(lid, cstr, args) => Pattern {
            pat_desc: PatternDesc::Tpat_construct(
                lid.clone(),
                cstr.clone(),
                args.iter().map(|arg| alpha_pat(env, arg)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_variant(label, arg, row) => Pattern {
            pat_desc: PatternDesc::Tpat_variant(
                label.clone(),
                arg.as_ref().map(|arg| Box::new(alpha_pat(env, arg))),
                *row,
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_record(fields, closed, rest) => Pattern {
            pat_desc: PatternDesc::Tpat_record(
                fields
                    .iter()
                    .map(|(lid, lbl, field_pat, opt)| {
                        (lid.clone(), lbl.clone(), alpha_pat(env, field_pat), *opt)
                    })
                    .collect(),
                *closed,
                rest.as_ref().map(|rest| {
                    let mut rest = rest.clone();
                    if let Some(new_id) = alpha_pat_id(env, &rest.rest_ident) {
                        rest.rest_ident = new_id.clone();
                    }
                    rest
                }),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_array(items) => Pattern {
            pat_desc: PatternDesc::Tpat_array(
                items.iter().map(|item| alpha_pat(env, item)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_or(left, right, row) => Pattern {
            pat_desc: PatternDesc::Tpat_or(
                Box::new(alpha_pat(env, left)),
                Box::new(alpha_pat(env, right)),
                row.clone(),
            ),
            ..pat.clone()
        },
        _ => pat.clone(),
    }
}

/// Expand an or-pattern into separate cases with alpha-renamed variables.
///
/// `arg`: optional binding for alias variables
/// `patl`: surrounding pattern context
/// `mk_action`: closure that builds an action given a list of fresh idents
/// `rem`: accumulator of already-expanded cases
/// `vars`: set of variables that need alpha-renaming
/// `aliases`: accumulated alias identifiers from Tpat_alias wrappers
/// `pat`: the pattern being exploded
///
/// Equivalent to OCaml's `explode_or_pat`.
pub fn explode_or_pat<F>(
    ctx_ref: Option<&TypeContext>,
    arg: &Option<Ident>,
    patl: &[Pattern],
    mk_action: &F,
    rem: Vec<Clause>,
    vars: &IdentSet,
    aliases: &[Ident],
    pat: &Pattern,
) -> Result<Vec<Clause>, CannotFlatten>
where
    F: Fn(&[Ident]) -> RawLambda,
{
    match &pat.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            let rem = explode_or_pat(ctx_ref, arg, patl, mk_action, rem, vars, aliases, p2)?;
            explode_or_pat(ctx_ref, arg, patl, mk_action, rem, vars, aliases, p1)
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            let mut new_aliases = vec![id.clone()];
            new_aliases.extend_from_slice(aliases);
            explode_or_pat(ctx_ref, arg, patl, mk_action, rem, vars, &new_aliases, p)
        }
        PatternDesc::Tpat_var(x, _) => {
            let mut x_aliases = vec![x.clone()];
            x_aliases.extend_from_slice(aliases);
            let env = mk_alpha_env(ctx_ref, arg, &x_aliases, vars)?;
            let new_ids: Vec<Ident> = env.iter().map(|(_, id)| id.clone()).collect();
            let mut row = vec![omega()];
            row.extend_from_slice(patl);
            let mut result = vec![(row, MatchAction::new(mk_action(&new_ids)))];
            result.extend(rem);
            Ok(result)
        }
        _ => {
            let env = mk_alpha_env(ctx_ref, arg, aliases, vars)?;
            let new_ids: Vec<Ident> = env.iter().map(|(_, id)| id.clone()).collect();
            let mut row = vec![alpha_pat(&env, pat)];
            row.extend_from_slice(patl);
            let mut result = vec![(row, MatchAction::new(mk_action(&new_ids)))];
            result.extend(rem);
            Ok(result)
        }
    }
}

/// Compute the free variables of a pattern matching's actions.
/// Equivalent to OCaml's `pm_free_variables`.
pub fn pm_free_variables(pm: &PatternMatching) -> IdentSet {
    // OCaml uses IdentSet.union (free_variables act) r folded right over cases.
    // We use raw_free_variables (HashSet-based) and convert to BTreeSet.
    pm.cases
        .iter()
        .rev()
        .fold(BTreeSet::new(), |mut r, (_, act)| {
            let fv = act.free_variables();
            r.extend(fv);
            r
        })
}

/// Compute free variables of a RawLambda expression.
/// Local helper equivalent to Lambda.free_variables, matching
/// the raw_free_variables in convert.rs.
fn raw_lambda_free_variables(lam: &RawLambda) -> IdentSet {
    fn collect(lam: &RawLambda, fv: &mut IdentSet) {
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
            RawLambda::LifThenElse(cond, then_br, else_br) => {
                collect(cond, fv);
                collect(then_br, fv);
                collect(else_br, fv);
            }
            RawLambda::Lsequence(first, second) => {
                collect(first, fv);
                collect(second, fv);
            }
            RawLambda::Lwhile(cond, body) => {
                collect(cond, fv);
                collect(body, fv);
            }
            RawLambda::Lfor(id, lo, hi, _, body) => {
                collect(lo, fv);
                collect(hi, fv);
                collect(body, fv);
                fv.remove(id);
            }
            RawLambda::Lfor_of(id, iterable, body)
            | RawLambda::Lfor_await_of(id, iterable, body) => {
                collect(iterable, fv);
                collect(body, fv);
                fv.remove(id);
            }
            RawLambda::Lassign(id, expr) => {
                fv.insert(id.clone());
                collect(expr, fv);
            }
            RawLambda::Lsend(_, obj, _) => {
                collect(obj, fv);
            }
            RawLambda::Lbreak | RawLambda::Lcontinue => {}
        }
    }

    let mut fv = BTreeSet::new();
    collect(lam, &mut fv);
    fv
}

// ============================================================================
// Layer 4: Grouping and splitting
// ============================================================================
// Ported from OCaml's matching.ml lines 659-1090.
// This layer implements the pattern grouping predicates, or-pattern
// operations, and the split/precompile functions that prepare pattern
// matchings for compilation.

// ============================================================================
// is_guarded — Check if an action has a guard (anticipated staticraise)
// ============================================================================
// Ported from OCaml's lambda.ml lines 603-606.

/// Check if a lambda action is guarded (contains `if ... then ... else staticraise(0, [])`).
/// Equivalent to OCaml's `Lambda.is_guarded`.
fn is_guarded(lam: &RawLambda) -> bool {
    match lam {
        RawLambda::LifThenElse(_, _, else_br) => {
            matches!(else_br.as_ref(), RawLambda::LstaticRaise(0, args) if args.is_empty())
        }
        RawLambda::Llet(_, _, _, body) => is_guarded(body),
        _ => false,
    }
}

// ============================================================================
// Group predicates (lines 659-700)
// ============================================================================

/// Extract the constructor description from a construct pattern.
/// Equivalent to OCaml's `pat_as_constr`.
fn pat_as_constr(p: &Pattern) -> &crate::types::ConstructorDescription {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr,
        _ => panic!("Matching.pat_as_constr"),
    }
}

/// Group predicate for constant patterns.
/// Equivalent to OCaml's `group_constant`.
fn group_constant(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_constant(_))
}

/// Group predicate for constructor patterns.
/// Equivalent to OCaml's `group_constructor`.
fn group_constructor(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_construct(_, _, _))
}

/// Group predicate for variant patterns.
/// Equivalent to OCaml's `group_variant`.
fn group_variant(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_variant(_, _, _))
}

/// Group predicate for variable/wildcard patterns.
/// Equivalent to OCaml's `group_var`.
fn group_var(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_any)
}

/// Group predicate for tuple patterns (including wildcard).
/// Equivalent to OCaml's `group_tuple`.
fn group_tuple(p: &Pattern) -> bool {
    matches!(
        &p.pat_desc,
        PatternDesc::Tpat_tuple(_) | PatternDesc::Tpat_any
    )
}

/// Group predicate for record patterns (including wildcard).
/// Equivalent to OCaml's `group_record`.
fn group_record(p: &Pattern) -> bool {
    matches!(
        &p.pat_desc,
        PatternDesc::Tpat_record(_, _, _) | PatternDesc::Tpat_any
    )
}

/// Group predicate for array patterns.
/// Equivalent to OCaml's `group_array`.
fn group_array(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_array(_))
}

/// Get the appropriate group predicate for a pattern.
/// Equivalent to OCaml's `get_group`.
fn get_group(p: &Pattern) -> fn(&Pattern) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_any => group_var,
        PatternDesc::Tpat_constant(_) => group_constant,
        PatternDesc::Tpat_construct(_, _, _) => group_constructor,
        PatternDesc::Tpat_tuple(_) => group_tuple,
        PatternDesc::Tpat_record(_, _, _) => group_record,
        PatternDesc::Tpat_array(_) => group_array,
        PatternDesc::Tpat_variant(_, _, _) => group_variant,
        _ => panic!("Matching.get_group"),
    }
}

/// Check if a pattern is an or-pattern.
/// Equivalent to OCaml's `is_or`.
fn is_or(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_or(_, _, _))
}

// ============================================================================
// Or-pattern operations (lines 708-773)
// ============================================================================

/// Condition (a) for appending to the Or matrix: p and q are incompatible.
/// Equivalent to OCaml's `conda`.
fn conda(p: &Pattern, q: &Pattern) -> bool {
    !may_compat(p, q)
}

/// Condition (b) for appending: action is not guarded and qs <= ps.
/// Equivalent to OCaml's `condb`.
fn condb(act: &MatchAction, ps: &[Pattern], qs: &[Pattern]) -> bool {
    !act.is_guarded() && le_pats(qs, ps)
}

/// Check if p can be appended/inserted into the or-matrix l, given
/// surrounding patterns ps.
/// Equivalent to OCaml's `or_ok`.
fn or_ok(p: &Pattern, ps: &[Pattern], l: &[Clause]) -> bool {
    or_ok_iter(p, ps, l.iter())
}

fn or_ok_iter<'a>(
    p: &Pattern,
    ps: &[Pattern],
    mut clauses: impl Iterator<Item = &'a Clause>,
) -> bool {
    clauses.all(|(row, act)| match row.split_first() {
        Some((q, qs)) if is_or(q) => conda(p, q) || condb(act, ps, qs),
        _ => true,
    })
}

/// Check if two patterns are equivalent (each le the other).
/// Equivalent to OCaml's `equiv_pat`.
fn equiv_pat(p: &Pattern, q: &Pattern) -> bool {
    le_pat(p, q) && le_pat(q, p)
}

/// Get equivalent or-patterns from the front of the list.
/// Returns (equivalent_clauses, remaining_clauses).
/// Equivalent to OCaml's `get_equiv`.
fn get_equiv(p: &Pattern, l: &[Clause]) -> (Vec<Clause>, Vec<Clause>) {
    // OCaml compiler/ml/matching.ml:727-732 recurses through the equivalent
    // prefix and conses each row while returning, preserving source order.
    // Count the prefix first so Rust clones each row once without repeated
    // front insertion.
    let prefix_len = l
        .iter()
        .take_while(|cl| match cl.0.first() {
            Some(q) => equiv_pat(p, q),
            None => false,
        })
        .count();

    if prefix_len == 0 {
        return (Vec::new(), l.to_vec());
    }

    (l[..prefix_len].to_vec(), l[prefix_len..].to_vec())
}

/// Insert or append a pattern in the Or matrix.
/// Returns (updated_ors, updated_no).
/// Equivalent to OCaml's `insert_or_append`.
fn insert_or_append(
    p: &Pattern,
    ps: &[Pattern],
    act: &MatchAction,
    mut ors: VecDeque<Clause>,
    mut no: VecDeque<Clause>,
) -> (VecDeque<Clause>, VecDeque<Clause>) {
    fn clause_from_head(p: &Pattern, ps: &[Pattern], act: &MatchAction) -> Clause {
        let mut new_p_row = vec![p.clone()];
        new_p_row.extend_from_slice(ps);
        (new_p_row, act.clone())
    }

    let ors_len = ors.len();

    for index in 0..ors_len {
        let cl = ors
            .get(index)
            .expect("insert_or_append: index within deque length");
        let (q_head, qs) = match cl.0.split_first() {
            Some((q, qs)) => (q, qs),
            None => panic!("insert_or_append: empty pattern row"),
        };
        let act_q = &cl.1;

        if is_or(q_head) && may_compat(p, q_head) {
            if !pattern_binds_vars(p) && !pattern_binds_vars(q_head) && equiv_pat(p, q_head) {
                // OCaml compiler/ml/matching.ml:743-756 checks the tail after
                // the equivalent-prefix group. Keep that as deque iteration so
                // we do not force VecDeque::make_contiguous on a push_front-built
                // accumulator.
                let equivalent_tail_len = ors
                    .iter()
                    .skip(index + 1)
                    .take_while(|cl| match cl.0.first() {
                        Some(q) => equiv_pat(q_head, q),
                        None => false,
                    })
                    .count();
                let not_e_start = index + 1 + equivalent_tail_len;
                if or_ok_iter(p, ps, ors.iter().skip(not_e_start))
                    && ors
                        .iter()
                        .take(index)
                        .all(|seen_cl| match seen_cl.0.first() {
                            Some(q) => !may_compat(p, q),
                            None => panic!("insert_or_append: empty seen row"),
                        })
                {
                    // OCaml compiler/ml/matching.ml:733-756 builds `seen` as a
                    // shared list prefix. Keep the Rust equivalent as a deque
                    // prefix and only clone rows when reconstructing the result.
                    let mut result = VecDeque::with_capacity(ors_len + 1);
                    result.extend(ors.iter().take(index).cloned());
                    result.push_back(clause_from_head(p, ps, act));
                    result.push_back(cl.clone());
                    result.extend(ors.iter().skip(index + 1).cloned());
                    return (result, no);
                }

                no.push_front(clause_from_head(p, ps, act));
                return (ors, no);
            }

            if !condb(act_q, ps, qs) {
                no.push_front(clause_from_head(p, ps, act));
                return (ors, no);
            }
        }

        // OCaml's recursive `attempt (cl :: seen) rem` shares `cl`
        // (compiler/ml/matching.ml:733-734,768). The current index is the
        // logical `seen` prefix for subsequent iterations.
    }

    // OCaml compiler/ml/matching.ml:768-773 returns `((p :: ps, act) :: ors, no)`.
    ors.push_front(clause_from_head(p, ps, act));
    (ors, no)
}

// ============================================================================
// Rebuild functions (lines 777-793)
// ============================================================================

/// Reconstruct a matrix from a half-compiled pattern matching.
/// Equivalent to OCaml's `rebuild_matrix`.
fn rebuild_matrix(pmh: &PmHalfCompiled) -> Matrix {
    match pmh {
        PmHalfCompiled::Pm(pm) => as_matrix(&pm.cases),
        PmHalfCompiled::PmOr(por) => por.or_matrix.clone(),
        PmHalfCompiled::PmVar(x) => add_omega_column(&rebuild_matrix(&x.inside)),
    }
}

/// Reconstruct default information from half-compiled pm list.
/// Equivalent to OCaml's `rebuild_default`.
fn rebuild_default(nexts: &[(i32, PmHalfCompiled)], def: DefaultEnv) -> DefaultEnv {
    match nexts.split_first() {
        None => def,
        Some(((e, pmh), rem)) => {
            let mut result = vec![(add_omega_column(&rebuild_matrix(pmh)), *e)];
            result.extend(rebuild_default(rem, def));
            result
        }
    }
}

/// Wrap nexts with PmVar nodes.
/// Equivalent to OCaml's `rebuild_nexts`.
fn rebuild_nexts(
    arg: &RawLambda,
    nexts: Vec<(i32, PmHalfCompiled)>,
    k: Vec<(i32, PmHalfCompiled)>,
) -> Vec<(i32, PmHalfCompiled)> {
    // OCaml compiler/ml/matching.ml:789-792 uses `List.fold_right` to keep
    // `nexts` order and prepend each wrapped item before `k`.
    let mut result = Vec::with_capacity(nexts.len() + k.len());
    result.extend(nexts.into_iter().map(|(e, pm)| {
        (
            e,
            PmHalfCompiled::PmVar(PmVarCompiled {
                inside: Box::new(pm),
                var_arg: arg.clone(),
            }),
        )
    }));
    result.extend(k);
    result
}

// ============================================================================
// Split functions (lines 814-1090)
// ============================================================================

/// Split a matching, directed first by or-patterns, then by tests/variable transitions.
/// Equivalent to OCaml's `split_or`.
fn split_or(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    cls: Vec<Clause>,
    args: &MatchArgs,
    def: DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    let cls = simplify_cases(ctx_ref, args, cls);

    do_split_or(
        ctx_ref,
        argo,
        VecDeque::new(),
        VecDeque::new(),
        VecDeque::new(),
        cls.into(),
        args,
        &def,
        next_raise,
    )
}

/// Inner do_split for split_or.
fn do_split_or(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    mut before: VecDeque<Clause>,
    mut ors: VecDeque<Clause>,
    mut no: VecDeque<Clause>,
    mut rest: VecDeque<Clause>,
    args: &MatchArgs,
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    // OCaml `compiler/ml/matching.ml:817-828` is tail-recursive. Rust does not
    // guarantee tail-call elimination, and large generated matches build very
    // deep `do_split_or` stacks. Keep the exact branch order but run it as an
    // explicit loop.
    loop {
        let Some(cl) = rest.pop_front() else {
            let before = rev_deque_to_vec(before);
            let ors = rev_deque_to_vec(ors);
            let no = rev_deque_to_vec(no);
            return cons_next_or(ctx_ref, argo, before, ors, no, args, def, next_raise);
        };

        let push_to_before_or_ors = {
            let (p, ps) = cl.0.split_first().expect("split_or: empty pattern row");
            let act = &cl.1;
            if up_ok_iter(cl.0.as_slice(), act, no.iter()) {
                if is_or(p) {
                    let (new_ors, new_no) = insert_or_append(p, ps, act, ors, no);
                    ors = new_ors;
                    no = new_no;
                    continue;
                } else if up_ok_iter(cl.0.as_slice(), act, ors.iter()) {
                    // OCaml `do_split` moves the current row into `before` with
                    // `(cl :: before)` (compiler/ml/matching.ml:820-826).
                    Some(true)
                } else if or_ok_iter(p, ps, ors.iter()) {
                    Some(false)
                } else {
                    None
                }
            } else {
                None
            }
        };

        match push_to_before_or_ors {
            Some(true) => before.push_front(cl),
            Some(false) => ors.push_front(cl),
            None => no.push_front(cl),
        }
    }
}

/// cons_next helper for split_or.
fn cons_next_or(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    yes: Vec<Clause>,
    yesor: Vec<Clause>,
    no: Vec<Clause>,
    args: &MatchArgs,
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    if no.is_empty() {
        precompile_or(
            ctx_ref,
            argo,
            yes,
            yesor,
            args,
            def.clone(),
            Vec::new(),
            next_raise,
        )
    } else {
        let (info, nexts) = do_split_or(
            ctx_ref,
            argo,
            VecDeque::new(),
            VecDeque::new(),
            VecDeque::new(),
            no.into(),
            args,
            def,
            next_raise,
        );
        let idef = bump_raise_count(next_raise, "matching::cons_next_or");
        let PmHalfCompiledInfo {
            me: next,
            matrix,
            top_default,
        } = info;
        let new_def = cons_default(matrix, idef, top_default);
        let mut new_nexts = vec![(idef, next)];
        new_nexts.extend(nexts);
        precompile_or(
            ctx_ref, argo, yes, yesor, args, new_def, new_nexts, next_raise,
        )
    }
}

/// Ultra-naive splitting, close to semantics, used for extension constructors.
/// Equivalent to OCaml's `split_naive`.
fn split_naive(
    cls: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match cls.split_first() {
        None => panic!("split_naive: empty cases"),
        Some((cl, rem)) => match cl.0.first() {
            Some(p) if group_constructor(p) => split_exc(
                pat_as_constr(p),
                vec![cl.clone()],
                rem,
                args,
                def,
                k,
                next_raise,
            ),
            Some(_) => split_noexc(vec![cl.clone()], rem, args, def, k, next_raise),
            None => panic!("split_naive: empty pattern row"),
        },
    }
}

/// Split on extension constructors (naive).
fn split_exc(
    cstr0: &crate::types::ConstructorDescription,
    yes: Vec<Clause>,
    rest: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            (
                PmHalfCompiledInfo {
                    me: PmHalfCompiled::Pm(PatternMatching {
                        cases: yes.clone(),
                        args: args.clone(),
                        default: def.clone(),
                    }),
                    matrix: as_matrix(&yes),
                    top_default: def,
                },
                k,
            )
        }
        Some((cl, rem)) => match cl.0.first() {
            Some(p) if group_constructor(p) => {
                let cstr = pat_as_constr(p);
                if same_constructor(cstr, cstr0) {
                    let mut new_yes = yes;
                    new_yes.insert(0, cl.clone());
                    split_exc(cstr0, new_yes, rem, args, def, k, next_raise)
                } else {
                    let yes = rev_vec(yes);
                    let (info, nexts) = split_exc(
                        cstr,
                        vec![cl.clone()],
                        rem,
                        args,
                        def.clone(),
                        k,
                        next_raise,
                    );
                    let idef = bump_raise_count(next_raise, "matching::split_exc:constructor");
                    let PmHalfCompiledInfo {
                        me: next,
                        matrix,
                        top_default,
                    } = info;
                    let new_def = cons_default(matrix, idef, top_default);
                    let mut new_nexts = vec![(idef, next)];
                    new_nexts.extend(nexts);
                    (
                        PmHalfCompiledInfo {
                            me: PmHalfCompiled::Pm(PatternMatching {
                                cases: yes.clone(),
                                args: args.clone(),
                                default: new_def.clone(),
                            }),
                            matrix: as_matrix(&yes),
                            top_default: new_def,
                        },
                        new_nexts,
                    )
                }
            }
            Some(_) => {
                let yes = rev_vec(yes);
                let (info, nexts) =
                    split_noexc(vec![cl.clone()], rem, args, def.clone(), k, next_raise);
                let idef = bump_raise_count(next_raise, "matching::split_exc:nonconstructor");
                let PmHalfCompiledInfo {
                    me: next,
                    matrix,
                    top_default,
                } = info;
                let new_def = cons_default(matrix, idef, top_default);
                let mut new_nexts = vec![(idef, next)];
                new_nexts.extend(nexts);
                (
                    PmHalfCompiledInfo {
                        me: PmHalfCompiled::Pm(PatternMatching {
                            cases: yes.clone(),
                            args: args.clone(),
                            default: new_def.clone(),
                        }),
                        matrix: as_matrix(&yes),
                        top_default: new_def,
                    },
                    new_nexts,
                )
            }
            None => panic!("split_exc: empty pattern row"),
        },
    }
}

/// Split on non-extension constructors (naive).
fn split_noexc(
    yes: Vec<Clause>,
    rest: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            precompile_var(args, yes, def, k, next_raise)
        }
        Some((cl, rem)) => match cl.0.first() {
            Some(p) if group_constructor(p) => {
                let yes = rev_vec(yes);
                let (info, nexts) = split_exc(
                    pat_as_constr(p),
                    vec![cl.clone()],
                    rem,
                    args,
                    def.clone(),
                    k,
                    next_raise,
                );
                let idef = bump_raise_count(next_raise, "matching::split_noexc");
                let PmHalfCompiledInfo {
                    me: next,
                    matrix,
                    top_default,
                } = info;
                precompile_var(
                    args,
                    yes,
                    cons_default(matrix, idef, top_default),
                    {
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        new_nexts
                    },
                    next_raise,
                )
            }
            Some(_) => {
                let mut new_yes = yes;
                new_yes.insert(0, cl.clone());
                split_noexc(new_yes, rem, args, def, k, next_raise)
            }
            None => panic!("split_noexc: empty pattern row"),
        },
    }
}

/// Split on constructors using group predicates.
/// Equivalent to OCaml's `split_constr`.
fn split_constr(
    cls: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    let ex_pat = what_is_cases(cls);
    match &ex_pat.pat_desc {
        PatternDesc::Tpat_any => precompile_var(args, cls.to_vec(), def, k, next_raise),
        PatternDesc::Tpat_construct(_, cstr, _)
            if matches!(&cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) =>
        {
            split_naive(cls, args, def, k, next_raise)
        }
        _ => {
            let group = get_group(&ex_pat);
            match cls.split_first() {
                Some((cl, rem)) => match cl.0.first() {
                    Some(p) if group(p) => split_ex(
                        group,
                        vec![cl.clone()],
                        Vec::new(),
                        rem,
                        args,
                        def,
                        k,
                        next_raise,
                    ),
                    _ => split_noex(
                        group,
                        vec![cl.clone()],
                        Vec::new(),
                        rem,
                        args,
                        def,
                        k,
                        next_raise,
                    ),
                },
                None => panic!("split_constr: empty cases"),
            }
        }
    }
}

/// split_ex: raise constructor rows up.
fn split_ex(
    group: fn(&Pattern) -> bool,
    yes: Vec<Clause>,
    no: Vec<Clause>,
    rest: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            let no = rev_vec(no);
            match no.split_first() {
                None => (
                    PmHalfCompiledInfo {
                        me: PmHalfCompiled::Pm(PatternMatching {
                            cases: yes.clone(),
                            args: args.clone(),
                            default: def.clone(),
                        }),
                        matrix: as_matrix(&yes),
                        top_default: def,
                    },
                    k,
                ),
                Some((no_cl, no_rem)) => {
                    if yes.is_empty() {
                        // Could not succeed in raising up a constr matching up
                        split_noex(
                            group,
                            vec![no_cl.clone()],
                            Vec::new(),
                            no_rem,
                            args,
                            def,
                            k,
                            next_raise,
                        )
                    } else {
                        let (info, nexts) = split_noex(
                            group,
                            vec![no_cl.clone()],
                            Vec::new(),
                            no_rem,
                            args,
                            def.clone(),
                            k,
                            next_raise,
                        );
                        let idef = bump_raise_count(next_raise, "matching::split_ex");
                        let PmHalfCompiledInfo {
                            me: next,
                            matrix,
                            top_default,
                        } = info;
                        let new_def = cons_default(matrix, idef, top_default);
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        (
                            PmHalfCompiledInfo {
                                me: PmHalfCompiled::Pm(PatternMatching {
                                    cases: yes.clone(),
                                    args: args.clone(),
                                    default: new_def.clone(),
                                }),
                                matrix: as_matrix(&yes),
                                top_default: new_def,
                            },
                            new_nexts,
                        )
                    }
                }
            }
        }
        Some((cl, rem)) => match cl.0.first() {
            Some(p) if group(p) && up_ok(&cl.0, &cl.1, &no) => {
                let mut new_yes = yes;
                new_yes.insert(0, cl.clone());
                split_ex(group, new_yes, no, rem, args, def, k, next_raise)
            }
            _ => {
                let mut new_no = no;
                new_no.insert(0, cl.clone());
                split_ex(group, yes, new_no, rem, args, def, k, next_raise)
            }
        },
    }
}

/// split_noex: raise non-constructor rows up.
fn split_noex(
    group: fn(&Pattern) -> bool,
    yes: Vec<Clause>,
    no: Vec<Clause>,
    rest: &[Clause],
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            let no = rev_vec(no);
            match no.split_first() {
                None => precompile_var(args, yes, def, k, next_raise),
                Some((no_cl, no_rem)) => {
                    let (info, nexts) = split_ex(
                        group,
                        vec![no_cl.clone()],
                        Vec::new(),
                        no_rem,
                        args,
                        def.clone(),
                        k,
                        next_raise,
                    );
                    let idef = bump_raise_count(next_raise, "matching::split_noex");
                    let PmHalfCompiledInfo {
                        me: next,
                        matrix,
                        top_default,
                    } = info;
                    precompile_var(
                        args,
                        yes,
                        cons_default(matrix, idef, top_default),
                        {
                            let mut new_nexts = vec![(idef, next)];
                            new_nexts.extend(nexts);
                            new_nexts
                        },
                        next_raise,
                    )
                }
            }
        }
        Some((_cl, _rem)) if rest.len() == 1 => {
            // Check for the special case: last row is all variables and yes is non-empty
            let cl = &rest[0];
            if cl.0.iter().all(|p| group_var(p)) && !yes.is_empty() {
                // This enables an extra division in some frequent cases:
                // last row is made of variables only
                let mut new_no = no;
                new_no.insert(0, cl.clone());
                split_noex(group, yes, new_no, &[], args, def, k, next_raise)
            } else {
                // Fall through to normal case
                let cl = &rest[0];
                match cl.0.first() {
                    Some(p) if !group(p) && up_ok(&cl.0, &cl.1, &no) => {
                        let mut new_yes = yes;
                        new_yes.insert(0, cl.clone());
                        split_noex(group, new_yes, no, &[], args, def, k, next_raise)
                    }
                    _ => {
                        let mut new_no = no;
                        new_no.insert(0, cl.clone());
                        split_noex(group, yes, new_no, &[], args, def, k, next_raise)
                    }
                }
            }
        }
        Some((cl, rem)) => match cl.0.first() {
            Some(p) if !group(p) && up_ok(&cl.0, &cl.1, &no) => {
                let mut new_yes = yes;
                new_yes.insert(0, cl.clone());
                split_noex(group, new_yes, no, rem, args, def, k, next_raise)
            }
            _ => {
                let mut new_no = no;
                new_no.insert(0, cl.clone());
                split_noex(group, yes, new_no, rem, args, def, k, next_raise)
            }
        },
    }
}

/// Precompile variable patterns: if the match argument is a variable,
/// split further on the second column.
/// Equivalent to OCaml's `precompile_var`.
fn precompile_var(
    args: &MatchArgs,
    cls: Vec<Clause>,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match args.as_slice() {
        [] => panic!("precompile_var: empty args"),
        [_, arg_rest @ ..] if !arg_rest.is_empty() => {
            // Check if second arg is Lvar
            match &arg_rest[0].0 {
                RawLambda::Lvar(v) => {
                    if cls.len() == 1 {
                        // as split as it can
                        dont_precompile_var(args, cls, def, k)
                    } else {
                        // Precompile: strip first pattern from each case
                        let var_cls: Vec<Clause> = cls
                            .iter()
                            .map(|(ps, act)| match ps.split_first() {
                                Some((_, rest)) => (rest.to_vec(), act.clone()),
                                None => panic!("precompile_var: empty pattern row"),
                            })
                            .collect();
                        let var_def =
                            make_default(&|_p: &Pattern, rem: &[Pattern]| Ok(rem.to_vec()), &def);
                        let av = arg_rest[0].0.clone();
                        let arg_tail = args.tail(1);
                        let (first_info, nexts) = split_or(
                            None, // TypeContext not available in do_split_or
                            &Some(v.clone()),
                            var_cls,
                            &arg_tail,
                            var_def,
                            next_raise,
                        );

                        // Compute top information
                        if nexts.is_empty() {
                            // If you need
                            dont_precompile_var(args, cls, def, k)
                        } else {
                            let rfirst = PmHalfCompiledInfo {
                                me: PmHalfCompiled::PmVar(PmVarCompiled {
                                    inside: Box::new(first_info.me),
                                    var_arg: av.clone(),
                                }),
                                matrix: add_omega_column(&first_info.matrix),
                                top_default: rebuild_default(&nexts, def),
                            };
                            let rnexts = rebuild_nexts(&av, nexts, k);
                            (rfirst, rnexts)
                        }
                    }
                }
                _ => dont_precompile_var(args, cls, def, k),
            }
        }
        _ => dont_precompile_var(args, cls, def, k),
    }
}

/// Don't precompile: just wrap the cases in a PatternMatching.
/// Equivalent to OCaml's `dont_precompile_var`.
fn dont_precompile_var(
    args: &MatchArgs,
    cls: Vec<Clause>,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    (
        PmHalfCompiledInfo {
            me: PmHalfCompiled::Pm(PatternMatching {
                cases: cls.clone(),
                args: args.clone(),
                default: def.clone(),
            }),
            matrix: as_matrix(&cls),
            top_default: def,
        },
        k,
    )
}

/// Precompile or-patterns.
/// Equivalent to OCaml's `precompile_or`.
fn precompile_or(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    cls: Vec<Clause>,
    ors: Vec<Clause>,
    args: &MatchArgs,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    if ors.is_empty() {
        return split_constr(&cls, args, def, k, next_raise);
    }

    // do_cases processes the or-pattern list
    let (end_body, handlers) = do_cases_or(ctx_ref, argo, &ors, args, &def, next_raise);

    let matrix = as_matrix(&[cls.as_slice(), ors.as_slice()].concat());
    let body = PatternMatching {
        cases: [cls, end_body].concat(),
        args: args.clone(),
        default: def.clone(),
    };
    (
        PmHalfCompiledInfo {
            me: PmHalfCompiled::PmOr(PmOrCompiled {
                body,
                handlers,
                or_matrix: matrix.clone(),
            }),
            matrix,
            top_default: def,
        },
        k,
    )
}

/// Process or-pattern cases for precompile_or.
/// Equivalent to the inner `do_cases` in OCaml's `precompile_or`.
fn do_cases_or(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    ors: &[Clause],
    args: &MatchArgs,
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (Vec<Clause>, Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>) {
    let (body, handlers) = do_cases_or_deque(ctx_ref, argo, ors, args, def, next_raise);
    (body.into_iter().collect(), handlers)
}

fn do_cases_or_deque(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    ors: &[Clause],
    args: &MatchArgs,
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (
    VecDeque<Clause>,
    Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>,
) {
    match ors.split_first() {
        None => (VecDeque::new(), Vec::new()),
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(orp) if is_or(orp) => {
                    let patl = &cl.0[1..];
                    let action = &cl.1;

                    let (others, rem) = get_equiv(orp, rem);

                    let orpm_cases = {
                        let mut cases = vec![(patl.to_vec(), action.clone())];
                        cases.extend(others.iter().map(|(ps, act)| match ps.split_first() {
                            Some((_, rest)) => (rest.to_vec(), act.clone()),
                            None => panic!("do_cases_or: empty pattern row"),
                        }));
                        cases
                    };
                    let orpm_args = match args.split_first() {
                        Some(_) => args.tail(1),
                        None => panic!("do_cases_or: empty args"),
                    };
                    let orpm = PatternMatching {
                        cases: orpm_cases,
                        args: orpm_args,
                        default: default_compat(orp, def),
                    };

                    let vars: Vec<Ident> = {
                        let orp_vars = extract_vars(BTreeSet::new(), orp);
                        let pm_fv = pm_free_variables(&orpm);
                        orp_vars.intersection(&pm_fv).cloned().collect()
                    };

                    let or_num = bump_raise_count(next_raise, "matching::do_cases_or");
                    let new_patl = omega_list(patl);

                    let mk_new_action = |vs: &[Ident]| -> RawLambda {
                        RawLambda::LstaticRaise(
                            or_num,
                            vs.iter().map(|v| RawLambda::Lvar(v.clone())).collect(),
                        )
                    };

                    let (body, handlers) =
                        do_cases_or_deque(ctx_ref, argo, &rem, args, def, next_raise);

                    let exploded = explode_or_pat(
                        ctx_ref,
                        argo,
                        &new_patl,
                        &mk_new_action,
                        body.into_iter().collect(),
                        &vars.iter().cloned().collect(),
                        &[],
                        orp,
                    );

                    let new_body = match exploded {
                        Ok(b) => b,
                        Err(_) => panic!("do_cases_or: Cannot_flatten"),
                    };

                    let mat = vec![vec![orp.clone()]];
                    let mut new_handlers = vec![(mat, or_num, vars, orpm)];
                    new_handlers.extend(handlers);
                    (new_body.into(), new_handlers)
                }
                _ => {
                    // OCaml compiler/ml/matching.ml:846-1090 conses ordinary
                    // rows before the recursively processed tail. Use
                    // `push_front` for the same list shape without shifting a
                    // Rust Vec on every row.
                    let (mut new_ord, new_to_catch) =
                        do_cases_or_deque(ctx_ref, argo, rem, args, def, next_raise);
                    new_ord.push_front(cl.clone());
                    (new_ord, new_to_catch)
                }
            }
        }
    }
}

/// Top-level split_precompile.
/// Equivalent to OCaml's `split_precompile`.
pub fn split_precompile(
    ctx_ref: Option<&TypeContext>,
    argo: &Option<Ident>,
    pm: &PatternMatching,
    next_raise: &mut i32,
) -> (PmHalfCompiled, Vec<(i32, PmHalfCompiled)>) {
    let (info, nexts) = split_or(
        ctx_ref,
        argo,
        pm.cases.clone(),
        &pm.args,
        pm.default.clone(),
        next_raise,
    );
    (info.me, nexts)
}

/// Reverse a vector — equivalent to OCaml's `List.rev`.
///
/// OCaml compiler/ml/matching.ml:814-846 accumulates rows with `::` and restores
/// source order with `List.rev`; callers use `VecDeque::push_front` for the
/// same asymptotic behavior.
fn rev_vec<T>(mut v: Vec<T>) -> Vec<T> {
    v.reverse();
    v
}

fn rev_deque_to_vec<T>(v: VecDeque<T>) -> Vec<T> {
    let mut v: Vec<T> = v.into_iter().collect();
    v.reverse();
    v
}

// ============================================================================
// Layer 5: General divide functions (lines 1094-1131)
// ============================================================================

/// A cell: a pattern matching with its context list and pattern.
/// Equivalent to OCaml's `cell`.
struct MatchCell {
    pm: PatternMatching,
    ctx: Vec<Ctx>,
    pat: Pattern,
}

/// Add a case to the appropriate cell in a division, creating a new cell if needed.
/// Equivalent to OCaml's `add`.
fn add<K>(
    make_matching_fun: impl FnOnce(&MatchArgs) -> MatchCell,
    mut division: Vec<(K, MatchCell)>,
    eq_key: impl Fn(&K, &K) -> bool,
    key: K,
    patl_action: Clause,
    args: &MatchArgs,
) -> Vec<(K, MatchCell)> {
    // Try to find existing entry with matching key
    if let Some(pos) = division.iter().position(|(k, _)| eq_key(&key, k)) {
        division[pos].1.pm.cases.insert(0, patl_action);
        division
    } else {
        let mut cell = make_matching_fun(args);
        cell.pm.cases = vec![patl_action];
        division.insert(0, (key, cell));
        division
    }
}

/// Divide a pattern matching by the first pattern column, grouping by key.
/// OCaml's `compiler/ml/matching.ml:1110-1120` recurses to the tail, then
/// conses the current case with `add` (`compiler/ml/matching.ml:1100-1108`).
/// Iterating from the tail, pushing, and reversing once preserves the same
/// group/case order without Rust `Vec::insert(0, ...)` shifting every element.
fn divide<K>(
    make: impl Fn(&Pattern, &DefaultEnv, &[Ctx], &MatchArgs) -> MatchCell,
    eq_key: impl Fn(&K, &K) -> bool,
    get_key: impl Fn(&Pattern) -> K,
    get_args: impl Fn(&Pattern, &[Pattern]) -> Vec<Pattern>,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<(K, MatchCell)> {
    let mut division: Vec<(K, MatchCell)> = Vec::new();

    for (patl, action) in pm.cases.iter().rev() {
        let Some((p, rest_patl)) = patl.split_first() else {
            division.clear();
            continue;
        };

        let key = get_key(p);
        let patl_action = (get_args(p, rest_patl), action.clone());

        if let Some(pos) = division.iter().position(|(k, _)| eq_key(&key, k)) {
            division[pos].1.pm.cases.push(patl_action);
        } else {
            let mut cell = make(p, &pm.default, ctx, &pm.args);
            cell.pm.cases.push(patl_action);
            division.push((key, cell));
        }
    }

    division.reverse();
    for (_, cell) in &mut division {
        cell.pm.cases.reverse();
    }
    division
}

/// Divide a pattern matching into a single cell (no grouping by key).
/// OCaml's `compiler/ml/matching.ml:1122-1130` uses the same tail-recursive
/// consing shape as `divide`; use push + one suffix reverse to keep that order
/// without shifting the whole Rust vector per case.
fn divide_line(
    make_ctx: impl Fn(&[Ctx]) -> Vec<Ctx>,
    make: impl Fn(&DefaultEnv, &MatchArgs) -> PatternMatching,
    get_args: impl Fn(&Pattern, &[Pattern]) -> Vec<Pattern>,
    pat: Pattern,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> MatchCell {
    let mut divided = make(&pm.default, &pm.args);
    let mut base_case_count = divided.cases.len();

    for (patl, action) in pm.cases.iter().rev() {
        match patl.split_first() {
            Some((p, rest_patl)) => {
                divided.cases.push((get_args(p, rest_patl), action.clone()));
            }
            None => {
                divided = make(&pm.default, &pm.args);
                base_case_count = divided.cases.len();
            }
        }
    }

    divided.cases[base_case_count..].reverse();

    MatchCell {
        pm: divided,
        ctx: make_ctx(ctx),
        pat,
    }
}

// ============================================================================
// Layer 6: Per-type pattern matchers (lines 1148-1516)
// ============================================================================

// --- Constants (lines 1148-1177) ---

/// Matcher for constant patterns.
/// Equivalent to OCaml's `matcher_const`.
fn matcher_const(cst: &Constant, p: &Pattern, rem: &[Pattern]) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => match matcher_const(cst, p1, rem) {
            Ok(r) => Ok(r),
            Err(MatchError::NoMatch) => matcher_const(cst, p2, rem),
            Err(e) => Err(e),
        },
        PatternDesc::Tpat_constant(c1) if const_compare(c1, cst) == std::cmp::Ordering::Equal => {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Get the key (constant) from a constant pattern.
/// Equivalent to OCaml's `get_key_constant`.
fn get_key_constant(caller: &str, p: &Pattern) -> Constant {
    match &p.pat_desc {
        PatternDesc::Tpat_constant(cst) => cst.clone(),
        _ => {
            eprintln!("BAD: {}", caller);
            // pretty_pat p; -- omitted
            panic!("get_key_constant: not a constant pattern");
        }
    }
}

/// Get the arguments from a constant pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_constant`.
fn get_args_constant(_p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    rem.to_vec()
}

/// Make a constant matching cell.
/// Equivalent to OCaml's `make_constant_matching`.
fn make_constant_matching(
    p: &Pattern,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &MatchArgs,
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_constant_matching"),
        Some(_) => {
            let key = get_key_constant("make", p);
            let def = make_default(&|p2, rem| matcher_const(&key, p2, rem), def);
            let ctx = filter_ctx(None, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: args.tail(1),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by constant values.
/// Equivalent to OCaml's `divide_constant`.
fn divide_constant(ctx: &[Ctx], m: &PatternMatching) -> Vec<(Constant, MatchCell)> {
    divide(
        make_constant_matching,
        |c, d| const_compare(c, d) == std::cmp::Ordering::Equal,
        |p| get_key_constant("divide", p),
        get_args_constant,
        ctx,
        m,
    )
}

// --- Constructors (lines 1180-1289) ---

/// Make field access arguments for a constructor.
/// Equivalent to OCaml's `make_field_args`.
fn make_field_args(
    fld_info: FieldDbgInfo,
    loc: Location,
    binding_kind: LetKind,
    arg: &RawLambda,
    first_pos: i32,
    last_pos: i32,
    argl: &MatchArgs,
) -> Vec<(RawLambda, LetKind)> {
    let mut result = Vec::new();
    for pos in first_pos..=last_pos {
        result.push((
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pfield(pos, fld_info.clone()),
                args: vec![arg.clone()],
                loc: loc.clone(),
            }),
            binding_kind,
        ));
    }
    result.extend(argl.iter().cloned());
    result
}

/// Get the declared constructor from a constructor pattern.
/// Equivalent to OCaml's `get_key_constr`.
fn get_key_constr(p: &Pattern) -> ConstructorDescription {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr.clone(),
        _ => panic!("get_key_constr: not a construct pattern"),
    }
}

/// Get the arguments from a constructor pattern.
/// Equivalent to OCaml's `get_args_constr`.
fn get_args_constr(p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, _, args) => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_constr: not a construct pattern"),
    }
}

/// Matcher for constructor patterns.
/// Equivalent to OCaml's `matcher_constr`.
///
/// NB: matcher_constr applies to default matrices.
/// In that context, matching by constructors of extensible
/// types degrades to arity checking, due to potential rebinding.
/// This comparison is performed by Types.may_equal_constr.
fn matcher_constr(
    cstr: &ConstructorDescription,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match cstr.cstr_arity {
        0 => matcher_constr_arity0(cstr, p, rem),
        1 => matcher_constr_arity1(cstr, p, rem),
        _ => matcher_constr_arityN(cstr, p, rem),
    }
}

/// Matcher for 0-arity constructor.
fn matcher_constr_arity0(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => match matcher_constr_arity0(cstr, p1, rem) {
            Ok(r) => Ok(r),
            Err(MatchError::NoMatch) => matcher_constr_arity0(cstr, p2, rem),
            Err(e) => Err(e),
        },
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.is_empty() && may_equal_constr(cstr, cstr2) =>
        {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for 1-arity constructor.
fn matcher_constr_arity1(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            let r1 = matcher_constr_arity1(cstr, p1, rem).ok();
            let r2 = matcher_constr_arity1(cstr, p2, rem).ok();
            match (r1, r2) {
                (None, None) => Err(MatchError::NoMatch),
                (Some(r1), None) => Ok(r1),
                (None, Some(r2)) => Ok(r2),
                (Some(r1), Some(r2)) => match (r1.first(), r2.first()) {
                    (Some(a1), Some(a2)) => {
                        let or_pat = Pattern {
                            pat_desc: PatternDesc::Tpat_or(
                                Box::new(a1.clone()),
                                Box::new(a2.clone()),
                                None,
                            ),
                            pat_loc: LocIdx::none(),
                            pat_extra: Default::default(),
                            pat_type: a1.pat_type,
                            pat_env: a1.pat_env,
                            pat_attributes: Attributes::new(),
                        };
                        let mut result = vec![or_pat];
                        result.extend(rem.iter().cloned());
                        Ok(result)
                    }
                    _ => panic!("matcher_constr_arity1: unexpected empty result"),
                },
            }
        }
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.len() == 1 && may_equal_constr(cstr, cstr2) =>
        {
            let mut result = vec![args[0].clone()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for N-arity constructor (N >= 2).
fn matcher_constr_arityN(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_construct(_, cstr2, args) if may_equal_constr(cstr, cstr2) => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(cstr.cstr_arity as usize);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Helper: get runtime name from label attributes (OCaml's Lambda.find_name).
fn label_runtime_name_matching(lbl: &LabelDescription) -> String {
    for attr in &lbl.lbl_attributes {
        if attr.attr_name.txt == "as" {
            if let crate::types::decl::AttributePayload::Str(name) = &attr.attr_payload {
                return name.clone();
            }
        }
    }
    lbl.lbl_name.clone()
}

/// Create field debug info for a record label (equivalent to OCaml's Lambda.fld_record).
fn fld_record(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::Record {
        name: label_runtime_name_matching(lbl),
    }
}

/// Create field debug info for an inlined record label (equivalent to OCaml's Lambda.fld_record_inline).
fn fld_record_inline(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordInline {
        name: label_runtime_name_matching(lbl),
    }
}

/// Create field debug info for a record extension label (equivalent to OCaml's Lambda.fld_record_extension).
fn fld_record_extension(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordExtension {
        name: label_runtime_name_matching(lbl),
    }
}

/// Make a constructor matching cell.
/// Equivalent to OCaml's `make_constr_matching`.
fn make_constr_matching(
    ctx_ref: &TypeContext,
    p: &Pattern,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &MatchArgs,
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_constr_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let cstr = pat_as_constr(p);
            let untagged = has_untagged(&cstr.cstr_attributes);
            let newargs = if cstr.cstr_inlined.is_some() || (untagged && !cstr.cstr_args.is_empty())
            {
                let mut result = vec![(arg.clone(), LetKind::Alias)];
                result.extend(argl.iter().cloned());
                result
            } else {
                match &cstr.cstr_kind {
                    // OCaml compiler/ml/matching.ml only unwraps option-shaped
                    // ordinary constructors marked with internal.optional.
                    crate::types::ConstructorKind::Ordinary(_)
                        if !cstr.cstr_args.is_empty() && constructor_has_optional_shape(cstr) =>
                    {
                        let from_option = match &p.pat_desc {
                            PatternDesc::Tpat_construct(_, _, args_inner)
                                if args_inner.len() == 1 =>
                            {
                                let pat = &args_inner[0];
                                // First try env-based check
                                let env_opt = ctx_ref.get_typed_env(pat.pat_env);
                                let can_skip = env_opt
                                    .map(|env| {
                                        type_cannot_contain_undefined(
                                            ctx_ref,
                                            env.as_ref(),
                                            pat.pat_type,
                                        )
                                    })
                                    .unwrap_or_else(|| {
                                        // Fast path: check type descriptor directly
                                        // (works for Ttuple, Tarrow, Tvariant, Tpackage
                                        // which always return true)
                                        type_cannot_contain_undefined_no_env(ctx_ref, pat.pat_type)
                                    });
                                if can_skip {
                                    Primitive::PvalFromOptionNotNest
                                } else {
                                    Primitive::PvalFromOption
                                }
                            }
                            _ => Primitive::PvalFromOption,
                        };
                        let mut result = vec![(
                            RawLambda::Lprim(RawPrimInfo {
                                primitive: from_option,
                                args: vec![arg.clone()],
                                loc: Location::none(),
                            }),
                            LetKind::Alias,
                        )];
                        result.extend(argl.iter().cloned());
                        result
                    }
                    crate::types::ConstructorKind::Ordinary(_) => {
                        let fld_info = if cstr.cstr_name == "::" {
                            FieldDbgInfo::Cons
                        } else {
                            FieldDbgInfo::Variant
                        };
                        make_field_args(
                            fld_info,
                            Location::none(),
                            LetKind::Alias,
                            arg,
                            0,
                            cstr.cstr_arity - 1,
                            &argl,
                        )
                    }
                    crate::types::ConstructorKind::Extension(_) => make_field_args(
                        FieldDbgInfo::Extension,
                        Location::none(),
                        LetKind::Alias,
                        arg,
                        1,
                        cstr.cstr_arity,
                        &argl,
                    ),
                }
            };
            let cstr_clone = cstr.clone();
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: MatchArgs::new(newargs),
                    default: make_default(&|p2, rem| matcher_constr(&cstr_clone, p2, rem), def),
                },
                ctx: filter_ctx(Some(ctx_ref), p, ctx),
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by constructor.
/// Equivalent to OCaml's `divide_constructor`.
fn divide_constructor(
    ctx_ref: &TypeContext,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<(ConstructorDescription, MatchCell)> {
    divide(
        |p, def, ctx_inner, args| make_constr_matching(ctx_ref, p, def, ctx_inner, args),
        same_constructor,
        get_key_constr,
        get_args_constr,
        ctx,
        pm,
    )
}

// --- Variants (lines 1293-1362) ---

/// Matcher for constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_const`.
fn matcher_variant_const(
    lab: &str,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => match matcher_variant_const(lab, p1, rem) {
            Ok(r) => Ok(r),
            Err(MatchError::NoMatch) => matcher_variant_const(lab, p2, rem),
            Err(e) => Err(e),
        },
        PatternDesc::Tpat_variant(lab1, _, _) if lab1 == lab => Ok(rem.to_vec()),
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for constant variants.
/// Equivalent to OCaml's `make_variant_matching_constant`.
fn make_variant_matching_constant(
    p: &Pattern,
    lab: &str,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &MatchArgs,
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_variant_matching_constant"),
        Some(_) => {
            let lab_owned = lab.to_string();
            let def = make_default(&|p2, rem| matcher_variant_const(&lab_owned, p2, rem), def);
            let ctx = filter_ctx(None, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: args.tail(1),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Matcher for non-constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_nonconst`.
fn matcher_variant_nonconst(
    lab: &str,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_variant(lab1, Some(arg), _) if lab1 == lab => {
            let mut result = vec![(**arg).clone()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for non-constant variants.
/// Equivalent to OCaml's `make_variant_matching_nonconst`.
fn make_variant_matching_nonconst(
    p: &Pattern,
    lab: &str,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &MatchArgs,
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_variant_matching_nonconst"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let lab_owned = lab.to_string();
            let def = make_default(
                &|p2, rem| matcher_variant_nonconst(&lab_owned, p2, rem),
                def,
            );
            let ctx = filter_ctx(None, p, ctx);
            let mut new_args = vec![(
                RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                    args: vec![arg.clone()],
                    loc: Location::none(),
                }),
                LetKind::Alias,
            )];
            new_args.extend(argl.iter().cloned());
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: MatchArgs::new(new_args),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by variant tag.
/// Equivalent to OCaml's `divide_variant`.
fn divide_variant(
    ctx_ref: &TypeContext,
    row: &RowDesc,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<((String, bool), MatchCell)> {
    let row = btype::row_repr(ctx_ref, row);

    fn divide_rec(
        ctx_ref: &TypeContext,
        row: &RowDesc,
        cases: &[Clause],
        def: &DefaultEnv,
        ctx: &[Ctx],
        al: &MatchArgs,
    ) -> Vec<((String, bool), MatchCell)> {
        match cases.split_first() {
            Some(((patl, action), rem)) => {
                match patl.split_first() {
                    Some((p, rest_patl)) => {
                        match &p.pat_desc {
                            PatternDesc::Tpat_variant(lab, pato, _) => {
                                let variants = divide_rec(ctx_ref, row, rem, def, ctx, al);

                                // Check if this label is absent in the row
                                let is_absent = match row.row_fields.iter().find(|(l, _)| l == lab)
                                {
                                    Some((_, field)) => {
                                        matches!(
                                            btype::row_field_repr(ctx_ref, field),
                                            RowField::Rabsent
                                        )
                                    }
                                    None => true,
                                };

                                if is_absent {
                                    return variants;
                                }

                                let eq_key = |a: &(String, bool), b: &(String, bool)| a == b;

                                match pato {
                                    None => {
                                        let key = (lab.clone(), true);
                                        add(
                                            |a| make_variant_matching_constant(p, lab, def, ctx, a),
                                            variants,
                                            eq_key,
                                            key,
                                            (rest_patl.to_vec(), action.clone()),
                                            al,
                                        )
                                    }
                                    Some(pat_inner) => {
                                        let key = (lab.clone(), false);
                                        let mut new_patl = vec![(**pat_inner).clone()];
                                        new_patl.extend(rest_patl.iter().cloned());
                                        add(
                                            |a| make_variant_matching_nonconst(p, lab, def, ctx, a),
                                            variants,
                                            eq_key,
                                            key,
                                            (new_patl, action.clone()),
                                            al,
                                        )
                                    }
                                }
                            }
                            _ => Vec::new(),
                        }
                    }
                    None => Vec::new(),
                }
            }
            None => Vec::new(),
        }
    }

    divide_rec(ctx_ref, &row, &pm.cases, &pm.default, ctx, &pm.args)
}

// --- Variables (lines 1370-1378) ---

/// Get the arguments from a variable pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_var`.
fn get_args_var(_p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    rem.to_vec()
}

/// Matcher version of get_args_var for make_default.
fn matcher_get_args_var(_p: &Pattern, rem: &[Pattern]) -> Result<Vec<Pattern>, MatchError> {
    Ok(rem.to_vec())
}

/// Make a variable matching.
/// Equivalent to OCaml's `make_var_matching`.
fn make_var_matching(def: &DefaultEnv, args: &MatchArgs) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_var_matching"),
        Some(_) => PatternMatching {
            cases: Vec::new(),
            args: args.tail(1),
            default: make_default(&matcher_get_args_var, def),
        },
    }
}

/// Divide a pattern matching by variable.
/// Equivalent to OCaml's `divide_var`.
fn divide_var(ctx: &[Ctx], pm: &PatternMatching) -> MatchCell {
    divide_line(
        ctx_lshift,
        make_var_matching,
        get_args_var,
        omega(),
        ctx,
        pm,
    )
}

// --- Tuples (lines 1382-1413) ---

/// Get the arguments from a tuple pattern.
/// Equivalent to OCaml's `get_args_tuple`.
fn get_args_tuple(arity: usize, p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_tuple(args) => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_tuple: not a tuple or any pattern"),
    }
}

/// Matcher for tuple patterns.
/// Equivalent to OCaml's `matcher_tuple`.
fn matcher_tuple(arity: usize, p: &Pattern, rem: &[Pattern]) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) if args.len() == arity => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a tuple matching.
/// Equivalent to OCaml's `make_tuple_matching`.
fn make_tuple_matching(
    loc: Location,
    arity: usize,
    def: &DefaultEnv,
    args: &MatchArgs,
) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_tuple_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let mut new_args = Vec::new();
            for pos in 0..arity {
                new_args.push((
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pfield(pos as i32, FieldDbgInfo::Tuple),
                        args: vec![arg.clone()],
                        loc: loc.clone(),
                    }),
                    LetKind::Alias,
                ));
            }
            new_args.extend(argl.iter().cloned());
            PatternMatching {
                cases: Vec::new(),
                args: MatchArgs::new(new_args),
                default: make_default(&|p2, rem| matcher_tuple(arity, p2, rem), def),
            }
        }
    }
}

/// Divide a pattern matching by tuple.
/// Equivalent to OCaml's `divide_tuple`.
fn divide_tuple(
    arena: &ParseArena,
    arity: usize,
    p: &Pattern,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> MatchCell {
    divide_line(
        |c| filter_ctx(None, p, c),
        |def, args| make_tuple_matching(arena.to_location(p.pat_loc), arity, def, args),
        |pat, rem| get_args_tuple(arity, pat, rem),
        p.clone(),
        ctx,
        pm,
    )
}

// --- Records (lines 1417-1476) ---

/// Build a list of patterns for record matching, filling in omegas for missing fields.
/// Equivalent to OCaml's `record_matching_line`.
fn record_matching_line(
    num_fields: usize,
    lbl_pat_list: &[(impl std::any::Any, LabelDescription, Pattern, bool)],
) -> Vec<Pattern> {
    let mut patv: Vec<Pattern> = (0..num_fields).map(|_| omega()).collect();
    for (_, lbl, pat, _) in lbl_pat_list {
        patv[lbl.lbl_pos as usize] = pat.clone();
    }
    patv
}

/// Build a record matching line from a Tpat_record pattern's fields.
/// This version takes the typed record fields directly.
fn record_matching_line_from_fields(
    num_fields: usize,
    fields: &[(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        LabelDescription,
        Pattern,
        bool,
    )],
) -> Vec<Pattern> {
    // Determine the actual size needed: max of num_fields and any label position + 1.
    let max_pos = fields
        .iter()
        .map(|(_, lbl, _, _)| lbl.lbl_pos as usize + 1)
        .max()
        .unwrap_or(0);
    let size = std::cmp::max(num_fields, max_pos);
    let mut patv: Vec<Pattern> = (0..size).map(|_| omega()).collect();
    for (_, lbl, pat, _) in fields {
        patv[lbl.lbl_pos as usize] = pat.clone();
    }
    patv
}

/// Get the arguments from a record pattern.
/// Equivalent to OCaml's `get_args_record`.
fn get_args_record(num_fields: usize, p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = record_matching_line_from_fields(num_fields, &[]);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_record(lbl_pat_list, _, _) => {
            let mut result = record_matching_line_from_fields(num_fields, lbl_pat_list);
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_record: not a record or any pattern"),
    }
}

/// Matcher for record patterns.
/// Equivalent to OCaml's `matcher_record`.
fn matcher_record(
    num_fields: usize,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = record_matching_line_from_fields(num_fields, &[]);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_record(fields, _, _) if fields.is_empty() && num_fields == 0 => {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_record(lbl_pat_list, _, _) => {
            // Check that the first label's lbl_all length matches num_fields.
            // In OCaml: Array.length lbl.lbl_all = num_fields
            // In Rust, lbl_all is a LabelArrayRef placeholder. We check using
            // the all_labels array passed to divide_record instead.
            // For the matcher, we trust the caller's num_fields is correct.
            if !lbl_pat_list.is_empty() {
                let mut result = record_matching_line_from_fields(num_fields, lbl_pat_list);
                result.extend(rem.iter().cloned());
                Ok(result)
            } else {
                Err(MatchError::NoMatch)
            }
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a record matching.
/// Equivalent to OCaml's `make_record_matching`.
fn make_record_matching(
    loc: Location,
    all_labels: &[LabelDescription],
    def: &DefaultEnv,
    args: &MatchArgs,
) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_record_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let mut new_args = Vec::new();
            for lbl in all_labels.iter() {
                let access = match &lbl.lbl_repres {
                    RecordRepresentation::RecordFloatUnused => {
                        panic!("Record_float_unused")
                    }
                    RecordRepresentation::RecordRegular => RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pfield(lbl.lbl_pos, fld_record(lbl)),
                        args: vec![arg.clone()],
                        loc: loc.clone(),
                    }),
                    RecordRepresentation::RecordInlined { .. } => RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pfield(lbl.lbl_pos, fld_record_inline(lbl)),
                        args: vec![arg.clone()],
                        loc: loc.clone(),
                    }),
                    RecordRepresentation::RecordUnboxed(_) => arg.clone(),
                    RecordRepresentation::RecordExtension => RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pfield(lbl.lbl_pos + 1, fld_record_extension(lbl)),
                        args: vec![arg.clone()],
                        loc: loc.clone(),
                    }),
                };
                let str_kind = match lbl.lbl_mut {
                    MutableFlag::Immutable => LetKind::Alias,
                    MutableFlag::Mutable => LetKind::StrictOpt,
                };
                new_args.push((access, str_kind));
            }
            new_args.extend(argl.iter().cloned());
            let nfields = all_labels.len();
            let def = make_default(&|p2, rem| matcher_record(nfields, p2, rem), def);
            PatternMatching {
                cases: Vec::new(),
                args: MatchArgs::new(new_args),
                default: def,
            }
        }
    }
}

/// Divide a pattern matching by record fields.
/// Equivalent to OCaml's `divide_record`.
fn divide_record(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    all_labels: &[LabelDescription],
    p: &Pattern,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> MatchCell {
    let num_fields = all_labels.len();
    divide_line(
        |c| filter_ctx(Some(ctx_ref), p, c),
        |def, args| make_record_matching(arena.to_location(p.pat_loc), all_labels, def, args),
        |pat, rem| get_args_record(num_fields, pat, rem),
        p.clone(),
        ctx,
        pm,
    )
}

// --- Arrays (lines 1480-1516) ---

/// Get the key (length) from an array pattern.
/// Equivalent to OCaml's `get_key_array`.
fn get_key_array(p: &Pattern) -> usize {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => patl.len(),
        _ => panic!("get_key_array: not an array pattern"),
    }
}

/// Get the arguments from an array pattern.
/// Equivalent to OCaml's `get_args_array`.
fn get_args_array(p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => {
            let mut result = patl.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_array: not an array pattern"),
    }
}

/// Matcher for array patterns.
/// Equivalent to OCaml's `matcher_array`.
fn matcher_array(len: usize, p: &Pattern, rem: &[Pattern]) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_array(args) if args.len() == len => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(len);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make an array matching cell.
/// Equivalent to OCaml's `make_array_matching`.
fn make_array_matching(p: &Pattern, def: &DefaultEnv, ctx: &[Ctx], args: &MatchArgs) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_array_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let len = get_key_array(p);
            let mut new_args = Vec::new();
            for pos in 0..len {
                new_args.push((
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Parrayrefu,
                        args: vec![
                            arg.clone(),
                            RawLambda::Lconst(crate::lambda::Constant::Int {
                                i: pos as i32,
                                comment: None,
                            }),
                        ],
                        loc: Location::none(),
                    }),
                    LetKind::StrictOpt,
                ));
            }
            new_args.extend(argl.iter().cloned());
            let def = make_default(&|p2, rem| matcher_array(len, p2, rem), def);
            let ctx = filter_ctx(None, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: MatchArgs::new(new_args),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by array length.
/// Equivalent to OCaml's `divide_array`.
fn divide_array(ctx: &[Ctx], pm: &PatternMatching) -> Vec<(usize, MatchCell)> {
    divide(
        make_array_matching,
        |a, b| a == b,
        get_key_array,
        get_args_array,
        ctx,
        pm,
    )
}

// ============================================================================
// Layer 7: String matching — OCaml matching.ml lines 1532-1659
// ============================================================================

/// Threshold for switching from dichotomic tree to sequential tests.
/// Equivalent to OCaml's `strings_test_threshold`.
const STRINGS_TEST_THRESHOLD: usize = 8;

/// Bind a switch argument to a variable if it's not already a variable.
/// Equivalent to OCaml's `bind_sw`.
fn bind_sw(
    ctx_ref: &TypeContext,
    arg: RawLambda,
    k: impl FnOnce(RawLambda) -> RawLambda,
) -> RawLambda {
    match &arg {
        RawLambda::Lvar(_) => k(arg),
        _ => {
            let id = ctx_ref.create_ident("switch");
            let var = RawLambda::Lvar(id.clone());
            let body = k(var);
            RawLambda::Llet(LetKind::Strict, id, Box::new(arg), Box::new(body))
        }
    }
}

/// Build a sequential string equality test sequence.
/// Equivalent to OCaml's `make_string_test_sequence`.
fn make_string_test_sequence(
    ctx_ref: &TypeContext,
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
) -> RawLambda {
    let (d, sw) = match d {
        None => {
            let mut sw = sw;
            assert!(!sw.is_empty());
            let (_, d) = sw.remove(0);
            (d, sw)
        }
        Some(d) => (d, sw),
    };
    bind_sw(ctx_ref, arg, |arg| {
        // fold_right: iterate from the end
        let mut result = d;
        for (s, lam) in sw.into_iter().rev() {
            result = RawLambda::LifThenElse(
                Box::new(RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pstringcomp(Comparison::Neq),
                    args: vec![
                        arg.clone(),
                        RawLambda::Lconst(crate::lambda::Constant::ImmString(s)),
                    ],
                    loc: loc.clone(),
                })),
                Box::new(result),
                Box::new(lam),
            );
        }
        result
    })
}

/// Split a list into three parts: before middle, middle element, after middle.
/// Equivalent to OCaml's `split`.
fn split<T>(k: usize, xs: Vec<T>) -> (Vec<T>, T, Vec<T>) {
    assert!(!xs.is_empty());
    let mut iter = xs.into_iter();
    if k <= 1 {
        let x0 = iter.next().unwrap();
        let rest: Vec<T> = iter.collect();
        (Vec::new(), x0, rest)
    } else {
        let x0 = iter.next().unwrap();
        let rest: Vec<T> = iter.collect();
        let (mut xs, y0, ys) = split(k - 2, rest);
        xs.insert(0, x0);
        (xs, y0, ys)
    }
}

/// Zero lambda constant.
/// Equivalent to OCaml's `zero_lam`.
fn zero_lam() -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::int(0))
}

/// Three-way test on an integer value (less than, equal, greater than zero).
/// Equivalent to OCaml's `tree_way_test`.
fn tree_way_test(
    loc: Location,
    arg: RawLambda,
    lt: RawLambda,
    eq: RawLambda,
    gt: RawLambda,
) -> RawLambda {
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Lt),
            args: vec![arg.clone(), zero_lam()],
            loc: loc.clone(),
        })),
        Box::new(lt),
        Box::new(RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Lt),
                args: vec![zero_lam(), arg],
                loc,
            })),
            Box::new(gt),
            Box::new(eq),
        )),
    )
}

/// Build a dichotomic string test tree.
/// Equivalent to OCaml's `do_make_string_test_tree`.
fn do_make_string_test_tree(
    ctx_ref: &TypeContext,
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    delta: usize,
    d: Option<RawLambda>,
) -> RawLambda {
    let len = sw.len();
    if len <= STRINGS_TEST_THRESHOLD + delta {
        make_string_test_sequence(ctx_ref, loc, arg, sw, d)
    } else {
        let (lt, (s, act), gt) = split(len, sw);
        bind_sw(
            ctx_ref,
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pstringcomp(Comparison::Eq),
                args: vec![
                    arg.clone(),
                    RawLambda::Lconst(crate::lambda::Constant::ImmString(s)),
                ],
                loc: loc.clone(),
            }),
            |r| {
                tree_way_test(
                    loc.clone(),
                    r,
                    do_make_string_test_tree(
                        ctx_ref,
                        loc.clone(),
                        arg.clone(),
                        lt,
                        delta,
                        d.clone(),
                    ),
                    act,
                    do_make_string_test_tree(
                        ctx_ref,
                        loc.clone(),
                        arg.clone(),
                        gt,
                        delta,
                        d.clone(),
                    ),
                )
            },
        )
    }
}

/// Expand a string switch into a test tree.
/// Entry point for string matching.
/// Equivalent to OCaml's `expand_stringswitch`.
pub fn expand_stringswitch(
    ctx_ref: &TypeContext,
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> RawLambda {
    match d {
        None => bind_sw(ctx_ref, arg, |arg| {
            do_make_string_test_tree(ctx_ref, loc, arg, sw, 0, None)
        }),
        Some(e) => bind_sw(ctx_ref, arg, |arg| {
            make_catch(e, next_raise_count, |d| {
                do_make_string_test_tree(ctx_ref, loc, arg, sw, 1, Some(d))
            })
        }),
    }
}

// ============================================================================
// Generic test trees — Sharing (OCaml matching.ml lines 1609-1659)
// ============================================================================

/// Process shared actions for tree-based matching.
/// Returns `(wrapper_fn, processed_sw, processed_d)`.
/// The wrapper_fn wraps the result with catch handlers.
///
/// Equivalent to OCaml's `share_actions_tree`.
fn share_actions_tree(
    sw: Vec<(Constant, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> (
    Vec<(i32, RawLambda)>,
    Vec<(Constant, RawLambda)>,
    Option<RawLambda>,
) {
    let mut store = StoreExp::mk_store();

    // Default action is always shared
    let d_idx = d.map(|d| store.act_store_shared(d));

    // Store all other actions
    let sw_indices: Vec<(Constant, usize)> = sw
        .into_iter()
        .map(|(cst, act)| (cst, store.act_store(act)))
        .collect();

    // Retrieve all actions, including potential default
    let acts = store.act_get_shared();

    // Process shared actions — OCaml's handle_shared
    let mut handlers: Vec<(i32, Box<dyn FnOnce(RawLambda) -> RawLambda>)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a, next_raise_count);
                handlers.push((i, h));
                make_exit(i)
            }
        })
        .collect();

    let mut use_counts = vec![0usize; resolved_acts.len()];
    if let Some(idx) = d_idx {
        use_counts[idx] += 1;
    }
    for (_, idx) in &sw_indices {
        use_counts[*idx] += 1;
    }
    let mut resolved_acts = resolved_acts.into_iter().map(Some).collect::<Vec<_>>();

    // Reconstruct default and switch list
    let d = d_idx.map(|idx| materialize_resolved_action(&mut resolved_acts, &use_counts, idx));
    let sw: Vec<(Constant, RawLambda)> = sw_indices
        .into_iter()
        .map(|(cst, j)| {
            (
                cst,
                materialize_resolved_action(&mut resolved_acts, &use_counts, j),
            )
        })
        .collect();

    // Extract only the actual catch handlers. When the wrapper is identity
    // (the shared action is already a simple exit), there is no handler to reapply.
    let handler_pairs: Vec<(i32, RawLambda)> = handlers
        .into_iter()
        .filter_map(|(i, h)| match h(make_exit(i)) {
            RawLambda::LstaticRaise(j, args) if j == i && args.is_empty() => None,
            handler => Some((i, handler)),
        })
        .collect();

    (handler_pairs, sw, d)
}

/// Apply handler wrappers to a result lambda.
/// The handlers are applied in forward order (first handler = innermost).
/// Equivalent to OCaml's `!hs result`.
fn apply_handlers(mut result: RawLambda, handlers: Vec<(i32, RawLambda)>) -> RawLambda {
    // OCaml composes: hs := fun act -> h(ohs(act))
    // First handler added is innermost, last is outermost.
    // Each wrapper h wraps the body in LstaticCatch(body, (i,[]), handler_body).
    // So iterating forward: first handler wraps result first (innermost),
    // then each subsequent handler wraps around (outermost).
    for (exit_id, handler) in handlers.into_iter() {
        match &result {
            RawLambda::LstaticRaise(j, args) if *j == exit_id && args.is_empty() => {
                result = handler;
            }
            _ => {
                result = RawLambda::LstaticCatch(
                    Box::new(result),
                    (exit_id, Vec::new()),
                    Box::new(handler),
                );
            }
        }
    }
    result
}

/// Remove duplicate entries from a sorted (constant, lambda) list.
/// Keeps the first occurrence of each constant.
/// Equivalent to OCaml's `uniq_lambda_list`.
fn uniq_lambda_list(sw: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    if sw.len() <= 1 {
        return sw;
    }
    let mut result: Vec<(Constant, RawLambda)> = Vec::new();
    let mut iter = sw.into_iter();
    let first = iter.next().unwrap();
    result.push(first);
    for (c2, lam2) in iter {
        let last_c = &result.last().unwrap().0;
        if const_compare(last_c, &c2) == std::cmp::Ordering::Equal {
            // Duplicate — skip (keep the first, which is already in result)
            // OCaml keeps p1 (first) and drops the second
        } else {
            result.push((c2, lam2));
        }
    }
    result
}

/// Sort a (constant, lambda) list by constant value, then remove duplicates.
/// Equivalent to OCaml's `sort_lambda_list`.
fn sort_lambda_list(mut l: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    l.sort_by(|(x, _), (y, _)| const_compare(x, y));
    uniq_lambda_list(l)
}

// ============================================================================
// Layer 8: Integer/switch matching — OCaml matching.ml lines 1661-1941
// ============================================================================

/// Cut a list at position n, returning (first_n_elements, rest).
/// Equivalent to OCaml's `cut`.
fn cut<T>(n: usize, l: Vec<T>) -> (Vec<T>, Vec<T>) {
    if n == 0 {
        return (Vec::new(), l);
    }
    assert!(!l.is_empty(), "cut: list too short");
    let mut iter = l.into_iter();
    let mut first = Vec::with_capacity(n);
    for _ in 0..n {
        first.push(iter.next().expect("cut: list too short"));
    }
    let rest: Vec<T> = iter.collect();
    (first, rest)
}

/// Sequential equality tests with a fail action.
/// Equivalent to OCaml's `do_tests_fail`.
fn do_tests_fail(
    loc: Location,
    fail: RawLambda,
    tst: Primitive,
    arg: RawLambda,
    cases: &[(Constant, RawLambda)],
) -> RawLambda {
    if cases.is_empty() {
        return fail;
    }
    let (c, act) = &cases[0];
    let rest = &cases[1..];
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: tst.clone(),
            args: vec![arg.clone(), typed_const_to_lambda_const(c)],
            loc: loc.clone(),
        })),
        Box::new(do_tests_fail(loc, fail, tst, arg, rest)),
        Box::new(act.clone()),
    )
}

fn do_tests_fail_owned(
    loc: Location,
    fail: RawLambda,
    tst: Primitive,
    arg: RawLambda,
    cases: Vec<(Constant, RawLambda)>,
) -> RawLambda {
    // OCaml compiler/ml/matching.ml:1761-1833 receives immutable action
    // pointers from `share_actions_tree`. `materialize_resolved_action` above
    // has already converted single-use Rust actions back to owned lambdas, so
    // build the same right-associated test chain while moving those actions
    // into place instead of recursively cloning them.
    cases.into_iter().rev().fold(fail, |acc, (c, act)| {
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: tst.clone(),
                args: vec![arg.clone(), typed_const_to_lambda_const(&c)],
                loc: loc.clone(),
            })),
            Box::new(acc),
            Box::new(act),
        )
    })
}

/// Sequential equality tests without a fail action.
/// Equivalent to OCaml's `do_tests_nofail`.
fn do_tests_nofail(
    loc: Location,
    tst: Primitive,
    arg: RawLambda,
    cases: &[(Constant, RawLambda)],
) -> RawLambda {
    assert!(!cases.is_empty(), "Matching.do_tests_nofail");
    if cases.len() == 1 {
        return cases[0].1.clone();
    }
    let (c, act) = &cases[0];
    let rest = &cases[1..];
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: tst.clone(),
            args: vec![arg.clone(), typed_const_to_lambda_const(c)],
            loc: loc.clone(),
        })),
        Box::new(do_tests_nofail(loc, tst, arg, rest)),
        Box::new(act.clone()),
    )
}

fn do_tests_nofail_owned(
    loc: Location,
    tst: Primitive,
    arg: RawLambda,
    mut cases: Vec<(Constant, RawLambda)>,
) -> RawLambda {
    assert!(!cases.is_empty(), "Matching.do_tests_nofail");
    let (_, last_action) = cases
        .pop()
        .expect("checked non-empty constant test sequence");
    // Same branch shape as `do_tests_nofail`: for [c1->a1; c2->a2],
    // emit `if c1 then a2 else a1`. See compiler/ml/matching.ml:1761-1833.
    cases.into_iter().rev().fold(last_action, |acc, (c, act)| {
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: tst.clone(),
                args: vec![arg.clone(), typed_const_to_lambda_const(&c)],
                loc: loc.clone(),
            })),
            Box::new(acc),
            Box::new(act),
        )
    })
}

/// Convert a typedtree constant to a lambda constant wrapped in Lconst.
/// Equivalent to OCaml's `Lconst(Const_base c)`.
fn typed_const_to_lambda_const(c: &Constant) -> RawLambda {
    let lc = match c {
        Constant::Int(i) => crate::lambda::Constant::int(*i as i32),
        Constant::Char(c) => crate::lambda::Constant::Char(*c),
        Constant::String(s, _) => crate::lambda::Constant::String {
            s: s.clone(),
            delim: None,
        },
        Constant::Float(f) => crate::lambda::Constant::Float(f.clone()),
        Constant::BigInt(positive, v) => crate::lambda::Constant::BigInt {
            negative: !*positive,
            value: v.clone(),
        },
    };
    RawLambda::Lconst(lc)
}

/// Build a test sequence for constant matching.
/// Uses dichotomic splitting when there are enough cases and a less-than test is available.
/// Equivalent to OCaml's `make_test_sequence`.
fn make_test_sequence(
    loc: Location,
    fail: Option<RawLambda>,
    tst: Primitive,
    lt_tst: Primitive,
    arg: RawLambda,
    const_lambda_list: Vec<(Constant, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let const_lambda_list = sort_lambda_list(const_lambda_list);
    let (handlers, const_lambda_list, fail) =
        share_actions_tree(const_lambda_list, fail, next_raise_count);

    fn make_test_seq_inner(
        loc: &Location,
        fail: &Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        const_lambda_list: &[(Constant, RawLambda)],
    ) -> RawLambda {
        if const_lambda_list.len() >= 4 && !matches!(lt_tst, Primitive::Pignore) {
            split_sequence(loc, fail, tst, lt_tst, arg, const_lambda_list)
        } else {
            match fail {
                None => do_tests_nofail(loc.clone(), tst.clone(), arg.clone(), const_lambda_list),
                Some(fail) => do_tests_fail(
                    loc.clone(),
                    fail.clone(),
                    tst.clone(),
                    arg.clone(),
                    const_lambda_list,
                ),
            }
        }
    }

    fn make_test_seq_inner_owned(
        loc: &Location,
        fail: Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        mut const_lambda_list: Vec<(Constant, RawLambda)>,
    ) -> RawLambda {
        if const_lambda_list.len() >= 4 && !matches!(lt_tst, Primitive::Pignore) {
            let mid = const_lambda_list.len() / 2;
            let list2 = const_lambda_list.split_off(mid);
            let pivot_const = &list2[0].0;
            RawLambda::LifThenElse(
                Box::new(RawLambda::Lprim(RawPrimInfo {
                    primitive: lt_tst.clone(),
                    args: vec![arg.clone(), typed_const_to_lambda_const(pivot_const)],
                    loc: loc.clone(),
                })),
                Box::new(make_test_seq_inner_owned(
                    loc,
                    fail.clone(),
                    tst,
                    lt_tst,
                    arg,
                    const_lambda_list,
                )),
                Box::new(make_test_seq_inner_owned(
                    loc, fail, tst, lt_tst, arg, list2,
                )),
            )
        } else {
            match fail {
                None => {
                    do_tests_nofail_owned(loc.clone(), tst.clone(), arg.clone(), const_lambda_list)
                }
                Some(fail) => do_tests_fail_owned(
                    loc.clone(),
                    fail,
                    tst.clone(),
                    arg.clone(),
                    const_lambda_list,
                ),
            }
        }
    }

    fn split_sequence(
        loc: &Location,
        fail: &Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        const_lambda_list: &[(Constant, RawLambda)],
    ) -> RawLambda {
        let mid = const_lambda_list.len() / 2;
        let (list1, list2) = const_lambda_list.split_at(mid);
        let pivot_const = &list2[0].0;
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: lt_tst.clone(),
                args: vec![arg.clone(), typed_const_to_lambda_const(pivot_const)],
                loc: loc.clone(),
            })),
            Box::new(make_test_seq_inner(loc, fail, tst, lt_tst, arg, list1)),
            Box::new(make_test_seq_inner(loc, fail, tst, lt_tst, arg, list2)),
        )
    }

    let result = make_test_seq_inner_owned(&loc, fail, &tst, &lt_tst, &arg, const_lambda_list);
    apply_handlers(result, handlers)
}

// ============================================================================
// SArg module — Switch module arguments (OCaml matching.ml lines 1708-1758)
// ============================================================================
// The SArg module in OCaml provides the primitives needed by Switch.Make.
// In Rust, the switch.rs module already has these functions built in.
// The functions below provide matching.ml-level wrappers.

/// SArg: make a primitive application.
/// Equivalent to OCaml's `SArg.make_prim`.
fn sarg_make_prim(p: Primitive, args: Vec<RawLambda>) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: p,
        args,
        loc: Location::none(),
    })
}

/// SArg: add an offset to an argument.
/// Equivalent to OCaml's `SArg.make_offset`.
fn sarg_make_offset(arg: RawLambda, n: i32) -> RawLambda {
    if n == 0 {
        arg
    } else {
        RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Poffsetint(n),
            args: vec![arg],
            loc: Location::none(),
        })
    }
}

/// SArg: bind a variable.
/// Equivalent to OCaml's `SArg.bind`.
fn sarg_bind(arg: RawLambda, body: impl FnOnce(RawLambda) -> RawLambda) -> RawLambda {
    match &arg {
        RawLambda::Lvar(v) => {
            let newarg = arg.clone();
            let result = body(newarg);
            RawLambda::Llet(LetKind::Alias, v.clone(), Box::new(arg), Box::new(result))
        }
        _ => {
            let newvar = Ident::create_local("switcher");
            let newarg = RawLambda::Lvar(newvar.clone());
            let result = body(newarg);
            RawLambda::Llet(LetKind::Alias, newvar, Box::new(arg), Box::new(result))
        }
    }
}

/// SArg: make a constant integer.
/// Equivalent to OCaml's `SArg.make_const`.
fn sarg_make_const(i: i32) -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::int(i))
}

/// SArg: make an `isout` test.
/// Equivalent to OCaml's `SArg.make_isout`.
fn sarg_make_isout(h: RawLambda, arg: RawLambda) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pisout(match &h {
            RawLambda::Lconst(crate::lambda::Constant::Int { i, .. }) => *i,
            _ => 0,
        }),
        args: vec![arg],
        loc: Location::none(),
    })
}

/// SArg: make an `isin` test.
/// Equivalent to OCaml's `SArg.make_isin`.
fn sarg_make_isin(h: RawLambda, arg: RawLambda) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pnot,
        args: vec![sarg_make_isout(h, arg)],
        loc: Location::none(),
    })
}

/// SArg: make an if-then-else.
/// Equivalent to OCaml's `SArg.make_if`.
fn sarg_make_if(cond: RawLambda, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    RawLambda::LifThenElse(Box::new(cond), Box::new(ifso), Box::new(ifnot))
}

/// SArg: make a switch.
/// Equivalent to OCaml's `SArg.make_switch`.
fn sarg_make_switch(
    _loc: Location,
    arg: RawLambda,
    cases: &[usize],
    acts: Vec<RawLambda>,
    offset: i32,
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
) -> RawLambda {
    let mut use_counts = vec![0usize; acts.len()];
    for &index in cases {
        use_counts[index] += 1;
    }
    let mut acts = acts.into_iter().map(Some).collect::<Vec<_>>();
    let mut l: Vec<(i32, RawLambda)> = Vec::new();
    for i in (0..cases.len()).rev() {
        l.push((
            offset + i as i32,
            materialize_resolved_action(&mut acts, &use_counts, cases[i]),
        ));
    }
    l.reverse();
    RawLambda::Lswitch(
        Box::new(arg),
        RawLambdaSwitch {
            sw_numconsts: cases.len(),
            sw_consts_full: false,
            sw_consts: l
                .into_iter()
                .map(|(key, action)| (crate::lambda::SwitchKey::Int(key), action))
                .collect(),
            sw_numblocks: 0,
            sw_blocks_full: false,
            sw_blocks: Vec::new(),
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Direct,
        },
        _loc,
    )
}

// ============================================================================
// Action sharing for Lswitch argument (OCaml matching.ml lines 1761-1833)
// ============================================================================

fn share_match_switch(
    sw_numconsts: usize,
    sw_consts_full: bool,
    sw_consts: Vec<(crate::lambda::SwitchKey, MatchCode)>,
    sw_numblocks: usize,
    sw_blocks_full: bool,
    sw_blocks: Vec<(crate::lambda::SwitchKey, MatchCode)>,
    sw_failaction: Option<MatchCode>,
    sw_dispatch: crate::lambda::SwitchDispatch,
    next_raise_count: &mut i32,
) -> (Vec<(i32, RawLambda)>, RawLambdaSwitch) {
    let mut store = MatchCodeStore::new();
    let fail = sw_failaction.map(|code| store.store(true, code));
    let consts: Vec<_> = sw_consts
        .into_iter()
        .map(|(key, code)| (key, store.store(false, code)))
        .collect();
    let blocks: Vec<_> = sw_blocks
        .into_iter()
        .map(|(key, code)| (key, store.store(false, code)))
        .collect();

    let mut handlers = Vec::new();
    let resolved: Vec<_> = store
        .get()
        .into_iter()
        .map(|stored| match stored {
            StoredMatchCode::Single(code) => code.into_raw(),
            StoredMatchCode::Shared(code) => {
                let raw = code.into_raw();
                let (exit, wrapper) = make_catch_delayed(raw, next_raise_count);
                let dummy = RawLambda::Lconst(crate::lambda::Constant::int(0));
                if let RawLambda::LstaticCatch(_, (caught, _), handler) = wrapper(dummy) {
                    handlers.push((caught, *handler));
                }
                make_exit(exit)
            }
        })
        .collect();

    let mut use_counts = vec![0usize; resolved.len()];
    if let Some(index) = fail {
        use_counts[index] += 1;
    }
    for (_, index) in &consts {
        use_counts[*index] += 1;
    }
    for (_, index) in &blocks {
        use_counts[*index] += 1;
    }
    let mut resolved = resolved.into_iter().map(Some).collect::<Vec<_>>();

    let failaction = fail.map(|index| {
        Box::new(materialize_resolved_action(
            &mut resolved,
            &use_counts,
            index,
        ))
    });
    let consts = consts
        .into_iter()
        .map(|(key, index)| {
            (
                key,
                materialize_resolved_action(&mut resolved, &use_counts, index),
            )
        })
        .collect();
    let blocks = blocks
        .into_iter()
        .map(|(key, index)| {
            (
                key,
                materialize_resolved_action(&mut resolved, &use_counts, index),
            )
        })
        .collect();

    (
        handlers,
        RawLambdaSwitch {
            sw_numconsts,
            sw_consts_full,
            sw_consts: consts,
            sw_numblocks,
            sw_blocks_full,
            sw_blocks: blocks,
            sw_failaction: failaction,
            sw_dispatch,
        },
    )
}

/// Deduplicate switch actions by wrapping shared actions in catch/exit.
/// Equivalent to OCaml's `share_actions_sw`.
pub fn share_actions_sw(
    sw: RawLambdaSwitch,
    next_raise_count: &mut i32,
) -> (Vec<(i32, RawLambda)>, RawLambdaSwitch) {
    let mut store = StoreExp::mk_store();

    // Store fail action as shared
    let RawLambdaSwitch {
        sw_numconsts,
        sw_consts_full,
        sw_consts,
        sw_numblocks,
        sw_blocks_full,
        sw_blocks,
        sw_failaction,
        sw_dispatch,
    } = sw;

    let fail_idx = sw_failaction.map(|fail| store.act_store_shared(*fail));

    // Store const and block actions
    let consts: Vec<(crate::lambda::SwitchKey, usize)> = sw_consts
        .into_iter()
        .map(|(i, e)| (i, store.act_store(e)))
        .collect();
    let blocks: Vec<(crate::lambda::SwitchKey, usize)> = sw_blocks
        .into_iter()
        .map(|(i, e)| (i, store.act_store(e)))
        .collect();

    // Get shared actions
    let acts = store.act_get_shared();

    // Process shared actions (handle_shared pattern)
    let mut handlers: Vec<(i32, RawLambda)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a, next_raise_count);
                // Extract handler body from the wrapper function
                let dummy = RawLambda::Lconst(crate::lambda::Constant::int(0));
                let wrapped = h(dummy);
                match wrapped {
                    RawLambda::LstaticCatch(_, (exit_id, _), handler) => {
                        handlers.push((exit_id, *handler));
                        make_exit(exit_id)
                    }
                    _ => {
                        // h was identity — the action is already a simple exit.
                        // Use the original action directly; the exit already
                        // targets an existing handler, no new wrapper needed.
                        make_exit(i)
                    }
                }
            }
        })
        .collect();

    let mut use_counts = vec![0usize; resolved_acts.len()];
    if let Some(idx) = fail_idx {
        use_counts[idx] += 1;
    }
    for (_, idx) in &consts {
        use_counts[*idx] += 1;
    }
    for (_, idx) in &blocks {
        use_counts[*idx] += 1;
    }
    let mut resolved_acts = resolved_acts.into_iter().map(Some).collect::<Vec<_>>();

    // Reconstruct fail
    let fail = fail_idx.map(|idx| {
        Box::new(materialize_resolved_action(
            &mut resolved_acts,
            &use_counts,
            idx,
        ))
    });

    let new_sw = RawLambdaSwitch {
        sw_numconsts,
        sw_consts_full,
        sw_consts: consts
            .into_iter()
            .map(|(i, j)| {
                (
                    i,
                    materialize_resolved_action(&mut resolved_acts, &use_counts, j),
                )
            })
            .collect(),
        sw_numblocks,
        sw_blocks_full,
        sw_blocks: blocks
            .into_iter()
            .map(|(i, j)| {
                (
                    i,
                    materialize_resolved_action(&mut resolved_acts, &use_counts, j),
                )
            })
            .collect(),
        sw_failaction: fail,
        sw_dispatch,
    };

    (handlers, new_sw)
}

/// Reintroduce fail action in switch argument.
/// When a static exit appears >= 3 times in the cases and there's no failaction,
/// extract it as the failaction to reduce switch size.
/// Equivalent to OCaml's `reintroduce_fail`.
pub fn reintroduce_fail(sw: RawLambdaSwitch) -> RawLambdaSwitch {
    if sw.sw_failaction.is_some() {
        return sw;
    }

    let mut counts: HashMap<i32, i32> = HashMap::new();
    let seen = |counts: &mut HashMap<i32, i32>, lam: &RawLambda| {
        if let Some(i) = as_simple_exit(lam) {
            let old = counts.get(&i).copied().unwrap_or(0);
            counts.insert(i, old + 1);
        }
    };

    for (_, l) in &sw.sw_consts {
        seen(&mut counts, l);
    }
    for (_, l) in &sw.sw_blocks {
        seen(&mut counts, l);
    }

    let mut i_max: i32 = -1;
    let mut max: i32 = -1;
    for (&i, &c) in &counts {
        if c > max || (c == max && i > i_max) {
            i_max = i;
            max = c;
        }
    }

    if max >= 3 {
        let default = i_max;
        fn remove<K>(ls: Vec<(K, RawLambda)>, default: i32) -> Vec<(K, RawLambda)> {
            ls.into_iter()
                .filter(|(_, lam)| match as_simple_exit(lam) {
                    Some(j) => j != default,
                    None => true,
                })
                .collect()
        }
        RawLambdaSwitch {
            sw_numconsts: sw.sw_numconsts,
            sw_consts_full: sw.sw_consts_full,
            sw_consts: remove(sw.sw_consts, default),
            sw_numblocks: sw.sw_numblocks,
            sw_blocks_full: sw.sw_blocks_full,
            sw_blocks: remove(sw.sw_blocks, default),
            sw_failaction: Some(Box::new(make_exit(default))),
            sw_dispatch: sw.sw_dispatch,
        }
    } else {
        sw
    }
}

// ============================================================================
// Switcher = Switch.Make(SArg) — uses switch.rs (OCaml matching.ml line 1835)
// ============================================================================

// The Switcher module is already ported in switch.rs.
// The following functions provide the matching.ml-level interface.

/// Get the last key from a sorted list of (int, lambda) pairs.
/// Equivalent to OCaml's `last`.
fn last_key(def: i32, l: &[(i32, RawLambda)]) -> i32 {
    match l.last() {
        None => def,
        Some((x, _)) => *x,
    }
}

/// Get the edge values (low, high) from a sorted list.
/// Equivalent to OCaml's `get_edges`.
fn get_edges(low: i32, high: i32, l: &[(i32, RawLambda)]) -> (i32, i32) {
    match l.first() {
        None => (low, high),
        Some((x, _)) => (*x, last_key(high, l)),
    }
}

/// Convert a sorted int-lambda list with a fail action into intervals.
/// Equivalent to OCaml's `as_interval_canfail`.
fn as_interval_canfail(
    fail: RawLambda,
    low: i32,
    high: i32,
    l: &[(i32, RawLambda)],
) -> (Vec<(i32, i32, usize)>, StoreExp) {
    let mut store = StoreExp::mk_store();

    let fail_idx = store.act_store(fail);
    assert_eq!(fail_idx, 0); // fail has action index 0

    fn nofail_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            if cur_high == high {
                vec![(cur_low, cur_high, cur_act)]
            } else {
                vec![(cur_low, cur_high, cur_act), (cur_high + 1, high, 0)]
            }
        } else {
            let (i, ref act_i) = rest[0];
            let act_index = store.act_store(act_i.clone());
            if cur_high + 1 == i {
                if act_index == cur_act {
                    nofail_rec(cur_low, i, cur_act, &rest[1..], high, store)
                } else if act_index == 0 {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(fail_rec(i, i, &rest[1..], high, store));
                    r
                } else {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                    r
                }
            } else if act_index == 0 {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(fail_rec(cur_high + 1, cur_high + 1, rest, high, store));
                r
            } else {
                let mut r = vec![(cur_low, cur_high, cur_act), (cur_high + 1, i - 1, 0)];
                r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                r
            }
        }
    }

    fn fail_rec(
        cur_low: i32,
        cur_high: i32,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, 0)]
        } else {
            let (i, ref act_i) = rest[0];
            let index = store.act_store(act_i.clone());
            if index == 0 {
                fail_rec(cur_low, i, &rest[1..], high, store)
            } else {
                let mut r = vec![(cur_low, i - 1, 0)];
                r.extend(nofail_rec(i, i, index, &rest[1..], high, store));
                r
            }
        }
    }

    let intervals = if l.is_empty() {
        vec![(low, high, 0)]
    } else {
        let (i, ref act_i) = l[0];
        let index = store.act_store(act_i.clone());
        if index == 0 {
            fail_rec(low, i, &l[1..], high, &mut store)
        } else if low < i {
            let mut r = vec![(low, i - 1, 0)];
            r.extend(nofail_rec(i, i, index, &l[1..], high, &mut store));
            r
        } else {
            nofail_rec(i, i, index, &l[1..], high, &mut store)
        }
    };

    (intervals, store)
}

/// Convert a sorted int-lambda list (no fail action) into intervals.
/// Equivalent to OCaml's `as_interval_nofail`.
fn as_interval_nofail(l: &[(i32, RawLambda)]) -> (Vec<(i32, i32, usize)>, StoreExp) {
    let mut store = StoreExp::mk_store();

    fn some_hole(l: &[(i32, RawLambda)]) -> bool {
        if l.len() <= 1 {
            return false;
        }
        l.windows(2).any(|w| w[1].0 > w[0].0 + 1)
    }

    fn i_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, cur_act)]
        } else {
            let (i, ref act) = rest[0];
            let act_index = store.act_store(act.clone());
            if act_index == cur_act {
                i_rec(cur_low, i, cur_act, &rest[1..], store)
            } else {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(i_rec(i, i, act_index, &rest[1..], store));
                r
            }
        }
    }

    assert!(!l.is_empty());
    let (i, ref act) = l[0];
    let has_hole = some_hole(&l[1..]);
    let act_index = if has_hole {
        store.act_store_shared(act.clone())
    } else {
        store.act_store(act.clone())
    };
    assert_eq!(act_index, 0);
    let inters = i_rec(i, i, act_index, &l[1..], &mut store);

    (inters, store)
}

/// Sort an int-lambda list by key.
/// Equivalent to OCaml's `sort_int_lambda_list`.
fn sort_int_lambda_list(mut l: Vec<(i32, RawLambda)>) -> Vec<(i32, RawLambda)> {
    l.sort_by(|(i1, _), (i2, _)| i1.cmp(i2));
    l
}

/// Convert an int-lambda list into intervals for the switch compiler.
/// Equivalent to OCaml's `as_interval`.
fn as_interval(
    fail: Option<RawLambda>,
    low: i32,
    high: i32,
    l: Vec<(i32, RawLambda)>,
) -> ((i32, i32), (Vec<(i32, i32, usize)>, StoreExp)) {
    let l = sort_int_lambda_list(l);
    let edges = get_edges(low, high, &l);
    let result = match fail {
        None => as_interval_nofail(&l),
        Some(act) => as_interval_canfail(act, low, high, &l),
    };
    (edges, result)
}

/// Compile an integer switch using the switch module.
/// Equivalent to OCaml's `call_switcher`.
pub fn call_switcher(
    loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    low: i32,
    high: i32,
    int_lambda_list: Vec<(i32, RawLambda)>,
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let (edges, (cases, store)) = as_interval(fail, low, high, int_lambda_list);

    // Pass the existing action array through without re-storing it. The cases
    // above already contain indices into this exact array.
    let acts = store
        .act_get_shared()
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => crate::raw_lambda::switch::Shared::Single(a),
            SharedAction::Shared(a) => crate::raw_lambda::switch::Shared::Shared(a),
        })
        .collect();

    crate::raw_lambda::switch::zyva_with_shared_actions(
        loc,
        edges,
        arg,
        &cases,
        acts,
        sw_dispatch,
        &mut || bump_raise_count(next_raise_count, "matching::call_switcher"),
    )
}

// ============================================================================
// Layer 9: Combine functions — OCaml matching.ml lines 1945-2349
// ============================================================================

/// Construct a pattern by or-ing together a list of patterns.
/// Equivalent to OCaml's `list_as_pat`.
fn list_as_pat(pats: &[Pattern]) -> Pattern {
    match pats {
        [] => panic!("Matching.list_as_pat"),
        [pat] => pat.clone(),
        [pat, rest @ ..] => Pattern {
            pat_desc: PatternDesc::Tpat_or(
                Box::new(pat.clone()),
                Box::new(list_as_pat(rest)),
                None,
            ),
            ..pat.clone()
        },
    }
}

/// Complete the list of constructors not yet seen in the match.
/// Returns patterns for all constructors NOT in `pats`.
/// Equivalent to OCaml's `complete_pats_constrs`.
///
/// This requires environment lookups to get all constructors of a type.
/// We use a simplified approach: extract constructor info from the first pattern.
fn complete_pats_constrs(ctx_ref: &TypeContext, pats: &[Pattern]) -> Vec<Pattern> {
    match pats.first() {
        None => panic!("complete_pats_constrs: empty list"),
        Some(p) => {
            let cstr = pat_as_constr(p);

            if matches!(cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) {
                return Vec::new();
            }
            let seen_constrs: Vec<ConstructorDescription> =
                pats.iter().map(get_key_constr).collect();

            // Get all constructors of the type from the environment
            let env_opt = ctx_ref.get_typed_env(p.pat_env);
            let all_constrs: Vec<ConstructorDescription> = if let Some(env) = env_opt {
                // Try to find the type declaration and its constructors
                match &cstr.cstr_res {
                    ty => {
                        // Try to expand the type and find its constructors
                        get_variant_constructors_from_env(ctx_ref, env.as_ref(), *ty)
                    }
                }
            } else {
                Vec::new()
            };

            let mut others: Vec<_> = all_constrs
                .into_iter()
                .filter(|cnstr| {
                    !seen_constrs
                        .iter()
                        .any(|seen| same_constructor(cnstr, seen))
                })
                .collect();
            others.sort_by_key(|cnstr| cnstr.cstr_arity != 0);
            others.iter().map(|cnstr| pat_of_constr(p, cnstr)).collect()
        }
    }
}

/// Create a pattern from a constructor description, using the example pattern for type info.
/// Equivalent to OCaml's `pat_of_constr`.
fn pat_of_constr(ex_pat: &Pattern, cstr: &ConstructorDescription) -> Pattern {
    Pattern {
        pat_desc: PatternDesc::Tpat_construct(
            crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0), // dummy
                loc: LocIdx::none(),
            },
            cstr.clone(),
            omegas(cstr.cstr_arity as usize),
        ),
        ..ex_pat.clone()
    }
}

/// Get variant constructors from the environment for a given result type.
/// Equivalent to OCaml's `Parmatch.get_variant_constructors`.
fn get_variant_constructors_from_env(
    ctx_ref: &TypeContext,
    env: &crate::types::env::Env,
    result_type: TypeExprRef,
) -> Vec<ConstructorDescription> {
    use crate::types::ctype;
    use crate::types::decl::{ConstructorArguments, ConstructorDeclaration, TypeKind};
    use crate::types::type_expr::TypeDesc;

    fn cstr_arity(args: &ConstructorArguments) -> i32 {
        match args {
            ConstructorArguments::CstrTuple(v) => v.len() as i32,
            ConstructorArguments::CstrRecord(v) => v.len() as i32,
        }
    }

    fn build_descriptions(
        decl: &crate::types::TypeDeclaration,
        cds: &[ConstructorDeclaration],
        result_type: TypeExprRef,
    ) -> Vec<ConstructorDescription> {
        let layout = decl.variant_layout_ref().expect("variant layout");
        cds.iter()
            .enumerate()
            .map(|(position, cd)| {
                let arity = cstr_arity(&cd.cd_args);
                let args_vec = match &cd.cd_args {
                    ConstructorArguments::CstrTuple(v) => v.clone(),
                    ConstructorArguments::CstrRecord(v) => v.iter().map(|ld| ld.ld_type).collect(),
                };
                ConstructorDescription {
                    cstr_name: cd.cd_id.name().to_string(),
                    cstr_res: result_type,
                    cstr_existentials: Vec::new(),
                    cstr_args: args_vec,
                    cstr_arity: arity,
                    cstr_kind: crate::types::ConstructorKind::Ordinary(
                        crate::types::ConstructorReference {
                            variant: layout,
                            position,
                        },
                    ),
                    cstr_generalized: false,
                    cstr_private: crate::types::asttypes::PrivateFlag::Public,
                    cstr_loc: Location::none(),
                    cstr_attributes: Vec::new(),
                    cstr_inlined: None,
                }
            })
            .collect()
    }

    let mut ty = ctx_ref.repr(result_type);
    for _ in 0..16 {
        let desc = ctx_ref.get_desc(ty);
        let TypeDesc::Tconstr { path, .. } = &*desc else {
            return Vec::new();
        };
        let exact_lookup = |decl: &crate::types::decl::TypeDeclaration| match path {
            crate::types::Path::Pident(_) => true,
            _ => decl
                .type_path
                .as_ref()
                .is_some_and(|decl_path| decl_path.same(path) || decl_path.name() == path.name()),
        };

        let env_decl = match env.lookup_type(path) {
            Ok(decl) if exact_lookup(decl) => Some(decl),
            _ => None,
        };
        // OCaml `Parmatch.get_variant_constructors` trusts `Env.find_type`
        // for the queried path, even when an alias path returns the target
        // declaration metadata (compiler/ml/parmatch.ml:975-984). The helper
        // below is Rust's Env.find_type-equivalent, so do not require its
        // returned `type_path` to be textually identical to the query.
        let fallback_decl = ctype::lookup_type_decl_for_path(ctx_ref, env, path);

        if let Some(decl) = env_decl {
            match &decl.type_kind {
                TypeKind::TypeVariant(cds, _) => {
                    return build_descriptions(&decl, cds, result_type);
                }
                TypeKind::TypeAbstract => {
                    if let Some(manifest) = decl.type_manifest {
                        let manifest = ctx_ref.repr(manifest);
                        if manifest != ty {
                            ty = manifest;
                            continue;
                        }
                    }
                }
                _ => {}
            }
        } else if let Some(decl) = fallback_decl {
            match &decl.type_kind {
                TypeKind::TypeVariant(cds, _) => {
                    return build_descriptions(&decl, cds, result_type);
                }
                TypeKind::TypeAbstract => {
                    if let Some(manifest) = decl.type_manifest {
                        let manifest = ctx_ref.repr(manifest);
                        if manifest != ty {
                            ty = manifest;
                            continue;
                        }
                    }
                }
                _ => {}
            }
        }

        // OCaml `Parmatch.get_variant_constructors` asks `Env.find_type` for
        // the path and only expands the type head when that declaration has a
        // manifest (compiler/ml/parmatch.ml:975-984). Do not walk module type
        // aliases here: if normal Env-compatible lookup misses, the caller can
        // synthesize missing constructor tags from the typed constructor counts.

        if let Some(expanded) = ctype::expand_head_once(ctx_ref, env, ty) {
            let expanded = ctx_ref.repr(expanded);
            if expanded != ty {
                ty = expanded;
                continue;
            }
        }
        return Vec::new();
    }

    Vec::new()
}

/// Compute negative fail action (jump to default).
/// Returns (optional fail lambda, jumps).
/// Equivalent to OCaml's `mk_failaction_neg`.
fn mk_failaction_neg(
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
) -> (Option<RawLambda>, Jumps) {
    match partial {
        Partial::Partial => match def.first() {
            Some((_, idef)) => (
                Some(RawLambda::LstaticRaise(*idef, Vec::new())),
                jumps_singleton(*idef, ctx.to_vec()),
            ),
            None => {
                // Act as Total: if no default matrix exists, the switch cannot fail
                (None, jumps_empty())
            }
        },
        Partial::Total => (None, jumps_empty()),
    }
}

/// Compute positive fail action (enumerating missing constructors).
/// Returns (optional fail lambda, additional cases, jumps).
/// Equivalent to OCaml's `mk_failaction_pos`.
fn mk_failaction_pos(
    ctx_ref: &TypeContext,
    partial: &Partial,
    seen: &[Pattern],
    ctx: &[Ctx],
    defs: &DefaultEnv,
) -> (
    Option<RawLambda>,
    Vec<(ConstructorDescription, RawLambda)>,
    Jumps,
) {
    let fail_pats = complete_pats_constrs(ctx_ref, seen);
    if fail_pats.len() < 32 {
        let to_test: Vec<(Pattern, Vec<Ctx>)> = fail_pats
            .iter()
            .map(|pat| (pat.clone(), ctx_lub(pat, ctx)))
            .collect();

        let (fail, jmps) = scan_def(ctx, Vec::new(), to_test, defs);
        (None, fail, jmps)
    } else {
        // Too many non-matched constructors -> reduced information
        let (fail, jumps) = mk_failaction_neg(partial, ctx, defs);
        (fail, Vec::new(), jumps)
    }
}

/// Scan default environment to build per-constructor fail actions.
/// Returns (key-action list, jumps).
/// Equivalent to OCaml's inner `scan_def` in `mk_failaction_pos`.
fn scan_def(
    ctx: &[Ctx],
    env: Vec<(Vec<Pattern>, i32)>,
    to_test: Vec<(Pattern, Vec<Ctx>)>,
    defs: &[(Matrix, i32)],
) -> (Vec<(ConstructorDescription, RawLambda)>, Jumps) {
    if to_test.is_empty() || defs.is_empty() {
        // Fold env to build (klist, jumps)
        let mut klist: Vec<(ConstructorDescription, RawLambda)> = Vec::new();
        let mut jumps = jumps_empty();
        for (pats, i) in &env {
            let action = RawLambda::LstaticRaise(*i, Vec::new());
            let mut new_klist: Vec<(ConstructorDescription, RawLambda)> = pats
                .iter()
                .map(|pat| (get_key_constr(pat), action.clone()))
                .collect();
            new_klist.extend(klist);
            klist = new_klist;
        }
        for (pats, i) in env.iter().rev() {
            if !ctx.is_empty() {
                let jump_ctx = ctx_lub(&list_as_pat(pats), ctx);
                jumps = jumps_add(*i, jump_ctx, jumps);
            }
        }
        (klist, jumps)
    } else {
        match defs.split_first() {
            None => scan_def(ctx, env, Vec::new(), &[]),
            Some(((pss, idef), rem)) => {
                let (now, later): (Vec<_>, Vec<_>) = to_test
                    .into_iter()
                    .partition(|(_, p_ctx)| ctx_match(p_ctx, pss));
                if now.is_empty() {
                    scan_def(ctx, env, later, rem)
                } else {
                    let pats: Vec<Pattern> = now.into_iter().map(|(p, _)| p).collect();
                    let mut new_env = vec![(pats, *idef)];
                    new_env.extend(env);
                    scan_def(ctx, new_env, later, rem)
                }
            }
        }
    }
}

/// Overloaded version of `same_actions` for tagged lists (ConstructorTag, lambda).
/// Checks if all actions in a case list are the same.
fn all_actions_same_tagged<K>(cases: &[(K, RawLambda)]) -> bool {
    match cases {
        [] => false,
        [_] => true,
        [(_, first), rest @ ..] => {
            let Some(key) = make_key_string(first) else {
                return false;
            };
            rest.iter()
                .all(|(_, action)| make_key_string(action).as_deref() == Some(&key))
        }
    }
}

fn all_match_actions_same<K>(cases: &[(K, MatchCode)]) -> bool {
    match cases {
        [] => false,
        [_] => true,
        [(_, act0), rem @ ..] => {
            let Some(key0) = act0.normalized_key() else {
                return false;
            };
            rem.iter()
                .all(|(_, action)| action.normalized_key().as_deref() == Some(key0.as_str()))
        }
    }
}

/// Share actions for tree-based string matching.
/// Like share_actions_tree but for (String, RawLambda) pairs.
fn share_actions_tree_string(
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> (
    Box<dyn FnOnce(RawLambda) -> RawLambda>,
    Vec<(String, RawLambda)>,
    Option<RawLambda>,
) {
    let mut store = StoreExp::mk_store();

    let d_idx = d.map(|d| store.act_store_shared(d));

    let sw_indices: Vec<(String, usize)> = sw
        .into_iter()
        .map(|(s, act)| (s, store.act_store(act)))
        .collect();

    let acts = store.act_get_shared();

    // Process shared actions — handle_shared
    let mut handlers: Vec<(i32, Box<dyn FnOnce(RawLambda) -> RawLambda>)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a, next_raise_count);
                handlers.push((i, h));
                make_exit(i)
            }
        })
        .collect();

    let mut use_counts = vec![0usize; resolved_acts.len()];
    if let Some(index) = d_idx {
        use_counts[index] += 1;
    }
    for (_, index) in &sw_indices {
        use_counts[*index] += 1;
    }
    let mut resolved_acts = resolved_acts.into_iter().map(Some).collect::<Vec<_>>();
    let d = d_idx.map(|index| materialize_resolved_action(&mut resolved_acts, &use_counts, index));
    let sw: Vec<(String, RawLambda)> = sw_indices
        .into_iter()
        .map(|(string, index)| {
            (
                string,
                materialize_resolved_action(&mut resolved_acts, &use_counts, index),
            )
        })
        .collect();

    // Build composed wrapper function
    let hs: Box<dyn FnOnce(RawLambda) -> RawLambda> = handlers.into_iter().fold(
        Box::new(|x: RawLambda| x) as Box<dyn FnOnce(RawLambda) -> RawLambda>,
        |ohs, (_, h)| Box::new(move |act: RawLambda| h(ohs(act))),
    );

    (hs, sw, d)
}

/// Combine constant matching results.
/// Equivalent to OCaml's `combine_constant`.
fn combine_constant(
    names: Option<crate::lambda::SwitchDispatch>,
    loc: Location,
    arg: RawLambda,
    cst: &Constant,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<(Constant, RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (const_lambda_list, total, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
    let lambda1 = match cst {
        Constant::Int(_) => {
            let int_lambda_list: Vec<(i32, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, l)| match c {
                    Constant::Int(n) => (n as i32, l),
                    _ => panic!("combine_constant: expected Const_int"),
                })
                .collect();
            call_switcher(
                loc,
                fail,
                arg,
                i32::MIN,
                i32::MAX,
                int_lambda_list,
                names,
                next_raise_count,
            )
        }
        Constant::Char(_) => {
            let int_lambda_list: Vec<(i32, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, l)| match c {
                    Constant::Char(ch) => (ch as i32, l),
                    _ => panic!("combine_constant: expected Const_char"),
                })
                .collect();
            call_switcher(
                loc,
                fail,
                arg,
                0,
                i32::MAX,
                int_lambda_list,
                names,
                next_raise_count,
            )
        }
        Constant::String(_, _) => {
            let const_lambda_list = sort_lambda_list(const_lambda_list);
            let sw: Vec<(String, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, act)| match c {
                    Constant::String(s, _) => (s, act),
                    _ => panic!("combine_constant: expected Const_string"),
                })
                .collect();
            let (hs, sw, fail) = share_actions_tree_string(sw, fail, next_raise_count);
            hs(RawLambda::LstringSwitch(
                Box::new(arg),
                sw,
                fail.map(Box::new),
            ))
        }
        Constant::Float(_) => make_test_sequence(
            loc,
            fail,
            Primitive::Pfloatcomp(Comparison::Neq),
            Primitive::Pfloatcomp(Comparison::Lt),
            arg,
            const_lambda_list,
            next_raise_count,
        ),
        Constant::BigInt(_, _) => make_test_sequence(
            loc,
            fail,
            Primitive::Pbigintcomp(Comparison::Neq),
            Primitive::Pbigintcomp(Comparison::Lt),
            arg,
            const_lambda_list,
            next_raise_count,
        ),
    };
    (lambda1, jumps_union(&local_jumps, &total))
}

/// Split case list into constant and non-constant constructor cases.
/// Equivalent to OCaml's `split_cases`.
fn split_cases(
    tag_lambda_list: Vec<(ConstructorDescription, MatchCode)>,
) -> (
    Vec<(ConstructorDescription, MatchCode)>,
    Vec<(ConstructorDescription, MatchCode)>,
) {
    let (mut consts, mut nonconsts): (Vec<_>, Vec<_>) =
        tag_lambda_list
            .into_iter()
            .partition(|(cstr, _)| match cstr.cstr_kind {
                crate::types::ConstructorKind::Ordinary(_) => cstr.cstr_args.is_empty(),
                crate::types::ConstructorKind::Extension(_) => {
                    unreachable!("extension in split_cases")
                }
            });
    let position = |cstr: &ConstructorDescription| match cstr.cstr_kind {
        crate::types::ConstructorKind::Ordinary(reference) => reference.position,
        crate::types::ConstructorKind::Extension(_) => unreachable!("extension in split_cases"),
    };
    consts.sort_by_key(|(cstr, _)| position(cstr));
    nonconsts.sort_by_key(|(cstr, _)| position(cstr));
    (consts, nonconsts)
}

/// Split variant case list into constant and non-constant.
/// Equivalent to OCaml's `split_variant_cases`.
fn split_variant_cases(
    tag_lambda_list: Vec<((String, bool), RawLambda)>,
) -> (
    Vec<(i32, (String, RawLambda))>,
    Vec<(i32, (String, RawLambda))>,
) {
    let mut consts = Vec::new();
    let mut nonconsts = Vec::new();
    for ((name, is_const), act) in tag_lambda_list {
        let hash = btype::hash_variant(&name);
        if is_const {
            consts.push((hash, (name, act)));
        } else {
            nonconsts.push((hash, (name, act)));
        }
    }
    consts.sort_by_key(|(i, _)| *i);
    nonconsts.sort_by_key(|(i, _)| *i);
    (consts, nonconsts)
}

/// Get extension constructor cases.
/// Equivalent to OCaml's `get_extension_cases`.
fn get_extension_cases(
    tag_lambda_list: Vec<(ConstructorDescription, MatchCode)>,
) -> Vec<(crate::types::path::Path, MatchCode)> {
    tag_lambda_list
        .into_iter()
        .map(|(cstr, act)| match cstr.cstr_kind {
            crate::types::ConstructorKind::Extension(path) => (path, act),
            crate::types::ConstructorKind::Ordinary(_) => unreachable!("ordinary extension case"),
        })
        .collect()
}

/// Translate a path to a RawLambda access expression.
/// Equivalent to OCaml's `transl_normal_path`.
fn transl_normal_path(path: &crate::types::path::Path) -> RawLambda {
    use crate::types::path::Path;
    match path {
        Path::Pident(id) => {
            if id.is_global() {
                RawLambda::LglobalModule(id.clone(), false)
            } else {
                RawLambda::Lvar(id.clone())
            }
        }
        Path::Pdot(p, s, pos) => RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pfield(
                *pos,
                FieldDbgInfo::Module {
                    name: s.to_string(),
                },
            ),
            args: vec![transl_normal_path(p)],
            loc: Location::none(),
        }),
        Path::Papply(_, _) => panic!("transl_normal_path: Papply"),
    }
}

/// Translate an extension path to a RawLambda.
/// Equivalent to OCaml's `transl_extension_path`.
fn transl_extension_path(
    ctx_ref: &TypeContext,
    env: EnvRef,
    path: &crate::types::path::Path,
) -> RawLambda {
    // OCaml: transl_extension_path = transl_value_path = fun env path ->
    //   transl_normal_path (Env.normalize_path_prefix env path)
    if let Some(typed_env) = ctx_ref.get_typed_env(env) {
        let normalized = typed_env.normalize_path_prefix(path);
        // If normalization didn't resolve (still Pdot chain), try via type context's
        // resolved module sig cache for persistent module aliases
        let normalized = normalize_path_via_ctx(ctx_ref, &normalized);
        transl_normal_path(&normalized)
    } else {
        let normalized = normalize_path_via_ctx(ctx_ref, path);
        transl_normal_path(&normalized)
    }
}

/// Normalize a value path's prefix through the type context's module sig cache.
/// This handles persistent module aliases that Env::normalize_path can't resolve.
fn normalize_path_via_ctx(
    ctx_ref: &TypeContext,
    path: &crate::types::path::Path,
) -> crate::types::path::Path {
    use crate::types::path::Path;

    match path {
        Path::Pdot(prefix, name, pos) => {
            // First normalize the prefix recursively
            let norm_prefix = normalize_module_path_via_ctx(ctx_ref, prefix);
            if norm_prefix == **prefix {
                path.clone()
            } else {
                Path::Pdot(std::sync::Arc::new(norm_prefix), name.clone(), *pos)
            }
        }
        _ => path.clone(),
    }
}

/// Normalize a module path through the type context's module sig cache.
fn normalize_module_path_via_ctx(
    ctx_ref: &TypeContext,
    path: &crate::types::path::Path,
) -> crate::types::path::Path {
    use crate::types::decl::{ModuleType, SignatureItem};
    use crate::types::path::Path;

    // First normalize prefix recursively for Pdot
    let path = match path {
        Path::Pdot(prefix, name, pos) => {
            let norm_prefix = normalize_module_path_via_ctx(ctx_ref, prefix);
            if norm_prefix == **prefix {
                path.clone()
            } else {
                Path::Pdot(std::sync::Arc::new(norm_prefix), name.clone(), *pos)
            }
        }
        _ => path.clone(),
    };

    // Check if this path resolves to a module alias via sig caches
    match &path {
        Path::Pdot(prefix, name, _) => {
            // Strategy 1: check the qualified module components cache.
            // This covers persistent module aliases like Js.Exn → Stdlib_Exn
            // that were resolved during type checking via with_resolved_module_components_for_path.
            if let Some(alias_target) = ctx_ref.find_module_alias_in_components(prefix, name) {
                if !alias_target.same(&path) {
                    return normalize_module_path_via_ctx(ctx_ref, &alias_target);
                }
            }

            // Strategy 2: try to find the parent module's signature from sig caches.
            let prefix_name = prefix.name();
            if let Some((_, sig)) = ctx_ref.find_resolved_module_sig(&prefix_name) {
                for item in sig.iter() {
                    if let SignatureItem::SigModule(id, md, _) = item {
                        if id.name() == name {
                            if let ModuleType::MtyAlias(_, alias_path) = &md.md_type {
                                return normalize_module_path_via_ctx(ctx_ref, alias_path);
                            }
                        }
                    }
                }
            } else {
                let alias_path = {
                    let renamed_sigs = ctx_ref.renamed_module_sigs.borrow();
                    renamed_sigs.get(&prefix_name).and_then(|sig| {
                        sig.iter().find_map(|item| match item {
                            SignatureItem::SigModule(id, md, _) if id.name() == name => {
                                match &md.md_type {
                                    ModuleType::MtyAlias(_, alias_path) => Some(alias_path.clone()),
                                    _ => None,
                                }
                            }
                            _ => None,
                        })
                    })
                };
                if let Some(alias_path) = alias_path {
                    return normalize_module_path_via_ctx(ctx_ref, &alias_path);
                }
            }
            path
        }
        _ => path,
    }
}

/// Combine constructor matching results.
/// Equivalent to OCaml's `combine_constructor`.
fn combine_constructor(
    ctx_ref: &TypeContext,
    loc: Location,
    arg: RawLambda,
    ex_pat: &Pattern,
    cstr: &ConstructorDescription,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (
        Vec<(ConstructorDescription, MatchCode)>,
        Jumps,
        Vec<Pattern>,
    ),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (tag_lambda_list, total1, pats) = c_div;

    if matches!(cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) {
        // Special cases for extensions
        let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
        let lambda1 = {
            let extension_cases = get_extension_cases(tag_lambda_list);
            // OCaml compiler/ml/matching.ml:2118-2139 uses the first extension
            // action as the default, then fold_rights remaining cases into
            // Pextension_slot_eq tests. Consume the owned action list here so
            // the Rust port preserves that shape without cloning action bodies.
            let (default, extension_cases) = match fail {
                None => {
                    let mut extension_cases = extension_cases.into_iter();
                    let Some((_, default)) = extension_cases.next() else {
                        panic!("combine_constructor: no extension cases");
                    };
                    (default, extension_cases.collect())
                }
                Some(fail) => (MatchCode::raw(fail), extension_cases),
            };
            if extension_cases.is_empty() {
                default
            } else {
                let tag = ctx_ref.create_ident("tag");
                let tests = extension_cases
                    .into_iter()
                    .rev()
                    .fold(default, |rem, (path, act)| {
                        let ext = transl_extension_path(ctx_ref, ex_pat.pat_env, &path);
                        MatchCode::if_then_else(
                            RawLambda::Lprim(RawPrimInfo {
                                primitive: Primitive::PextensionSlotEq,
                                args: vec![RawLambda::Lvar(tag.clone()), ext],
                                loc: loc.clone(),
                            }),
                            act,
                            rem,
                        )
                    });
                tests.bind(LetKind::Alias, tag, arg)
            }
        };
        (lambda1.into_raw(), jumps_union(&local_jumps, &total1))
    } else {
        // Regular concrete type
        let reference = match cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(reference) => reference,
            crate::types::ConstructorKind::Extension(_) => unreachable!(),
        };
        let (num_consts, num_nonconsts, sig_complete, matching_facts) = ctx_ref
            .with_variant_layout(reference.variant, |layout| {
                (
                    layout.num_constants(),
                    layout.num_blocks(),
                    tag_lambda_list.len() == layout.constructors.len(),
                    layout.matching_facts.clone(),
                )
            });
        let (fail_opt, fails, local_jumps) = if sig_complete {
            (None, Vec::new(), jumps_empty())
        } else {
            mk_failaction_pos(ctx_ref, partial, &pats, ctx, def)
        };

        // OCaml shares the immutable list cells/actions here:
        // compiler/ml/matching.ml:2152-2155 builds `fails @ tag_lambda_list`,
        // then passes the same list to both `split_cases` and `same_actions`.
        // Rust's Vec is moved into `split_cases`, so compute the pure
        // same-action fast path first. When all actions match, move the first
        // owned action instead of cloning it; OCaml returns the original `act0`
        // at compiler/ml/matching.ml:2155-2156.
        let mut actions: Vec<_> = fails
            .into_iter()
            .map(|(key, action)| (key, MatchCode::raw(action)))
            .collect();
        actions.extend(tag_lambda_list);
        let actions_all_same = fail_opt.is_none() && all_match_actions_same(&actions);

        let lambda1 = if actions_all_same {
            let (_, act) = actions
                .into_iter()
                .next()
                .expect("non-empty action list after same-action check");
            act.into_raw() // Identical actions, no failure
        } else {
            let (mut consts, mut nonconsts) = split_cases(actions);
            let is_option = constructor_has_optional_shape(cstr);
            if num_consts == 1
                && num_nonconsts == 1
                && consts.len() == 1
                && nonconsts.len() == 1
                && (cstr.cstr_name == "::" || cstr.cstr_name == "[]" || is_option)
            {
                // OCaml compiler/ml/matching.ml:2156-2173 emits a two-way test
                // for lists/options. `consts` and `nonconsts` are owned here, so
                // move the branch actions instead of cloning whole RawLambda
                // bodies out of borrowed slice patterns.
                let (_, act1) = consts.pop().expect("one constant constructor case");
                let (_, act2) = nonconsts.pop().expect("one block constructor case");
                let test_arg = if is_option {
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::PisNotNone,
                        args: vec![arg],
                        loc: loc.clone(),
                    })
                } else {
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pjscomp(Comparison::Neq),
                        args: vec![arg, RawLambda::Lconst(crate::lambda::Constant::int(0))],
                        loc: loc.clone(),
                    })
                };
                RawLambda::LifThenElse(
                    Box::new(test_arg),
                    Box::new(act2.into_raw()),
                    Box::new(act1.into_raw()),
                )
            } else if num_consts == 2
                && num_nonconsts == 0
                && consts.len() == 2
                && nonconsts.is_empty()
                && (cstr.cstr_name == "true" || cstr.cstr_name == "false")
            {
                let mut true_action = None;
                let mut false_action = None;
                for (constructor, action) in consts {
                    match constructor.cstr_name.as_str() {
                        "true" => true_action = Some(action),
                        "false" => false_action = Some(action),
                        _ => {}
                    }
                }
                RawLambda::LifThenElse(
                    Box::new(arg),
                    Box::new(true_action.expect("true action").into_raw()),
                    Box::new(false_action.expect("false action").into_raw()),
                )
            } else {
                // Emit a switch. OCaml computes `act0` at
                // compiler/ml/matching.ml:2179-2189, but the only arm
                // that can consume it is guarded by `when false` at
                // matching.ml:2190. Skipping that pure computation
                // avoids normalizing/cloning switch actions without
                // changing the emitted lambda.
                let switch_cases = |cases: Vec<(ConstructorDescription, MatchCode)>| {
                    cases
                        .into_iter()
                        .map(|(cstr, action)| {
                            let reference = match cstr.cstr_kind {
                                crate::types::ConstructorKind::Ordinary(reference) => reference,
                                crate::types::ConstructorKind::Extension(_) => unreachable!(),
                            };
                            (
                                crate::lambda::SwitchKey::Constructor(
                                    reference.representation(ctx_ref),
                                ),
                                action,
                            )
                        })
                        .collect()
                };
                let (handlers, sw) = share_match_switch(
                    num_consts,
                    consts.len() >= num_consts,
                    switch_cases(consts),
                    num_nonconsts,
                    nonconsts.len() >= num_nonconsts,
                    switch_cases(nonconsts),
                    fail_opt.map(MatchCode::raw),
                    crate::lambda::SwitchDispatch::Variant(matching_facts),
                    next_raise_count,
                );
                let sw = reintroduce_fail(sw);
                let result = RawLambda::Lswitch(Box::new(arg), sw, loc.clone());
                apply_handlers(result, handlers)
            }
        };
        (lambda1, jumps_union(&local_jumps, &total1))
    }
}

/// Convert a polyvar int_lambda_list by grouping entries with the same action.
/// Equivalent to OCaml's `Polyvar_pattern_match.convert`.
///
/// Groups entries that have the same lambda action together, producing a list
/// of `(hash_names, action)` pairs sorted by first occurrence (stamp).
fn convert_polyvar_list(xs: &[(i32, (String, RawLambda))]) -> Vec<(Vec<(i32, String)>, RawLambda)> {
    // Group by normalized action equality, matching OCaml's make_key-based sharing.
    // Each entry gets a stamp (its original index) for stable sorting.
    struct Entry {
        stamp: usize,
        hash_names: Vec<(i32, String)>,
        act: RawLambda,
        key: Option<String>,
    }

    let mut entries: Vec<Entry> = Vec::new();

    for (i, (hash, (name, act))) in xs.iter().enumerate() {
        let key = make_key_string(act);
        let found_idx = key.as_ref().and_then(|key| {
            entries
                .iter()
                .position(|e| e.key.as_ref().is_some_and(|existing| existing == key))
        });
        if let Some(idx) = found_idx {
            entries[idx].hash_names.push((*hash, name.clone()));
        } else {
            entries.push(Entry {
                stamp: i,
                hash_names: vec![(*hash, name.clone())],
                act: act.clone(),
                key,
            });
        }
    }

    entries.sort_by_key(|e| e.stamp);
    entries
        .into_iter()
        .map(|mut e| {
            // Sort hashes descending within each group to match OCaml's Switcher.test_sequence ordering
            e.hash_names.sort_by(|a, b| b.0.cmp(&a.0));
            (e.hash_names, e.act)
        })
        .collect()
}

/// Create a disjunction of equality tests for polyvar hash values.
/// Equivalent to OCaml's `Polyvar_pattern_match.or_list`.
fn raw_polyvariant_hash_const(hash: i32, name: &str) -> RawLambda {
    RawLambda::Lconst(crate::lambda::lam_constant::Constant::Int {
        i: hash,
        comment: Some(PointerInfo::PolyVariant(name.to_string())),
    })
}

fn or_list_polyvar(arg: &RawLambda, hash_names: &[(i32, String)]) -> RawLambda {
    let (first_hash, first_name) = &hash_names[0];
    let init = RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pintcomp(Comparison::Eq),
        args: vec![
            arg.clone(),
            raw_polyvariant_hash_const(*first_hash, first_name),
        ],
        loc: Location::none(),
    });
    hash_names[1..].iter().fold(init, |acc, (hash, name)| {
        RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Psequor,
            args: vec![
                acc,
                RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pintcomp(Comparison::Eq),
                    args: vec![arg.clone(), raw_polyvariant_hash_const(*hash, name)],
                    loc: Location::none(),
                }),
            ],
            loc: Location::none(),
        })
    })
}

/// Build an if-chain from converted polyvar list.
/// Used by both make_test_sequence_variant_constant and call_switcher_variant_constant.
fn polyvar_if_chain(
    fail: Option<RawLambda>,
    arg: &RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
) -> RawLambda {
    let converted = convert_polyvar_list(int_lambda_list);
    match (converted.split_first(), &fail) {
        (Some(((_, default_act), rest)), &None) => {
            // No fail: first action is default, rest are if-then-else
            rest.iter()
                .rev()
                .fold(default_act.clone(), |acc, (hash_names, act)| {
                    let predicate = or_list_polyvar(arg, hash_names);
                    RawLambda::LifThenElse(
                        Box::new(predicate),
                        Box::new(act.clone()),
                        Box::new(acc),
                    )
                })
        }
        (_, &Some(ref fail_act)) => {
            // With fail: fail is default, all entries are if-then-else
            converted
                .iter()
                .rev()
                .fold(fail_act.clone(), |acc, (hash_names, act)| {
                    let predicate = or_list_polyvar(arg, hash_names);
                    RawLambda::LifThenElse(
                        Box::new(predicate),
                        Box::new(act.clone()),
                        Box::new(acc),
                    )
                })
        }
        (None, &None) => panic!("polyvar_if_chain: empty list with no fail"),
    }
}

/// Make a test sequence for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.make_test_sequence_variant_constant`.
fn make_test_sequence_variant_constant(
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    _next_raise_count: &mut i32,
) -> RawLambda {
    polyvar_if_chain(fail, &arg, int_lambda_list)
}

/// Call switcher for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constant`.
fn call_switcher_variant_constant(
    _loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    _names: Option<crate::lambda::SwitchDispatch>,
    _next_raise_count: &mut i32,
) -> RawLambda {
    polyvar_if_chain(fail, &arg, int_lambda_list)
}

/// Call switcher for variant non-constant (block) matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constr`.
fn call_switcher_variant_constr(
    ctx_ref: &TypeContext,
    loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    names: Option<crate::lambda::SwitchDispatch>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let v = ctx_ref.create_ident("variant");
    RawLambda::Llet(
        LetKind::Alias,
        v.clone(),
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pfield(0, FieldDbgInfo::PolyVarTag),
            args: vec![arg],
            loc: loc.clone(),
        })),
        Box::new(call_switcher_variant_constant(
            loc,
            fail,
            RawLambda::Lvar(v),
            int_lambda_list,
            names,
            next_raise_count,
        )),
    )
}

/// Combine variant matching results.
/// Equivalent to OCaml's `combine_variant`.
fn combine_variant(
    ctx_ref: &TypeContext,
    names: Option<crate::lambda::SwitchDispatch>,
    loc: Location,
    row: &RowDesc,
    arg: RawLambda,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<((String, bool), RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (tag_lambda_list, total1, _pats) = c_div;
    let row = btype::row_repr(ctx_ref, row);
    let mut num_constr: usize = 0;
    if row.row_closed {
        for (_, f) in &row.row_fields {
            match btype::row_field_repr(ctx_ref, f) {
                RowField::Rabsent => {}
                RowField::Reither {
                    constant: true,
                    ref types,
                    ..
                } if !types.is_empty() => {}
                _ => num_constr += 1,
            }
        }
    } else {
        num_constr = usize::MAX;
    }

    let test_int_or_block = |arg: RawLambda, if_int: RawLambda, if_block: RawLambda| -> RawLambda {
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::PisPolyVarBlock,
                args: vec![arg],
                loc: loc.clone(),
            })),
            Box::new(if_block),
            Box::new(if_int),
        )
    };

    let sig_complete = tag_lambda_list.len() == num_constr;

    let (fail, local_jumps) = if sig_complete || matches!(partial, Partial::Total) {
        (None, jumps_empty())
    } else {
        mk_failaction_neg(partial, ctx, def)
    };

    let actions_all_same = fail.is_none() && all_actions_same_tagged(&tag_lambda_list);
    let lambda1 = if actions_all_same {
        // OCaml compiler/ml/matching.ml:2155-2156 returns the original
        // action when all switch branches share the same lambda.
        let (_, act) = tag_lambda_list
            .into_iter()
            .next()
            .expect("non-empty variant action list after same-action check");
        act
    } else {
        let (consts, nonconsts) = split_variant_cases(tag_lambda_list);
        match (consts.as_slice(), nonconsts.as_slice()) {
            ([(_, (_, act1))], [(_, (_, act2))]) if fail.is_none() => {
                test_int_or_block(arg, act1.clone(), act2.clone())
            }
            (_, []) => {
                // One can compare integers and pointers
                make_test_sequence_variant_constant(fail, arg, &consts, next_raise_count)
            }
            ([], _) => {
                let lam = call_switcher_variant_constr(
                    ctx_ref,
                    loc.clone(),
                    fail.clone(),
                    arg.clone(),
                    &nonconsts,
                    names,
                    next_raise_count,
                );
                // One must not dereference integers
                match fail {
                    None => lam,
                    Some(fail) => test_int_or_block(arg, fail, lam),
                }
            }
            _ => {
                let lam_const = call_switcher_variant_constant(
                    loc.clone(),
                    fail.clone(),
                    arg.clone(),
                    &consts,
                    names.clone(),
                    next_raise_count,
                );
                let lam_nonconst = call_switcher_variant_constr(
                    ctx_ref,
                    loc.clone(),
                    fail,
                    arg.clone(),
                    &nonconsts,
                    names,
                    next_raise_count,
                );
                test_int_or_block(arg, lam_const, lam_nonconst)
            }
        }
    };
    (lambda1, jumps_union(&local_jumps, &total1))
}

/// Combine array matching results.
/// Equivalent to OCaml's `combine_array`.
fn combine_array(
    ctx_ref: &TypeContext,
    names: Option<crate::lambda::SwitchDispatch>,
    loc: Location,
    arg: RawLambda,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<(usize, RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (len_lambda_list, total1, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
    let lambda1 = {
        let newvar = ctx_ref.create_ident("len");
        let int_lambda_list: Vec<(i32, RawLambda)> = len_lambda_list
            .into_iter()
            .map(|(len, act)| (len as i32, act))
            .collect();
        let switch_result = call_switcher(
            loc.clone(),
            fail,
            RawLambda::Lvar(newvar.clone()),
            0,
            i32::MAX,
            int_lambda_list,
            names,
            next_raise_count,
        );
        bind(
            LetKind::Alias,
            &newvar,
            &RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Parraylength,
                args: vec![arg],
                loc,
            }),
            switch_result,
        )
    };
    (lambda1, jumps_union(&local_jumps, &total1))
}

// ============================================================================
// Layer 10: Compile functions — OCaml matching.ml lines 2351-2606
// ============================================================================

/// Exception raised when all cases in a compile are unreachable.
/// Equivalent to OCaml's `Unused` exception.
#[derive(Debug)]
struct Unused;

/// Compile a list of divided cells.
/// Returns (key-action list, total jumps, pattern list).
/// Equivalent to OCaml's `compile_list`.
fn materialize_compiled_div<K>(
    (actions, jumps, patterns): (Vec<(K, MatchCode)>, Jumps, Vec<Pattern>),
) -> (Vec<(K, RawLambda)>, Jumps, Vec<Pattern>) {
    (
        actions
            .into_iter()
            .map(|(key, action)| (key, action.into_raw()))
            .collect(),
        jumps,
        patterns,
    )
}

fn compile_list<K: Clone>(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(MatchCode, Jumps), Unused>,
    division: Vec<(K, MatchCell)>,
) -> Result<(Vec<(K, MatchCode)>, Jumps, Vec<Pattern>), Unused> {
    let mut compiled = Vec::new();
    let mut totals = Vec::new();
    let mut new_pats = Vec::new();

    for (key, cell) in division {
        if cell.ctx.is_empty() {
            continue;
        }
        match compile_fun(&cell.ctx, &cell.pm) {
            Ok((lambda1, total1)) => {
                // OCaml `compiler/ml/matching.ml:2358-2364` recurses on the
                // tail with `jumps_map ctx_combine total1 :: totals`, then
                // conses `(key, lambda1)` and `cell.pat` onto the returned
                // lists. Rust vectors need the result lists in forward order
                // and the jump totals in reverse-success order, so push
                // results linearly and reverse only the totals once.
                compiled.push((key, lambda1));
                totals.push(jumps_map(|c| ctx_combine(&c), &total1));
                new_pats.push(cell.pat);
            }
            Err(Unused) => {}
        }
    }

    totals.reverse();
    Ok((compiled, jumps_unions(totals), new_pats))
}

/// Compile or-pattern handlers.
/// Equivalent to OCaml's `compile_orhandlers`.
fn compile_orhandlers(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(MatchCode, Jumps), Unused>,
    lambda1: MatchCode,
    total1: Jumps,
    ctx: &[Ctx],
    to_catch: &[(Matrix, i32, Vec<Ident>, PatternMatching)],
) -> (MatchCode, Jumps) {
    fn do_rec(
        compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(MatchCode, Jumps), Unused>,
        r: MatchCode,
        total_r: Jumps,
        ctx: &[Ctx],
        to_catch: &[(Matrix, i32, Vec<Ident>, PatternMatching)],
    ) -> (MatchCode, Jumps) {
        match to_catch.split_first() {
            None => (r, total_r),
            Some(((mat, i, vars, pm), rem)) => {
                let ctx_i = select_columns(mat, ctx);
                match compile_fun(&ctx_i, pm) {
                    Ok((handler_i, total_i)) => {
                        match r.normalized_static_raise() {
                            Some((j, args)) if j == *i => {
                                let body = vars.iter().zip(args.iter()).rev().fold(
                                    handler_i,
                                    |body, (var, arg)| {
                                        body.bind(LetKind::Alias, var.clone(), arg.clone())
                                    },
                                );
                                do_rec(
                                    compile_fun,
                                    body,
                                    jumps_map(|c| ctx_rshift_num(ncols(mat), &c), &total_i),
                                    ctx,
                                    rem,
                                )
                            }
                            Some((_, args)) => {
                                // OCaml `compiler/ml/matching.ml:2375-2388`
                                // skips a handler when `raw_action r` is a
                                // different static raise.
                                drop(args);
                                do_rec(compile_fun, r, total_r, ctx, rem)
                            }
                            None => do_rec(
                                compile_fun,
                                MatchCode::static_catch(r, (*i, vars.clone()), handler_i),
                                jumps_union(
                                    &jumps_remove(*i, &total_r),
                                    &jumps_map(|c| ctx_rshift_num(ncols(mat), &c), &total_i),
                                ),
                                ctx,
                                rem,
                            ),
                        }
                    }
                    Err(Unused) => do_rec(
                        compile_fun,
                        MatchCode::static_catch(
                            r,
                            (*i, vars.clone()),
                            MatchCode::raw(lambda_unit()),
                        ),
                        total_r,
                        ctx,
                        rem,
                    ),
                }
            }
        }
    }

    do_rec(compile_fun, lambda1, total1, ctx, to_catch)
}

/// Compile a test (divide + combine pattern).
/// Equivalent to OCaml's `compile_test`.
fn compile_test<K: Clone>(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(MatchCode, Jumps), Unused>,
    partial: &Partial,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> Vec<(K, MatchCell)>,
    combine_fn: &mut dyn FnMut(
        &[Ctx],
        &DefaultEnv,
        (Vec<(K, MatchCode)>, Jumps, Vec<Pattern>),
    ) -> (RawLambda, Jumps),
    ctx: &[Ctx],
    to_match: &PatternMatching,
) -> Result<(MatchCode, Jumps), Unused> {
    let division = divide_fn(ctx, to_match);
    let c_div = compile_list(compile_fun, division)?;
    match &c_div {
        (list, _, _) if list.is_empty() => {
            match mk_failaction_neg(partial, ctx, &to_match.default) {
                (None, _) => Err(Unused),
                (Some(l), total) => Ok((MatchCode::raw(l), total)),
            }
        }
        _ => {
            let (lambda, jumps) = combine_fn(ctx, &to_match.default, c_div);
            Ok((MatchCode::raw(lambda), jumps))
        }
    }
}

/// Check if v approximately appears in lam.
/// Equivalent to OCaml's `approx_present`.
fn approx_present(v: &Ident, lam: &RawLambda) -> bool {
    match lam {
        RawLambda::Lconst(_) | RawLambda::LglobalModule(_, _) => false,
        RawLambda::LstaticRaise(_, args) => args.iter().any(|a| approx_present(v, a)),
        RawLambda::Lprim(info) => info.args.iter().any(|a| approx_present(v, a)),
        RawLambda::Llet(LetKind::Alias, _, l1, l2) => {
            approx_present(v, l1) || approx_present(v, l2)
        }
        RawLambda::Lvar(vv) => v.same(vv),
        _ => true,
    }
}

/// Lower a binding into the appropriate branch.
/// Equivalent to OCaml's `lower_bind`.
fn lower_bind(v: &Ident, arg: &RawLambda, lam: RawLambda) -> RawLambda {
    // OCaml `compiler/ml/matching.ml:2413-2435` rebuilds only the branch that
    // needs the alias binding. Pattern-match the Rust value by ownership so
    // unchanged subtrees move through instead of recursively cloning the
    // already-built raw lambda.
    match lam {
        RawLambda::LifThenElse(cond, ifso, ifnot) => {
            let pcond = approx_present(v, &cond);
            let pso = approx_present(v, &ifso);
            let pnot = approx_present(v, &ifnot);
            match (pcond, pso, pnot) {
                (false, false, false) => RawLambda::LifThenElse(cond, ifso, ifnot),
                (false, true, false) => {
                    RawLambda::LifThenElse(cond, Box::new(lower_bind(v, arg, *ifso)), ifnot)
                }
                (false, false, true) => {
                    RawLambda::LifThenElse(cond, ifso, Box::new(lower_bind(v, arg, *ifnot)))
                }
                _ => bind(
                    LetKind::Alias,
                    v,
                    arg,
                    RawLambda::LifThenElse(cond, ifso, ifnot),
                ),
            }
        }
        RawLambda::Lswitch(ls, mut sw, loc) => {
            if sw.sw_consts.len() == 1 && sw.sw_blocks.is_empty() && !approx_present(v, &ls) {
                let (i, act) = sw.sw_consts.pop().expect("single const switch branch");
                sw.sw_consts.push((i, lower_bind(v, arg, act)));
                RawLambda::Lswitch(ls, sw, loc)
            } else if sw.sw_consts.is_empty() && sw.sw_blocks.len() == 1 && !approx_present(v, &ls)
            {
                let (i, act) = sw.sw_blocks.pop().expect("single block switch branch");
                sw.sw_blocks.push((i, lower_bind(v, arg, act)));
                RawLambda::Lswitch(ls, sw, loc)
            } else {
                bind(LetKind::Alias, v, arg, RawLambda::Lswitch(ls, sw, loc))
            }
        }
        RawLambda::Llet(LetKind::Alias, vv, lv, l) => {
            if approx_present(v, &lv) {
                bind(
                    LetKind::Alias,
                    v,
                    arg,
                    RawLambda::Llet(LetKind::Alias, vv, lv, l),
                )
            } else {
                RawLambda::Llet(LetKind::Alias, vv, lv, Box::new(lower_bind(v, arg, *l)))
            }
        }
        RawLambda::Lvar(u) if u.same(v) && u.name() == "*sth*" => {
            arg.clone() // eliminate let *sth* = from_option x in *sth*
        }
        other => bind(LetKind::Alias, v, arg, other),
    }
}

fn approx_present_action(v: &Ident, action: &MatchAction) -> bool {
    match &action.0.kind {
        MatchActionKind::Raw(raw) => approx_present(v, raw),
        MatchActionKind::Bind {
            kind: LetKind::Alias,
            arg,
            action,
            ..
        } => approx_present(v, arg) || approx_present_action(v, action),
        MatchActionKind::Bind { .. } => true,
    }
}

fn approx_present_code(v: &Ident, code: &MatchCode) -> bool {
    match code {
        MatchCode::Action(action) => approx_present_action(v, action),
        MatchCode::If {
            condition,
            ifso,
            ifnot,
        } => {
            approx_present(v, condition)
                || approx_present_code(v, ifso)
                || approx_present_code(v, ifnot)
        }
        MatchCode::Bind {
            kind: LetKind::Alias,
            arg,
            body,
            ..
        } => approx_present(v, arg) || approx_present_code(v, body),
        MatchCode::StaticCatch { .. } | MatchCode::Bind { .. } => true,
    }
}

fn lower_bind_action(v: &Ident, arg: &RawLambda, action: MatchAction) -> MatchCode {
    match &action.0.kind {
        MatchActionKind::Bind {
            kind: LetKind::Alias,
            id,
            arg: value,
            action: body,
        } => {
            if approx_present(v, value) {
                MatchCode::Action(action).bind(LetKind::Alias, v.clone(), arg.clone())
            } else {
                lower_bind_action(v, arg, body.clone()).bind(
                    LetKind::Alias,
                    id.clone(),
                    value.clone(),
                )
            }
        }
        MatchActionKind::Bind { .. } => {
            MatchCode::Action(action).bind(LetKind::Alias, v.clone(), arg.clone())
        }
        MatchActionKind::Raw(RawLambda::Lvar(u)) if u.same(v) && u.name() == "*sth*" => {
            MatchCode::raw(arg.clone())
        }
        MatchActionKind::Raw(RawLambda::LifThenElse(condition, ifso, ifnot)) => {
            let present = (
                approx_present(v, condition),
                approx_present(v, ifso),
                approx_present(v, ifnot),
            );
            match present {
                (false, false, false) => MatchCode::Action(action),
                (false, true, false) | (false, false, true) => {
                    MatchCode::raw(lower_bind(v, arg, action.into_raw()))
                }
                _ => MatchCode::Action(action).bind(LetKind::Alias, v.clone(), arg.clone()),
            }
        }
        MatchActionKind::Raw(RawLambda::Lswitch(selector, switch, _))
            if !approx_present(v, selector)
                && ((switch.sw_consts.len() == 1 && switch.sw_blocks.is_empty())
                    || (switch.sw_consts.is_empty() && switch.sw_blocks.len() == 1)) =>
        {
            MatchCode::raw(lower_bind(v, arg, action.into_raw()))
        }
        MatchActionKind::Raw(_) => {
            MatchCode::Action(action).bind(LetKind::Alias, v.clone(), arg.clone())
        }
    }
}

/// OCaml `lower_bind` over the owned match-code spine. Terminal actions remain
/// shared until a branch actually has to be rewritten.
fn lower_bind_code(v: &Ident, arg: &RawLambda, code: MatchCode) -> MatchCode {
    match code {
        MatchCode::If {
            condition,
            ifso,
            ifnot,
        } => {
            let pcond = approx_present(v, &condition);
            let pso = approx_present_code(v, &ifso);
            let pnot = approx_present_code(v, &ifnot);
            match (pcond, pso, pnot) {
                (false, false, false) => MatchCode::If {
                    condition,
                    ifso,
                    ifnot,
                },
                (false, true, false) => MatchCode::If {
                    condition,
                    ifso: Box::new(lower_bind_code(v, arg, *ifso)),
                    ifnot,
                },
                (false, false, true) => MatchCode::If {
                    condition,
                    ifso,
                    ifnot: Box::new(lower_bind_code(v, arg, *ifnot)),
                },
                _ => MatchCode::If {
                    condition,
                    ifso,
                    ifnot,
                }
                .bind(LetKind::Alias, v.clone(), arg.clone()),
            }
        }
        MatchCode::Bind {
            kind: LetKind::Alias,
            id,
            arg: value,
            body,
        } => {
            if approx_present(v, &value) {
                MatchCode::Bind {
                    kind: LetKind::Alias,
                    id,
                    arg: value,
                    body,
                }
                .bind(LetKind::Alias, v.clone(), arg.clone())
            } else {
                MatchCode::Bind {
                    kind: LetKind::Alias,
                    id,
                    arg: value,
                    body: Box::new(lower_bind_code(v, arg, *body)),
                }
            }
        }
        MatchCode::Action(action) => lower_bind_action(v, arg, action),
        other => other.bind(LetKind::Alias, v.clone(), arg.clone()),
    }
}

/// Bind with check, preserving OCaml's wrapper and alias-lowering order without
/// first materializing the complete match result.
fn bind_check_code(str_kind: LetKind, v: &Ident, arg: &RawLambda, code: MatchCode) -> MatchCode {
    match (&str_kind, arg) {
        (_, RawLambda::Lvar(_)) => code.bind(str_kind, v.clone(), arg.clone()),
        (LetKind::Alias, _) => lower_bind_code(v, arg, code),
        _ => code.bind(str_kind, v.clone(), arg.clone()),
    }
}

/// Compile the default/exit case.
/// Equivalent to OCaml's `comp_exit`.
fn comp_exit(ctx: &[Ctx], m: &PatternMatching) -> Result<(MatchCode, Jumps), Unused> {
    match m.default.first() {
        Some((_, i)) => Ok((
            MatchCode::raw(RawLambda::LstaticRaise(*i, Vec::new())),
            jumps_singleton(*i, ctx.to_vec()),
        )),
        None => panic!("Matching.comp_exit"),
    }
}

/// Compile a match with multiple handlers (for split results).
/// Equivalent to OCaml's `comp_match_handlers`.
fn comp_match_handlers(
    comp_fun: &mut dyn FnMut(
        &Partial,
        &[Ctx],
        &RawLambda,
        &PmHalfCompiled,
    ) -> Result<(MatchCode, Jumps), Unused>,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    first_match: &PmHalfCompiled,
    next_matchs: &[(i32, PmHalfCompiled)],
) -> Result<(MatchCode, Jumps), Unused> {
    if next_matchs.is_empty() {
        return comp_fun(partial, ctx, arg, first_match);
    }

    // OCaml `compiler/ml/matching.ml:2448-2482` recurses over `next_matchs`
    // structurally by sharing the tail list. Borrow the Rust slice for the
    // same control flow instead of cloning precompiled match trees.
    match comp_fun(&Partial::Partial, ctx, arg, first_match) {
        Ok((first_lam, total)) => c_rec(comp_fun, partial, ctx, arg, first_lam, total, next_matchs),
        Err(Unused) => match next_matchs.split_first() {
            None => Err(Unused),
            Some(((_, x), xs)) => comp_match_handlers(comp_fun, partial, ctx, arg, x, xs),
        },
    }
}

/// Inner recursive function for comp_match_handlers.
fn c_rec(
    comp_fun: &mut dyn FnMut(
        &Partial,
        &[Ctx],
        &RawLambda,
        &PmHalfCompiled,
    ) -> Result<(MatchCode, Jumps), Unused>,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    body: MatchCode,
    total_body: Jumps,
    rest: &[(i32, PmHalfCompiled)],
) -> Result<(MatchCode, Jumps), Unused> {
    match rest.split_first() {
        None => Ok((body, total_body)),
        Some(((i, pm), rem)) => {
            let (ctx_i, total_rem) = jumps_extract(*i, &total_body);
            if ctx_i.is_empty() {
                c_rec(comp_fun, partial, ctx, arg, body, total_body, rem)
            } else {
                let this_partial = if rem.is_empty() {
                    partial.clone()
                } else {
                    Partial::Partial
                };
                match comp_fun(&this_partial, &ctx_i, arg, pm) {
                    Ok((li, total_i)) => c_rec(
                        comp_fun,
                        partial,
                        ctx,
                        arg,
                        MatchCode::static_catch(body, (*i, Vec::new()), li),
                        jumps_union(&total_i, &total_rem),
                        rem,
                    ),
                    Err(Unused) => c_rec(
                        comp_fun,
                        partial,
                        ctx,
                        arg,
                        MatchCode::static_catch(
                            body,
                            (*i, Vec::new()),
                            MatchCode::raw(lambda_unit()),
                        ),
                        total_rem,
                        rem,
                    ),
                }
            }
        }
    }
}

/// Find a reasonable name for the match variable from the first pattern.
/// Equivalent to OCaml's `name_pattern`.
fn name_pattern(ctx_ref: &TypeContext, default: &str, cases: &[Clause]) -> Ident {
    for (pats, _) in cases {
        if let Some(pat) = pats.first() {
            if let Some(id) = id_of_pattern(ctx_ref, pat) {
                return id;
            }
        }
    }
    ctx_ref.create_ident(default)
}

/// Extract an identifier from a pattern (for naming purposes).
/// Equivalent to OCaml's `Typecore.id_of_pattern`.
fn id_of_pattern(ctx_ref: &TypeContext, pat: &Pattern) -> Option<Ident> {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id.clone()),
        PatternDesc::Tpat_alias(_, id, _) => Some(id.clone()),
        PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => match &args[0].pat_desc {
            PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                Some(ctx_ref.rename_ident(id))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Convert arg to a variable (bind if not already a variable).
/// Equivalent to OCaml's `arg_to_var`.
fn arg_to_var(ctx_ref: &TypeContext, arg: &RawLambda, cls: &[Clause]) -> (Ident, RawLambda) {
    match arg {
        RawLambda::Lvar(v) => (v.clone(), arg.clone()),
        _ => {
            let v = name_pattern(ctx_ref, "match", cls);
            (v.clone(), RawLambda::Lvar(v))
        }
    }
}

/// Lambda unit value.
/// Equivalent to OCaml's `Lambda.lambda_unit`.
fn lambda_unit() -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::JsUndefined { is_unit: true })
}

/// Patch a guarded action: replace the guard's static raise(0,[]) with the patch lambda.
/// Equivalent to OCaml's `Lambda.patch_guarded`.
fn patch_guarded(patch: RawLambda, lam: &RawLambda) -> RawLambda {
    match lam {
        RawLambda::LifThenElse(cond, body, else_br) => match else_br.as_ref() {
            RawLambda::LstaticRaise(0, args) if args.is_empty() => {
                RawLambda::LifThenElse(cond.clone(), body.clone(), Box::new(patch))
            }
            _ => panic!("patch_guarded: unexpected else branch"),
        },
        RawLambda::Llet(kind, id, lam_inner, body) => RawLambda::Llet(
            *kind,
            id.clone(),
            lam_inner.clone(),
            Box::new(patch_guarded(patch, body)),
        ),
        _ => panic!("patch_guarded: unexpected lambda"),
    }
}

/// The main compilation function.
/// Input:
///   repr=used for inserting debug events (unused in ReScript)
///   partial=exhaustiveness information
///   ctx=a context
///   m=a pattern matching
/// Output: a lambda term, a jump summary
///
/// Equivalent to OCaml's `compile_match`.
fn compile_match(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    _repr: Option<()>,
    partial: &Partial,
    ctx: &[Ctx],
    m: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(MatchCode, Jumps), Unused> {
    match (m.cases.as_slice(), m.args.as_slice()) {
        ([], []) => comp_exit(ctx, m),
        ([(pats, action), rem @ ..], _) if pats.is_empty() => {
            if action.is_guarded() {
                let remaining = PatternMatching {
                    cases: rem.to_vec(),
                    args: m.args.clone(),
                    default: m.default.clone(),
                };
                let (lambda, total) = compile_match(
                    ctx_ref,
                    arena,
                    None,
                    partial,
                    ctx,
                    &remaining,
                    next_raise_count,
                )?;
                Ok((
                    MatchCode::raw(action.patch_guarded(lambda.into_raw())),
                    total,
                ))
            } else {
                Ok((MatchCode::Action(action.clone()), jumps_empty()))
            }
        }
        (_, [(arg, str_kind), argl @ ..]) => {
            let (v, newarg) = arg_to_var(ctx_ref, arg, &m.cases);
            let new_args = {
                let mut a = vec![(newarg.clone(), LetKind::Alias)];
                a.extend(argl.iter().cloned());
                a
            };
            let new_pm = PatternMatching {
                cases: m.cases.clone(),
                args: MatchArgs::new(new_args),
                default: m.default.clone(),
            };
            let (first_match, rem) =
                split_precompile(Some(ctx_ref), &Some(v.clone()), &new_pm, next_raise_count);

            let mut comp_fn = |partial: &Partial,
                               ctx: &[Ctx],
                               arg: &RawLambda,
                               pmh: &PmHalfCompiled|
             -> Result<(MatchCode, Jumps), Unused> {
                do_compile_matching(ctx_ref, arena, partial, ctx, arg, pmh, next_raise_count)
            };

            let (lam, total) =
                comp_match_handlers(&mut comp_fn, partial, ctx, &newarg, &first_match, &rem)?;
            Ok((bind_check_code(*str_kind, &v, arg, lam), total))
        }
        (cases, []) if !cases.is_empty() => {
            // Cases exist but no args — shouldn't happen normally.
            // Return the first non-guarded action if available.
            for (_, act) in cases {
                if !act.is_guarded() {
                    return Ok((MatchCode::Action(act.clone()), jumps_empty()));
                }
            }
            Err(Unused)
        }
        _ => panic!("Matching.compile_match"),
    }
}

/// Main dispatch for compiling half-compiled pattern matchings.
/// Equivalent to OCaml's `do_compile_matching`.
fn do_compile_matching(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    pmh: &PmHalfCompiled,
    next_raise_count: &mut i32,
) -> Result<(MatchCode, Jumps), Unused> {
    match pmh {
        PmHalfCompiled::Pm(pm) => {
            let pat = what_is_cases(&pm.cases);
            match &pat.pat_desc {
                PatternDesc::Tpat_any => compile_no_test(
                    ctx_ref,
                    arena,
                    &|ctx, pm| divide_var(ctx, pm),
                    &|ctx| ctx_rshift(ctx),
                    partial,
                    ctx,
                    pm,
                    next_raise_count,
                ),
                PatternDesc::Tpat_tuple(patl) => {
                    let arity = patl.len();
                    let norm_pat = normalize_pat(&pat);
                    compile_no_test(
                        ctx_ref,
                        arena,
                        &move |ctx, pm| divide_tuple(arena, arity, &norm_pat, ctx, pm),
                        &|ctx| ctx_combine(ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_record(fields, _, _) if !fields.is_empty() => {
                    let all_labels = resolve_all_record_labels(ctx_ref, &pat, fields);
                    let norm_pat = normalize_pat(&pat);
                    compile_no_test(
                        ctx_ref,
                        arena,
                        &move |ctx, pm| {
                            divide_record(ctx_ref, arena, &all_labels, &norm_pat, ctx, pm)
                        },
                        &|ctx| ctx_combine(ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_constant(cst) => {
                    let names: Option<crate::lambda::SwitchDispatch> = None;
                    let loc = arena.to_location(pat.pat_loc);
                    let arg_clone = arg.clone();
                    let cst_clone = cst.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        arena,
                        partial,
                        &|ctx, pm| divide_constant(ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constant(
                                names.clone(),
                                loc.clone(),
                                arg_clone.clone(),
                                &cst_clone,
                                partial,
                                ctx,
                                def,
                                materialize_compiled_div(c_div),
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_construct(_, cstr, _) => {
                    let loc = arena.to_location(pat.pat_loc);
                    let arg_clone = arg.clone();
                    let ex_pat = pat.clone();
                    let cstr_clone = cstr.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        arena,
                        partial,
                        &|ctx, pm| divide_constructor(ctx_ref, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constructor(
                                ctx_ref,
                                loc.clone(),
                                arg_clone.clone(),
                                &ex_pat,
                                &cstr_clone,
                                partial,
                                ctx,
                                def,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_array(_) => {
                    let names: Option<crate::lambda::SwitchDispatch> = None;
                    let loc = arena.to_location(pat.pat_loc);
                    let arg_clone = arg.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        arena,
                        partial,
                        &|ctx, pm| divide_array(ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_array(
                                ctx_ref,
                                names.clone(),
                                loc.clone(),
                                arg_clone.clone(),
                                partial,
                                ctx,
                                def,
                                materialize_compiled_div(c_div),
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_variant(_, _, _row_ref) => {
                    let names: Option<crate::lambda::SwitchDispatch> = None;
                    let loc = arena.to_location(pat.pat_loc);
                    let arg_clone = arg.clone();
                    let row_desc =
                        extract_row_from_type_with_env(ctx_ref, pat.pat_type, pat.pat_env);
                    let row_desc2 = row_desc.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        arena,
                        partial,
                        &move |ctx, pm| divide_variant(ctx_ref, &row_desc, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_variant(
                                ctx_ref,
                                names.clone(),
                                loc.clone(),
                                &row_desc2,
                                arg_clone.clone(),
                                partial,
                                ctx,
                                def,
                                materialize_compiled_div(c_div),
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                _ => panic!("do_compile_matching: unexpected pattern"),
            }
        }
        PmHalfCompiled::PmVar(PmVarCompiled { inside, var_arg }) => {
            let (lam, total) = do_compile_matching(
                ctx_ref,
                arena,
                partial,
                &ctx_lshift(ctx),
                var_arg,
                inside,
                next_raise_count,
            )?;
            Ok((lam, jumps_map(|c| ctx_rshift(&c), &total)))
        }
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) =
                compile_match(ctx_ref, arena, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn =
                |ctx: &[Ctx], pm: &PatternMatching| -> Result<(MatchCode, Jumps), Unused> {
                    compile_match(ctx_ref, arena, None, partial, ctx, pm, next_raise_count)
                };
            Ok(compile_orhandlers(
                &mut compile_fn,
                lam,
                total,
                ctx,
                handlers,
            ))
        }
    }
}

/// Compile without test (divide_line + compile_match).
/// Equivalent to OCaml's `compile_no_test`.
fn compile_no_test(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> MatchCell,
    up_ctx: &dyn Fn(&[Ctx]) -> Vec<Ctx>,
    partial: &Partial,
    ctx: &[Ctx],
    to_match: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(MatchCode, Jumps), Unused> {
    let cell = divide_fn(ctx, to_match);
    let (lambda, total) = compile_match(
        ctx_ref,
        arena,
        None,
        partial,
        &cell.ctx,
        &cell.pm,
        next_raise_count,
    )?;
    Ok((lambda, jumps_map(|c| up_ctx(&c), &total)))
}

/// Wrapper for compile_test that handles the type-specific divide and combine.
/// This replaces the OCaml pattern of passing `compile_match repr partial` as a function.
///
/// We inline compile_test here to avoid borrow conflicts with next_raise_count
/// being captured by both compile_fn and combine_fn closures.
fn compile_test_wrapper<K: Clone>(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    partial: &Partial,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> Vec<(K, MatchCell)>,
    combine_fn: &dyn Fn(
        &[Ctx],
        &DefaultEnv,
        (Vec<(K, MatchCode)>, Jumps, Vec<Pattern>),
        &mut i32,
    ) -> (RawLambda, Jumps),
    ctx: &[Ctx],
    pm: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(MatchCode, Jumps), Unused> {
    let raise_counter = std::cell::Cell::new(*next_raise_count);

    // Step 1: divide
    let division = divide_fn(ctx, pm);

    // Step 2: compile_list
    let c_div = {
        let mut compile_fn =
            |ctx: &[Ctx], pm: &PatternMatching| -> Result<(MatchCode, Jumps), Unused> {
                let mut next_raise = raise_counter.get();
                let result = compile_match(ctx_ref, arena, None, partial, ctx, pm, &mut next_raise);
                raise_counter.set(next_raise);
                result
            };
        compile_list(&mut compile_fn, division)?
    };

    // Step 3: combine
    let result = match &c_div {
        (list, _, _) if list.is_empty() => match mk_failaction_neg(partial, ctx, &pm.default) {
            (None, _) => Err(Unused),
            (Some(l), total) => Ok((MatchCode::raw(l), total)),
        },
        _ => {
            let mut next_raise = raise_counter.get();
            let (lambda, jumps) = combine_fn(ctx, &pm.default, c_div, &mut next_raise);
            raise_counter.set(next_raise);
            Ok((MatchCode::raw(lambda), jumps))
        }
    };
    *next_raise_count = raise_counter.get();
    result
}

/// Extract all record label descriptions from a Tpat_record pattern's fields.
/// Sorted by field position (lbl_pos).
fn get_all_labels_from_record_fields(
    fields: &[(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        LabelDescription,
        Pattern,
        bool,
    )],
) -> Vec<LabelDescription> {
    let mut labels: Vec<LabelDescription> =
        fields.iter().map(|(_, lbl, _, _)| lbl.clone()).collect();
    labels.sort_by_key(|l| l.lbl_pos);
    labels
}

/// Resolve ALL record labels from the record type, not just those mentioned in the pattern.
/// This is the equivalent of OCaml's `lbl.lbl_all` which points to all labels of the record type.
/// We look up the type declaration via the TypeContext to get all labels.
fn resolve_all_record_labels(
    ctx_ref: &TypeContext,
    pat: &Pattern,
    fields: &[(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        LabelDescription,
        Pattern,
        bool,
    )],
) -> Vec<LabelDescription> {
    if fields.is_empty() {
        return Vec::new();
    }

    let first_lbl = &fields[0].1;

    // OCaml passes `lbl.lbl_all` from the typed pattern directly to
    // `divide_record` (compiler/ml/matching.ml:2564-2568). Rust reconstructs
    // that array, so reject loose lookups that do not include the labels from
    // the already-typed pattern.
    if let Some(all_labels) = resolve_labels_from_type(ctx_ref, first_lbl.lbl_res, pat.pat_env)
        .filter(|labels| record_labels_cover_pattern_fields(labels, fields))
    {
        return all_labels;
    }

    // Try via pat_type
    if let Some(all_labels) = resolve_labels_from_type(ctx_ref, pat.pat_type, pat.pat_env)
        .filter(|labels| record_labels_cover_pattern_fields(labels, fields))
    {
        return all_labels;
    }

    // Fallback: return only mentioned fields (old behavior)
    get_all_labels_from_record_fields(fields)
}

fn record_labels_cover_pattern_fields(
    all_labels: &[LabelDescription],
    fields: &[(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        LabelDescription,
        Pattern,
        bool,
    )],
) -> bool {
    fields.iter().all(|(_, field_label, _, _)| {
        all_labels.iter().any(|label| {
            // OCaml carries the physical `lbl_all` array from typecore into
            // matching.ml:1417-1476, so source names and `@as` runtime names
            // are two views of the same label. Rust reconstructs that array
            // from caches that may store Lambda.find_name-style runtime names
            // (compiler/ml/lambda.ml:147-154); accept either spelling while
            // still requiring the declaration position to match.
            label.lbl_pos == field_label.lbl_pos
                && (label.lbl_name == field_label.lbl_name
                    || label_runtime_name_matching(label)
                        == label_runtime_name_matching(field_label))
        })
    })
}

fn label_descriptions_from_cached_entries(
    cached: Vec<(
        String,
        i32,
        MutableFlag,
        RecordRepresentation,
        Vec<crate::types::decl::Attribute>,
    )>,
) -> Vec<LabelDescription> {
    cached
        .into_iter()
        .map(|(name, pos, mutflag, repr, attrs)| LabelDescription {
            lbl_name: name,
            lbl_res: TypeExprRef(0),
            lbl_arg: TypeExprRef(0),
            lbl_mut: mutflag,
            lbl_optional: true,
            lbl_pos: pos,
            lbl_all: crate::types::decl::LabelArrayRef(0),
            lbl_repres: repr,
            lbl_private: crate::types::asttypes::PrivateFlag::Public,
            lbl_loc: crate::location::Location::none(),
            lbl_attributes: attrs,
        })
        .collect()
}

/// Look up all LabelDescription entries for a record type.
fn resolve_labels_from_type(
    ctx_ref: &TypeContext,
    record_ty: TypeExprRef,
    env_ref: EnvRef,
) -> Option<Vec<LabelDescription>> {
    use crate::types::type_expr::TypeDesc;

    let ty = ctx_ref.repr(record_ty);
    let desc = ctx_ref.get_desc(ty);
    let (path, _args) = match &*desc {
        TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
        _ => return None,
    };
    drop(desc);

    if path.same(&crate::types::predef::path_dict()) {
        let cached = ctx_ref.get_dict_pattern_labels();
        if !cached.is_empty() {
            return Some(
                cached
                    .into_iter()
                    .map(|(name, pos, mutflag, repr, attrs)| LabelDescription {
                        lbl_name: name,
                        lbl_res: TypeExprRef(0),
                        lbl_arg: TypeExprRef(0),
                        lbl_mut: mutflag,
                        lbl_optional: true,
                        lbl_pos: pos,
                        lbl_all: crate::types::decl::LabelArrayRef(0),
                        lbl_repres: repr,
                        lbl_private: crate::types::asttypes::PrivateFlag::Public,
                        lbl_loc: crate::location::Location::none(),
                        lbl_attributes: attrs,
                    })
                    .collect(),
            );
        }
    }

    if let Some(labels) = ctx_ref.get_record_label_descriptions(&path) {
        return Some(labels.as_ref().clone());
    }

    // Match OCaml `lbl.lbl_all` use in compiler/ml/matching.ml:1417-1476.
    // Typecore registers this lightweight cache while reconstructing record
    // labels for raw lambda conversion, keyed by the exact type path
    // (including stamps). Prefer it before any declaration-name fallback.
    if let Some(labels) = ctx_ref.get_record_labels(&path) {
        return Some(label_descriptions_from_cached_entries(labels));
    }

    // Try env lookup first
    let env = ctx_ref.get_typed_env(env_ref)?;
    if let Ok(decl) = env.lookup_type(&path) {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }

    if let crate::types::Path::Pident(ref id) = path {
        if id.stamp() != 0 {
            if let Some(decl) = ctx_ref.find_type_decl_by_stamp(id.stamp()) {
                if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
                    return Some(build_label_descriptions(labels, repr, decl.type_private));
                }
            }
        }
    }

    // Try exact type_ctx stores. OCaml's `lbl_all` is already exact
    // (compiler/ml/typecore.ml:2802); avoid falling back from `A.B.t` to any
    // same-last-name `t`, which can attach another record's debug labels.
    if let Some(decl) = ctx_ref.find_type_decl_by_path(&path.name()) {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }
    if matches!(path, crate::types::Path::Pident(_))
        && let Some(decl) = ctx_ref.find_type_decl(path.last())
    {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }

    // Extension/exception inline records use the constructor path itself
    // (for example `A0`) rather than a parent-type `Pdot`, so reconstruct
    // their full label set from the constructor's synthetic inline record.
    for cstr in env.find_all_constructors(&path.last()).iter().rev() {
        let matches_inline_record_path = match &cstr.cstr_kind {
            crate::types::ConstructorKind::Extension(ext_path) => ext_path.same(&path),
            crate::types::ConstructorKind::Ordinary(_) => false,
        };
        if !matches_inline_record_path {
            continue;
        }
        if let Some(inlined) = &cstr.cstr_inlined {
            if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = inlined.type_kind {
                return Some(build_label_descriptions(labels, repr, inlined.type_private));
            }
        }
    }

    // Handle inline records: path is Pdot(parent_type, constructor_name, _)
    // Look up the parent type declaration and find the constructor's inline record
    if let crate::types::Path::Pdot(ref parent_path, ref cstr_name, _) = path {
        // Try to find the parent type declaration
        let parent_decl = env
            .lookup_type(parent_path)
            .ok()
            .cloned()
            .or_else(|| {
                ctx_ref
                    .find_type_decl_by_path(&parent_path.name())
                    .map(|d| d.clone())
            })
            .or_else(|| {
                ctx_ref
                    .find_type_decl(&parent_path.last())
                    .map(|d| d.clone())
            })
            .or_else(|| {
                if let crate::types::Path::Pident(ref id) = **parent_path {
                    if id.stamp() != 0 {
                        ctx_ref
                            .find_type_decl_by_stamp(id.stamp())
                            .map(|d| d.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            });
        if let Some(parent_decl) = parent_decl {
            if let crate::types::TypeKind::TypeVariant(ref constrs, layout) = parent_decl.type_kind
            {
                for (position, cd) in constrs.iter().enumerate() {
                    if cd.cd_id.name() == cstr_name.as_str() {
                        if let crate::types::ConstructorArguments::CstrRecord(ref labels) =
                            cd.cd_args
                        {
                            let repr = RecordRepresentation::RecordInlined {
                                name: cstr_name.to_string(),
                                representation: crate::types::ConstructorReference {
                                    variant: layout,
                                    position,
                                },
                            };
                            return Some(build_label_descriptions(
                                labels,
                                &repr,
                                parent_decl.type_private,
                            ));
                        }
                    }
                }
            }
        }
    }

    None
}

fn build_label_descriptions(
    labels: &[crate::types::decl::LabelDeclaration],
    repr: &RecordRepresentation,
    private: crate::types::asttypes::PrivateFlag,
) -> Vec<LabelDescription> {
    labels
        .iter()
        .enumerate()
        .map(|(pos, ld)| {
            LabelDescription {
                lbl_name: ld.ld_id.name().to_string(),
                lbl_res: TypeExprRef(0), // Not used by matching
                lbl_arg: ld.ld_type,
                lbl_mut: ld.ld_mutable,
                lbl_optional: ld.ld_optional,
                lbl_pos: pos as i32,
                lbl_all: crate::types::decl::LabelArrayRef(0),
                lbl_repres: repr.clone(),
                lbl_private: private,
                lbl_loc: ld.ld_loc.clone(),
                lbl_attributes: ld.ld_attributes.clone(),
            }
        })
        .collect()
}

/// Extract a RowDesc from a type expression (for variant matching).
/// Follows type links to find the Tvariant row.
/// Extract variant row with env-based expansion (preferred).
fn extract_row_from_type_with_env(
    ctx_ref: &TypeContext,
    ty: TypeExprRef,
    env_ref: crate::types::typedtree::EnvRef,
) -> RowDesc {
    use crate::types::btype;
    use crate::types::type_expr::TypeDesc;

    // First try expanding with the environment
    if let Some(env) = ctx_ref.get_typed_env(env_ref) {
        let expanded = crate::types::ctype::expand_head(ctx_ref, env.as_ref(), ty);
        let desc = ctx_ref.get_desc(expanded);
        if let TypeDesc::Tvariant(row) = &*desc {
            return btype::row_repr(ctx_ref, row);
        }
    }

    // Fall back to stamp/path-based lookup
    extract_row_from_type(ctx_ref, ty)
}

fn extract_row_from_type(ctx_ref: &TypeContext, ty: TypeExprRef) -> RowDesc {
    use crate::types::btype;
    use crate::types::type_expr::TypeDesc;

    // Expand through links, Tconstr, and row_more to find the variant row
    let mut current = ctx_ref.repr(ty);
    'outer: for _ in 0..20 {
        enum Action {
            ReturnRow(RowDesc),
            ExpandConstr(i32, String),
            Follow(TypeExprRef),
            Stop,
        }
        let action = {
            let desc = ctx_ref.get_desc(current);
            match &*desc {
                TypeDesc::Tvariant(row) => Action::ReturnRow(btype::row_repr(ctx_ref, row)),
                TypeDesc::Tconstr { path, .. } => {
                    let stamp = match path {
                        crate::types::Path::Pident(id) => id.stamp(),
                        _ => -1,
                    };
                    Action::ExpandConstr(stamp, path.name())
                }
                TypeDesc::Tlink(next) => Action::Follow(*next),
                _ => Action::Stop,
            }
        };
        match action {
            Action::ReturnRow(row) => return row,
            Action::ExpandConstr(stamp, path_name) => {
                if stamp >= 0 {
                    if let Some(decl) = ctx_ref.find_type_decl_by_stamp(stamp) {
                        if let Some(manifest) = decl.type_manifest {
                            current = ctx_ref.repr(manifest);
                            continue;
                        }
                    }
                }
                if let Some(decl) = ctx_ref.find_type_decl_by_path(&path_name) {
                    if let Some(manifest) = decl.type_manifest {
                        current = ctx_ref.repr(manifest);
                        continue;
                    }
                }
                break;
            }
            Action::Follow(next) => {
                current = ctx_ref.repr(next);
            }
            Action::Stop => break,
        }
    }

    // Fallback: empty row
    RowDesc {
        row_fields: Vec::new(),
        row_more: TypeExprRef(0),
        row_closed: true,
        row_fixed: false,
        row_name: None,
    }
}

// ============================================================================
// Layer 11: Entry points — OCaml matching.ml lines 2631-2978
// ============================================================================

/// Find if a predicate holds for any sub-pattern description.
/// Equivalent to OCaml's `find_in_pat`.
fn find_in_pat(pred: &dyn Fn(&PatternDesc) -> bool, p: &Pattern) -> bool {
    if pred(&p.pat_desc) {
        return true;
    }
    match &p.pat_desc {
        PatternDesc::Tpat_alias(p, _, _) | PatternDesc::Tpat_variant(_, Some(p), _) => {
            find_in_pat(pred, p)
        }
        PatternDesc::Tpat_tuple(ps)
        | PatternDesc::Tpat_construct(_, _, ps)
        | PatternDesc::Tpat_array(ps) => ps.iter().any(|p| find_in_pat(pred, p)),
        PatternDesc::Tpat_record(lpats, _, _) => {
            lpats.iter().any(|(_, _, p, _)| find_in_pat(pred, p))
        }
        PatternDesc::Tpat_or(p, q, _) => find_in_pat(pred, p) || find_in_pat(pred, q),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_var(_, _)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => false,
    }
}

/// Check if a pattern description accesses mutable record fields.
/// Equivalent to OCaml's `have_mutable_field`.
fn have_mutable_field(p: &PatternDesc) -> bool {
    match p {
        PatternDesc::Tpat_record(lps, _, _) => lps
            .iter()
            .any(|(_, lbl, _, _)| matches!(lbl.lbl_mut, MutableFlag::Mutable)),
        _ => false,
    }
}

/// Check if a pattern accesses mutable fields anywhere.
/// Equivalent to OCaml's `is_mutable`.
fn is_mutable(p: &Pattern) -> bool {
    find_in_pat(&have_mutable_field, p)
}

/// Downgrade Total to Partial when needed.
/// Equivalent to OCaml's `check_partial` (single pattern version).
fn check_partial_single(pat_act_list: &[(Pattern, RawLambda)], partial: Partial) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || pat_act_list
                    .iter()
                    .any(|(pat, lam)| is_mutable(pat) && is_guarded(lam))
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Downgrade Total to Partial when needed (list of patterns version).
/// Equivalent to OCaml's `check_partial_list`.
fn check_partial_list(pat_act_list: &[Clause], partial: Partial) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || pat_act_list
                    .iter()
                    .any(|(pats, lam)| pats.iter().any(|p| is_mutable(p)) && lam.is_guarded())
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Create a starting context of n wildcards.
/// Equivalent to OCaml's `start_ctx`.
fn start_ctx(n: usize) -> Vec<Ctx> {
    vec![Ctx {
        left: Vec::new(),
        right: omegas(n),
    }]
}

/// Check total: add a catch handler if jumps are not empty.
/// Equivalent to OCaml's `check_total`.
fn check_total(
    total: &Jumps,
    lambda: RawLambda,
    i: i32,
    handler_fun: impl FnOnce() -> RawLambda,
) -> RawLambda {
    if jumps_is_empty(total) {
        lambda
    } else {
        RawLambda::LstaticCatch(Box::new(lambda), (i, Vec::new()), Box::new(handler_fun()))
    }
}

/// Compile a matching with error handler.
/// Equivalent to OCaml's `compile_matching`.
pub fn compile_matching(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    handler_fun: impl FnOnce() -> RawLambda,
    arg: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let partial = check_partial_single(&pat_act_list, partial);
    match partial {
        Partial::Partial => {
            let raise_num = bump_raise_count(next_raise_count, "matching::compile_matching");
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], MatchAction::new(act)))
                    .collect(),
                args: MatchArgs::new(vec![(arg, LetKind::Strict)]),
                default: vec![(vec![vec![omega()]], raise_num)],
            };
            match compile_match(
                ctx_ref,
                arena,
                None,
                &partial,
                &start_ctx(1),
                &pm,
                next_raise_count,
            ) {
                Ok((lambda, total)) => {
                    check_total(&total, lambda.into_raw(), raise_num, handler_fun)
                }
                Err(Unused) => panic!("compile_matching: Unused"),
            }
        }
        Partial::Total => {
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], MatchAction::new(act)))
                    .collect(),
                args: MatchArgs::new(vec![(arg, LetKind::Strict)]),
                default: Vec::new(),
            };
            match compile_match(
                ctx_ref,
                arena,
                None,
                &partial,
                &start_ctx(1),
                &pm,
                next_raise_count,
            ) {
                Ok((lambda, total)) => {
                    assert!(jumps_is_empty(&total));
                    lambda.into_raw()
                }
                Err(Unused) => {
                    // Shouldn't happen for Total matches, but handle gracefully
                    // by returning a unit value as placeholder.
                    lambda_unit()
                }
            }
        }
    }
}

/// Build a match failure exception raise.
/// Equivalent to OCaml's `partial_function`.
pub fn partial_function(_ctx_ref: &TypeContext, loc: Location) -> RawLambda {
    let line = loc.loc_start.line;
    let char_pos = loc.loc_start.column();
    // File name is stored as StrIdx; we use "" as placeholder since we can't
    // resolve it without the parse arena. The actual file name will be resolved
    // when this is called from convert.rs which has arena access.
    let fname = String::new();

    let match_failure_ident = crate::types::predef::ident_match_failure();
    let exn = RawLambda::LglobalModule(match_failure_ident, false);
    let payload = RawLambda::Lconst(crate::lambda::Constant::Block {
        tag_info: TagInfo::Tuple,
        elements: vec![
            crate::lambda::Constant::string(fname),
            crate::lambda::Constant::int(line),
            crate::lambda::Constant::int(char_pos),
        ],
    });

    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Praise,
        args: vec![RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
            args: vec![exn, payload],
            loc: loc.clone(),
        })],
        loc,
    })
}

/// Compile a match for a function body.
/// Equivalent to OCaml's `for_function`.
pub fn for_function(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    param: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let loc_clone = loc.clone();
    compile_matching(
        ctx_ref,
        arena,
        || partial_function(ctx_ref, loc_clone),
        param,
        pat_act_list,
        partial,
        next_raise_count,
    )
}

/// Compile a match for a try-with handler.
/// Equivalent to OCaml's `for_trywith`.
pub fn for_trywith(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    param: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let param_clone = param.clone();
    compile_matching(
        ctx_ref,
        arena,
        || {
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Praise,
                args: vec![param_clone],
                loc: Location::none(),
            })
        },
        param,
        pat_act_list,
        Partial::Partial,
        next_raise_count,
    )
}

/// Simple let matching.
/// Equivalent to OCaml's `simple_for_let`.
pub fn simple_for_let(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    param: RawLambda,
    pat: Pattern,
    body: RawLambda,
    next_raise_count: &mut i32,
) -> RawLambda {
    let loc_clone = loc.clone();
    compile_matching(
        ctx_ref,
        arena,
        || partial_function(ctx_ref, loc_clone),
        param,
        vec![(pat, body)],
        Partial::Partial,
        next_raise_count,
    )
}

/// Compile a let binding match (with optimization for simple cases).
/// Equivalent to OCaml's `for_let`.
pub fn for_let(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    param: RawLambda,
    pat: &Pattern,
    body: RawLambda,
    next_raise_count: &mut i32,
) -> RawLambda {
    match &pat.pat_desc {
        PatternDesc::Tpat_any => {
            // Eliminates a useless variable
            RawLambda::Lsequence(Box::new(param), Box::new(body))
        }
        PatternDesc::Tpat_var(id, _) => {
            // Fast path
            RawLambda::Llet(LetKind::Strict, id.clone(), Box::new(param), Box::new(body))
        }
        _ => simple_for_let(
            ctx_ref,
            arena,
            loc,
            param,
            pat.clone(),
            body,
            next_raise_count,
        ),
    }
}

/// Compile a tupled function match.
/// Equivalent to OCaml's `for_tupled_function`.
pub fn for_tupled_function(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    paraml: &[Ident],
    pats_act_list: Vec<(Vec<Pattern>, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let pats_act_list: Vec<Clause> = pats_act_list
        .into_iter()
        .map(|(pats, act)| (pats, MatchAction::new(act)))
        .collect();
    let partial = check_partial_list(&pats_act_list, partial);
    let raise_num = bump_raise_count(next_raise_count, "matching::for_tupled_function");
    let omegas_row: Vec<Vec<Pattern>> = vec![paraml.iter().map(|_| omega()).collect()];
    let pm = PatternMatching {
        cases: pats_act_list,
        args: MatchArgs::new(
            paraml
                .iter()
                .map(|id| (RawLambda::Lvar(id.clone()), LetKind::Strict))
                .collect(),
        ),
        default: vec![(omegas_row, raise_num)],
    };
    match compile_match(
        ctx_ref,
        arena,
        None,
        &partial,
        &start_ctx(paraml.len()),
        &pm,
        next_raise_count,
    ) {
        Ok((lambda, total)) => {
            let loc_clone = loc.clone();
            check_total(&total, lambda.into_raw(), raise_num, || {
                partial_function(ctx_ref, loc_clone)
            })
        }
        Err(Unused) => partial_function(ctx_ref, loc),
    }
}

/// Cannot_flatten exception — used by flatten_pattern.
struct CannotFlattenExn;

/// Flatten a pattern into its tuple components.
/// Equivalent to OCaml's `flatten_pattern`.
fn flatten_pattern(size: usize, p: &Pattern) -> Result<Vec<Pattern>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_tuple(args) => Ok(args.clone()),
        PatternDesc::Tpat_any => Ok(omegas(size)),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten a pattern line (possibly through or-patterns and aliases).
/// Equivalent to OCaml's `flatten_pat_line`.
fn flatten_pat_line(
    size: usize,
    p: &Pattern,
    k: Vec<Vec<Pattern>>,
) -> Result<Vec<Vec<Pattern>>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = vec![omegas(size)];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) => {
            let mut result = vec![args.clone()];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            let k = flatten_pat_line(size, p2, k)?;
            flatten_pat_line(size, p1, k)
        }
        PatternDesc::Tpat_alias(p, _, _) => flatten_pat_line(size, p, k),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten all cases.
/// Equivalent to OCaml's `flatten_cases`.
fn flatten_cases(size: usize, cases: &[Clause]) -> Result<Vec<Clause>, CannotFlattenExn> {
    cases
        .iter()
        .map(|(ps, action)| match ps.as_slice() {
            [p] => Ok((flatten_pattern(size, p)?, action.clone())),
            _ => Err(CannotFlattenExn),
        })
        .collect()
}

/// Flatten a matrix.
/// Equivalent to OCaml's `flatten_matrix`.
fn flatten_matrix(size: usize, pss: &Matrix) -> Result<Matrix, CannotFlattenExn> {
    pss.iter()
        .rev()
        .try_fold(Vec::new(), |r, ps| match ps.as_slice() {
            [p] => flatten_pat_line(size, p, r),
            _ => Err(CannotFlattenExn),
        })
}

/// Flatten default environment.
/// Equivalent to OCaml's `flatten_def`.
fn flatten_def(size: usize, def: &DefaultEnv) -> Result<DefaultEnv, CannotFlattenExn> {
    def.iter()
        .map(|(pss, i)| Ok((flatten_matrix(size, pss)?, *i)))
        .collect()
}

/// Flatten a pattern matching.
/// Equivalent to OCaml's `flatten_pm`.
fn flatten_pm(
    size: usize,
    args: MatchArgs,
    pm: &PatternMatching,
) -> Result<PatternMatching, CannotFlattenExn> {
    Ok(PatternMatching {
        args,
        cases: flatten_cases(size, &pm.cases)?,
        default: flatten_def(size, &pm.default)?,
    })
}

/// Flatten a precompiled pattern matching.
/// Equivalent to OCaml's `flatten_precompiled`.
fn flatten_precompiled(
    size: usize,
    args: &MatchArgs,
    pmh: PmHalfCompiled,
) -> Result<PmHalfCompiled, CannotFlattenExn> {
    match pmh {
        PmHalfCompiled::Pm(pm) => Ok(PmHalfCompiled::Pm(flatten_pm(size, args.clone(), &pm)?)),
        PmHalfCompiled::PmOr(PmOrCompiled {
            body,
            handlers,
            or_matrix,
        }) => {
            let flat_body = flatten_pm(size, args.clone(), &body)?;
            let flat_handlers: Vec<_> = handlers
                .into_iter()
                .map(|(mat, i, vars, pm)| {
                    let flat_mat = flatten_matrix(size, &mat)?;
                    Ok((flat_mat, i, vars, pm))
                })
                .collect::<Result<_, CannotFlattenExn>>()?;
            let flat_or_matrix = flatten_matrix(size, &or_matrix)?;
            Ok(PmHalfCompiled::PmOr(PmOrCompiled {
                body: flat_body,
                handlers: flat_handlers,
                or_matrix: flat_or_matrix,
            }))
        }
        PmHalfCompiled::PmVar(_) => panic!("flatten_precompiled: PmVar"),
    }
}

/// Compiled_flattened: a comp_fun argument to comp_match_handlers.
/// Hence it needs a fourth argument (arg), which it ignores.
/// Equivalent to OCaml's `compile_flattened`.
fn compile_flattened(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    partial: &Partial,
    ctx: &[Ctx],
    _arg: &RawLambda,
    pmh: &PmHalfCompiled,
    next_raise_count: &mut i32,
) -> Result<(MatchCode, Jumps), Unused> {
    match pmh {
        PmHalfCompiled::Pm(pm) => {
            compile_match(ctx_ref, arena, None, partial, ctx, pm, next_raise_count)
        }
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) =
                compile_match(ctx_ref, arena, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn =
                |ctx: &[Ctx], pm: &PatternMatching| -> Result<(MatchCode, Jumps), Unused> {
                    compile_match(ctx_ref, arena, None, partial, ctx, pm, next_raise_count)
                };
            Ok(compile_orhandlers(
                &mut compile_fn,
                lam,
                total,
                ctx,
                handlers,
            ))
        }
        PmHalfCompiled::PmVar(_) => panic!("compile_flattened: PmVar"),
    }
}

/// Compile a multiple-match expression (tuple patterns on arguments).
/// Equivalent to OCaml's `do_for_multiple_match`.
pub fn do_for_multiple_match(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let partial = check_partial_single(&pat_act_list, partial);
    // OCaml `compiler/ml/matching.ml:3846-3852` builds the matrix from the
    // incoming action list directly. Rust owns `pat_act_list` here, so move
    // actions into the shared `MatchAction` wrapper instead of recursively
    // cloning each raw-lambda action before the matrix transformations.
    let cases: Vec<Clause> = pat_act_list
        .into_iter()
        .map(|(pat, act)| (vec![pat], MatchAction::new(act)))
        .collect();
    let tuple_arg = RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
        args: paraml.clone(),
        loc: loc.clone(),
    });
    let (raise_num, pm1) = match &partial {
        Partial::Partial => {
            let raise_num = bump_raise_count(next_raise_count, "matching::do_for_multiple_match");
            (
                raise_num,
                PatternMatching {
                    cases,
                    args: MatchArgs::new(vec![(tuple_arg, LetKind::Strict)]),
                    default: vec![(vec![vec![omega()]], raise_num)],
                },
            )
        }
        Partial::Total => (
            -1,
            PatternMatching {
                cases,
                args: MatchArgs::new(vec![(tuple_arg, LetKind::Strict)]),
                default: Vec::new(),
            },
        ),
    };

    // Try flatten optimization first
    let result = (|| -> Result<RawLambda, CannotFlattenExn> {
        let (next, nexts) = split_precompile(Some(ctx_ref), &None, &pm1, next_raise_count);

        let size = paraml.len();

        // Debug: print what split_precompile produced
        let idl: Vec<Ident> = paraml
            .iter()
            .map(|_| ctx_ref.create_ident("match"))
            .collect();
        let args = MatchArgs::new(
            idl.iter()
                .map(|id| (RawLambda::Lvar(id.clone()), LetKind::Alias))
                .collect(),
        );

        let flat_next = flatten_precompiled(size, &args, next)?;
        let flat_nexts: Vec<(i32, PmHalfCompiled)> = nexts
            .into_iter()
            .map(|(e, pm)| {
                let flat = flatten_precompiled(size, &args, pm)?;
                Ok((e, flat))
            })
            .collect::<Result<_, CannotFlattenExn>>()?;

        let mut compile_fn = |partial: &Partial,
                              ctx: &[Ctx],
                              arg: &RawLambda,
                              pmh: &PmHalfCompiled|
         -> Result<(MatchCode, Jumps), Unused> {
            compile_flattened(ctx_ref, arena, partial, ctx, arg, pmh, next_raise_count)
        };

        let dummy_arg = RawLambda::Lconst(crate::lambda::Constant::int(0));
        let (lam, total) = comp_match_handlers(
            &mut compile_fn,
            &partial,
            &start_ctx(size),
            &dummy_arg,
            &flat_next,
            &flat_nexts,
        )
        .map_err(|_| CannotFlattenExn)?;

        let result = idl.iter().zip(paraml.iter()).rev().fold(
            match &partial {
                Partial::Partial => {
                    let loc_clone = loc.clone();
                    check_total(&total, lam.into_raw(), raise_num, || {
                        partial_function(ctx_ref, loc_clone)
                    })
                }
                Partial::Total => {
                    assert!(jumps_is_empty(&total));
                    lam.into_raw()
                }
            },
            |body, (id, param)| bind(LetKind::Strict, id, param, body),
        );
        Ok(result)
    })();

    match result {
        Ok(lam) => lam,
        Err(CannotFlattenExn) => {
            // Fallback: compile without flattening
            match compile_match(
                ctx_ref,
                arena,
                None,
                &partial,
                &start_ctx(1),
                &pm1,
                next_raise_count,
            ) {
                Ok((lambda, total)) => match &partial {
                    Partial::Partial => {
                        let loc_clone = loc.clone();
                        check_total(&total, lambda.into_raw(), raise_num, || {
                            partial_function(ctx_ref, loc_clone)
                        })
                    }
                    Partial::Total => {
                        assert!(jumps_is_empty(&total));
                        lambda.into_raw()
                    }
                },
                Err(Unused) => panic!("do_for_multiple_match: Unused"),
            }
        }
    }
}

/// Extract a variable from a param, binding if needed.
/// Equivalent to OCaml's `param_to_var`.
fn param_to_var(ctx_ref: &TypeContext, param: &RawLambda) -> (Ident, Option<RawLambda>) {
    match param {
        RawLambda::Lvar(v) => (v.clone(), None),
        _ => (ctx_ref.create_ident("match"), Some(param.clone())),
    }
}

/// Optionally bind a variable.
/// Equivalent to OCaml's `bind_opt`.
fn bind_opt(v_eo: (Ident, Option<RawLambda>), k: RawLambda) -> RawLambda {
    match v_eo {
        (_, None) => k,
        (v, Some(e)) => bind(LetKind::Strict, &v, &e, k),
    }
}

/// Compile a multiple match expression.
/// Equivalent to OCaml's `for_multiple_match`.
pub fn for_multiple_match(
    ctx_ref: &TypeContext,
    arena: &ParseArena,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let v_paraml: Vec<(Ident, Option<RawLambda>)> = paraml
        .iter()
        .map(|param| param_to_var(ctx_ref, param))
        .collect();
    let new_paraml: Vec<RawLambda> = v_paraml
        .iter()
        .map(|(v, _)| RawLambda::Lvar(v.clone()))
        .collect();
    let inner = do_for_multiple_match(
        ctx_ref,
        arena,
        loc,
        new_paraml,
        pat_act_list,
        partial,
        next_raise_count,
    );
    v_paraml
        .into_iter()
        .rev()
        .fold(inner, |body, v_eo| bind_opt(v_eo, body))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::types::env::initial_env;
    use crate::types::predef;

    #[test]
    fn constructor_cases_use_pattern_env_layout() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let env_ref = ctx.store_typed_env(&env);
        let pat_type = ctx.new_generic_constr(
            predef::path_result(),
            vec![ctx.new_var(None), ctx.new_var(None)],
        );
        let pat = make_pat(PatternDesc::Tpat_any, pat_type, env_ref);

        let pat_env = ctx.get_typed_env(pat.pat_env).expect("pattern environment");
        let TypeDesc::Tconstr { path, .. } = &*ctx.get_desc(ctx.repr(pat.pat_type)) else {
            panic!("expected result constructor");
        };
        let decl = find_type_decl_pub(&ctx, pat_env.as_ref(), path).expect("result declaration");
        let TypeKind::TypeVariant(_, layout_ref) = decl.type_kind else {
            panic!("expected result variant layout");
        };
        let layout = ctx.variant_layout(layout_ref);
        let names: Vec<_> = layout
            .constructors
            .iter()
            .map(|case| match case {
                crate::types::VariantConstructorCase::Block(block) => {
                    block.runtime.tag.name.as_str()
                }
                crate::types::VariantConstructorCase::Constant(tag) => tag.name.as_str(),
            })
            .collect();

        assert_eq!(names, vec!["Ok", "Error"]);
        assert!(
            layout
                .constructors
                .iter()
                .all(|case| matches!(case, crate::types::VariantConstructorCase::Block(_)))
        );
    }

    #[test]
    fn or_list_polyvar_keeps_named_hash_metadata() {
        let arg = RawLambda::var(Ident::create_local("match"));
        let raw = or_list_polyvar(
            &arg,
            &[
                (btype::hash_variant("A"), "A".to_string()),
                (btype::hash_variant("B"), "B".to_string()),
            ],
        );

        let RawLambda::Lprim(first_or) = raw else {
            panic!("expected sequor chain");
        };
        let [RawLambda::Lprim(first_eq), RawLambda::Lprim(second_eq)] = first_or.args.as_slice()
        else {
            panic!("expected two equality tests");
        };

        assert!(
            matches!(first_eq.args.as_slice(), [RawLambda::Lvar(_), RawLambda::Lconst(crate::lambda::lam_constant::Constant::Int { i, comment: Some(PointerInfo::PolyVariant(name)) })]
            if *i == btype::hash_variant("A") && name == "A")
        );
        assert!(
            matches!(second_eq.args.as_slice(), [RawLambda::Lvar(_), RawLambda::Lconst(crate::lambda::lam_constant::Constant::Int { i, comment: Some(PointerInfo::PolyVariant(name)) })]
            if *i == btype::hash_variant("B") && name == "B")
        );
    }

    fn direct_switch(
        actions: Vec<MatchCode>,
        next_raise_count: &mut i32,
    ) -> (Vec<(i32, RawLambda)>, RawLambdaSwitch) {
        share_match_switch(
            actions.len(),
            true,
            actions
                .into_iter()
                .enumerate()
                .map(|(index, action)| (crate::lambda::SwitchKey::Int(index as i32), action))
                .collect(),
            0,
            true,
            Vec::new(),
            None,
            crate::lambda::SwitchDispatch::Direct,
            next_raise_count,
        )
    }

    #[test]
    fn match_switch_moves_a_unique_action_without_a_catch() {
        let action = RawLambda::Lsequence(
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(1))),
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(2))),
        );
        let mut next_raise_count = 40;
        let (handlers, switch) = direct_switch(vec![MatchCode::raw(action)], &mut next_raise_count);

        assert!(handlers.is_empty());
        assert_eq!(next_raise_count, 40);
        assert!(matches!(
            switch.sw_consts.as_slice(),
            [(_, RawLambda::Lsequence(first, second))]
                if matches!(first.as_ref(), RawLambda::Lconst(_))
                    && matches!(second.as_ref(), RawLambda::Lconst(_))
        ));
    }

    #[test]
    fn repeated_match_action_gets_one_handler_and_tiny_exits() {
        let leaf = MatchAction::new(RawLambda::Lsequence(
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(1))),
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(2))),
        ));
        let mut next_raise_count = 70;
        let (handlers, switch) = direct_switch(
            vec![MatchCode::Action(leaf.clone()), MatchCode::Action(leaf)],
            &mut next_raise_count,
        );

        assert_eq!(next_raise_count, 71);
        assert!(matches!(
            handlers.as_slice(),
            [(71, RawLambda::Lsequence(_, _))]
        ));
        assert!(switch.sw_consts.iter().all(|(_, action)| {
            matches!(action, RawLambda::LstaticRaise(71, args) if args.is_empty())
        }));
    }

    #[test]
    fn shared_handlers_keep_store_and_catch_number_order() {
        fn action(first: i32, second: i32) -> MatchCode {
            MatchCode::raw(RawLambda::Lsequence(
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(first))),
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(second))),
            ))
        }

        let mut next_raise_count = 8;
        let (handlers, switch) = share_match_switch(
            2,
            true,
            vec![
                (crate::lambda::SwitchKey::Int(0), action(3, 4)),
                (crate::lambda::SwitchKey::Int(1), action(3, 4)),
            ],
            0,
            true,
            Vec::new(),
            Some(action(1, 2)),
            crate::lambda::SwitchDispatch::Direct,
            &mut next_raise_count,
        );

        assert_eq!(
            handlers.iter().map(|(exit, _)| *exit).collect::<Vec<_>>(),
            vec![9, 10]
        );
        assert!(
            matches!(switch.sw_failaction.as_deref(), Some(RawLambda::LstaticRaise(9, args)) if args.is_empty())
        );
        assert!(switch.sw_consts.iter().all(|(_, action)| {
            matches!(action, RawLambda::LstaticRaise(10, args) if args.is_empty())
        }));
    }

    #[test]
    fn nested_generated_match_code_is_shared_at_the_switch_boundary() {
        fn nested() -> MatchCode {
            MatchCode::static_catch(
                MatchCode::if_then_else(
                    RawLambda::Lconst(crate::lambda::Constant::int(1)),
                    MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(2))),
                    MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(3))),
                ),
                (44, Vec::new()),
                MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(4))),
            )
        }

        let mut next_raise_count = 100;
        let (handlers, switch) = direct_switch(vec![nested(), nested()], &mut next_raise_count);
        assert_eq!(handlers.len(), 1);
        assert_eq!(next_raise_count, 101);
        assert!(switch.sw_consts.iter().all(|(_, action)| {
            matches!(action, RawLambda::LstaticRaise(101, args) if args.is_empty())
        }));
    }

    #[test]
    fn bind_check_keeps_existing_alias_before_lowered_alias() {
        let first = Ident::create_local("first");
        let selected = Ident::create_local("selected");
        let source = RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pnot,
            args: vec![RawLambda::Lconst(crate::lambda::Constant::int(0))],
            loc: Location::none(),
        });
        let code = MatchCode::Action(MatchAction::new(RawLambda::Lvar(selected.clone()))).bind(
            LetKind::Alias,
            first.clone(),
            RawLambda::Lconst(crate::lambda::Constant::int(1)),
        );
        let raw = bind_check_code(LetKind::Alias, &selected, &source, code).into_raw();

        assert!(matches!(
            raw,
            RawLambda::Llet(LetKind::Alias, outer, _, body)
                if outer.same(&first)
                    && matches!(body.as_ref(), RawLambda::Llet(LetKind::Alias, inner, _, _) if inner.same(&selected))
        ));
    }

    #[test]
    fn match_code_make_key_matches_materialized_alias_code() {
        let alias = Ident::create_local("alias");
        let code = MatchCode::Action(MatchAction::new(RawLambda::Lvar(alias.clone()))).bind(
            LetKind::Alias,
            alias,
            RawLambda::Lconst(crate::lambda::Constant::int(7)),
        );
        let raw = RawLambda::Lconst(crate::lambda::Constant::int(7));

        assert_eq!(code.normalized_key(), make_key_string(&raw));
    }

    fn assert_match_code_key_matches_raw(code: &MatchCode) {
        assert_eq!(
            make_key_string_code(code),
            make_key_string(&code.clone_to_raw_for_test())
        );
    }

    #[test]
    fn match_code_keys_match_raw_make_key_boundaries_and_wrappers() {
        for depth in [15, 16] {
            let mut code = MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(0)));
            for index in 0..depth {
                code = code.bind(
                    LetKind::Alias,
                    Ident::create_local(&format!("alias{index}")),
                    RawLambda::Lconst(crate::lambda::Constant::int(index)),
                );
            }
            let code_key = make_key_string_code(&code);
            let raw_key = make_key_string(&code.clone_to_raw_for_test());
            assert_eq!(code_key, raw_key);
            if depth == 15 {
                assert!(
                    code_key.is_some(),
                    "31 charged nodes must remain within MAX_RAW"
                );
            } else {
                assert!(code_key.is_none(), "33 charged nodes must exceed MAX_RAW");
            }
        }

        let alias = Ident::create_local("alias");
        let nested_alias = MatchCode::Action(MatchAction::new(RawLambda::Lvar(alias.clone())))
            .bind(
                LetKind::Alias,
                alias,
                RawLambda::Lconst(crate::lambda::Constant::int(1)),
            );
        assert_match_code_key_matches_raw(&nested_alias);

        for kind in [LetKind::Strict, LetKind::StrictOpt] {
            let id = Ident::create_local("identity");
            let identity = MatchCode::Bind {
                kind,
                id: id.clone(),
                arg: RawLambda::LstaticRaise(14, Vec::new()),
                body: Box::new(MatchCode::Action(MatchAction::new(RawLambda::Lvar(id)))),
            };
            assert_match_code_key_matches_raw(&identity);
        }

        let caught = Ident::create_local("caught");
        let catch = MatchCode::static_catch(
            MatchCode::raw(RawLambda::LstaticRaise(
                20,
                vec![RawLambda::Lvar(caught.clone())],
            )),
            (20, vec![caught.clone()]),
            MatchCode::raw(RawLambda::Lvar(caught)),
        );
        assert_match_code_key_matches_raw(&catch);

        let conditional = MatchCode::if_then_else(
            RawLambda::Lconst(crate::lambda::Constant::int(1)),
            MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(2))),
            MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::int(3))),
        );
        assert_match_code_key_matches_raw(&conditional);

        let record = MatchCode::raw(RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pmakeblock(
                TagInfo::Record {
                    fields: vec![("field".to_string(), false)],
                    logical_field_count: Some(33),
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                },
                Mutable::Immutable,
            ),
            args: vec![RawLambda::Lconst(crate::lambda::Constant::int(1))],
            loc: Location::none(),
        }));
        assert_match_code_key_matches_raw(&record);

        let key_none = MatchCode::raw(RawLambda::Lconst(crate::lambda::Constant::String {
            s: "mutable".to_string(),
            delim: None,
        }));
        assert_match_code_key_matches_raw(&key_none);
        assert!(make_key_string_code(&key_none).is_none());
    }

    #[test]
    fn simple_exit_sharing_reuses_existing_exit_without_handler() {
        let mut next_raise_count = 50;
        let (handlers, switch) = direct_switch(
            vec![
                MatchCode::raw(RawLambda::LstaticRaise(7, Vec::new())),
                MatchCode::raw(RawLambda::LstaticRaise(7, Vec::new())),
            ],
            &mut next_raise_count,
        );
        assert!(handlers.is_empty());
        assert_eq!(next_raise_count, 50);
        assert!(switch.sw_consts.iter().all(|(_, action)| {
            matches!(action, RawLambda::LstaticRaise(7, args) if args.is_empty())
        }));
    }

    #[test]
    fn guarded_patch_and_free_variables_preserve_nested_bind_shape() {
        let bound = Ident::create_local("bound");
        let condition = Ident::create_local("condition");
        let body_var = Ident::create_local("body");
        let action = MatchAction::new(RawLambda::Llet(
            LetKind::Alias,
            bound.clone(),
            Box::new(RawLambda::Lvar(body_var.clone())),
            Box::new(RawLambda::LifThenElse(
                Box::new(RawLambda::Lvar(condition.clone())),
                Box::new(RawLambda::Lvar(bound)),
                Box::new(RawLambda::LstaticRaise(0, Vec::new())),
            )),
        ));
        let patch = RawLambda::Lconst(crate::lambda::Constant::int(9));
        let patched = action.patch_guarded(patch);
        let free = action.free_variables();

        assert!(free.contains(&condition));
        assert!(free.contains(&body_var));
        assert!(matches!(
            patched,
            RawLambda::Llet(LetKind::Alias, _, _, body)
                if matches!(body.as_ref(), RawLambda::LifThenElse(_, _, replacement)
                    if matches!(replacement.as_ref(), RawLambda::Lconst(_)))
        ));
    }

    #[test]
    fn nested_shared_handlers_materialize_the_full_catch_shape() {
        fn action(first: i32, second: i32) -> MatchCode {
            MatchCode::raw(RawLambda::Lsequence(
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(first))),
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(second))),
            ))
        }
        let mut next_raise_count = 30;
        let (handlers, switch) = share_match_switch(
            2,
            true,
            vec![
                (crate::lambda::SwitchKey::Int(0), action(3, 4)),
                (crate::lambda::SwitchKey::Int(1), action(3, 4)),
            ],
            0,
            true,
            Vec::new(),
            Some(action(1, 2)),
            crate::lambda::SwitchDispatch::Direct,
            &mut next_raise_count,
        );
        let nested = apply_handlers(
            RawLambda::Lswitch(
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(0))),
                switch,
                Location::none(),
            ),
            handlers,
        );
        assert!(matches!(
            nested,
            RawLambda::LstaticCatch(outer_body, (32, _), outer_handler)
                if matches!(outer_body.as_ref(), RawLambda::LstaticCatch(_, (31, _), _))
                    && matches!(outer_handler.as_ref(), RawLambda::Lsequence(_, _))
        ));
    }

    #[test]
    fn match_switch_preserves_fail_const_block_mapping_and_distinct_keys() {
        fn action(first: i32, second: i32) -> MatchCode {
            MatchCode::raw(RawLambda::Lsequence(
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(first))),
                Box::new(RawLambda::Lconst(crate::lambda::Constant::int(second))),
            ))
        }
        let left = MatchCode::if_then_else(
            RawLambda::Lconst(crate::lambda::Constant::int(0)),
            action(1, 2),
            action(3, 4),
        );
        let right = MatchCode::if_then_else(
            RawLambda::Lconst(crate::lambda::Constant::int(1)),
            action(1, 2),
            action(3, 4),
        );
        assert_ne!(left.normalized_key(), right.normalized_key());
        assert_match_code_key_matches_raw(&left);
        assert_match_code_key_matches_raw(&right);

        let mut next_raise_count = 60;
        let (handlers, switch) = share_match_switch(
            1,
            true,
            vec![(crate::lambda::SwitchKey::Int(0), action(1, 2))],
            1,
            true,
            vec![(crate::lambda::SwitchKey::Int(0), action(3, 4))],
            Some(action(1, 2)),
            crate::lambda::SwitchDispatch::Direct,
            &mut next_raise_count,
        );
        assert_eq!(
            handlers.iter().map(|(exit, _)| *exit).collect::<Vec<_>>(),
            vec![61]
        );
        assert!(
            matches!(switch.sw_failaction.as_deref(), Some(RawLambda::LstaticRaise(61, args)) if args.is_empty())
        );
        assert!(
            matches!(switch.sw_consts.as_slice(), [(_, RawLambda::LstaticRaise(61, args))] if args.is_empty())
        );
        assert!(matches!(
            switch.sw_blocks.as_slice(),
            [(_, RawLambda::Lsequence(_, _))]
        ));
    }

    #[test]
    fn terminal_bind_keeps_shared_action_lazy_and_preserves_order() {
        let terminal = MatchAction::new(RawLambda::Lsequence(
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(1))),
            Box::new(RawLambda::Lconst(crate::lambda::Constant::int(2))),
        ));
        let shared_terminal = terminal.clone();
        let first = Ident::create_local("first");
        let second = Ident::create_local("second");
        let bound = terminal
            .bind(
                LetKind::Alias,
                first.clone(),
                RawLambda::Lconst(crate::lambda::Constant::int(3)),
            )
            .bind(
                LetKind::Alias,
                second.clone(),
                RawLambda::Lconst(crate::lambda::Constant::int(4)),
            );

        let MatchActionKind::Bind {
            action: first_bind, ..
        } = &bound.0.kind
        else {
            panic!("expected outer delayed bind");
        };
        let MatchActionKind::Bind { action: leaf, .. } = &first_bind.0.kind else {
            panic!("expected inner delayed bind");
        };
        assert!(Arc::ptr_eq(&leaf.0, &shared_terminal.0));
        assert!(matches!(
            bound.into_raw(),
            RawLambda::Llet(LetKind::Alias, outer, _, body)
                if outer.same(&second)
                    && matches!(body.as_ref(), RawLambda::Llet(LetKind::Alias, inner, _, _) if inner.same(&first))
        ));
    }
}
