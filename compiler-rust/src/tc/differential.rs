//! Differential harness of the new graph against the old checker (R3).
//!
//! One case is a generated program (type declarations and values) and a
//! sequence of [`Op`]s. The program is compiled by the old checker; its
//! publication is converted with `bridge::from_old`. The operations then run
//! on both sides: on the old checker's graph of the internalized unit, and on
//! the new graph of the converted segment. The two sides must agree on which
//! operation failed and on the *form* of every operand: one text for all
//! operands of a case, in which every node is numbered at its first visit
//! (`&n`) and named by that number at every later one (`@n`), with its level
//! relative to the level the case started at, its variable name and the last
//! component of its constructor path. A node two operands share therefore
//! prints as a back reference on both sides or on neither.
//!
//! This is the numbering rule of the canonical signature (CHECKER_REDESIGN
//! I.3.5) applied to a graph in the middle of a check: the canonical
//! signature itself prints a published unit, without levels and with links
//! followed, and cannot print an operand that is not generic.
//!
//! Variable names are part of the form in every tier: the old checker's
//! `instance` drops a variable's name (`copy_type_desc`,
//! compiler/ml/btype.ml:510), and so do `Graph::instance` and `Graph::copy`
//! since slice R3b (`r3_tests::instance_drops_variable_names` is the test
//! that compares them).
//!
//! A failed operation ends the case: what a failed unification leaves in
//! the graph is not observable (CHECKER_REWRITE "R3 as designed", decision
//! 5), so nothing after it is compared except the index of the failure.
//!
//! A [`Plan`] adds to a tier, one bit each (section 8.6, second skeleton):
//! - [`EXPLAIN`]: both sides run in the explaining mode, where a failure is
//!   observable. A failed operation does not end the case: its trace (the
//!   pairs in order, numbered with the operands) is compared, and the graph
//!   it leaves when that does not print as the graph before it; the case
//!   goes on and the final form is compared.
//! - [`SCOPED`]: the program declares three late types `s0`, `s1`, `s2<'a>`
//!   whose scopes are one, two and three levels above the level the case
//!   starts at, as a type declared after the item being checked is
//!   (`get_level`, compiler/ml/ctype.ml:562-569). Lowering can then clash.
//! - [`BUILD`]: operations that make a variable, a tuple of two operands and
//!   an operand's child, so that a type can hold a node above its own level
//!   and a unification can meet a type inside itself.
//! - [`OBJECTS`], [`VARIANTS`], [`UNIVARS`], [`PACKAGES`], [`PATTERN`],
//!   [`RELATIONS`], [`SUBTYPE`]: the types and operations of slices R3e to
//!   R3j; [`Plan::slices`] names the slices each reaches.
//!
//! Nothing here is on a compile path; the harness allocates freely.

use std::fmt::Write as _;
use std::sync::Arc;

use super::bridge::from_old::{Input, from_old};
use super::expand::{ExpandMode, TypeTable};
use super::graph::{ARROW, CONSTR, GENERIC, Mode, NONE, Node, TUPLE, Ty, VAR};
use super::unify::Checker;
use super::segment::{PathRow, SchemeRoot, Segment, SignatureKind};
use crate::cmi::persistent_env::{InMemoryModuleInfo, ModuleRegistry, PersistentEnv};
use crate::cmi::portable_types::{PortablePersStruct, internalize_pers_struct};
use crate::context::IdGenerator;
use crate::driver::{CompilerOptions, compile_source_in_process};
use crate::types::context::TypeContext;
use crate::types::ctype;
use crate::types::decl::SignatureItem;
use crate::types::env::{Env, initial_env};
use crate::types::type_expr::{GENERIC_LEVEL, TypeDesc, TypeExprRef};

/// Template reference flag of a node relative to an instance's first node
/// (tc/template.rs, `Template`).
const RELATIVE: u32 = 1 << 30;

/// SplitMix64: the whole case is a function of one seed.
pub(crate) struct Rng(pub u64);

impl Rng {
    /// O(1).
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// O(1): a number below `n` (`n` > 0).
    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Which operations a case may use; each tier needs more of R3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Tier {
    /// Instance, copy, generalize, lower: R1 and R2 only. Runs today.
    Kernel,
    /// Kernel and unification on programs without abbreviations (R3a).
    Structural,
    /// Kernel, expansion and memo cleanup on programs with abbreviations (R3b).
    Expand,
    /// Everything, on programs with abbreviations (R3c).
    Full,
}

impl Tier {
    /// O(1): whether generated programs declare abbreviations.
    fn abbreviations(self) -> bool {
        self != Tier::Structural
    }

    /// O(1): whether the form prints variable names: in every tier, since
    /// R1's instance and copy drop names as the old checker's do.
    fn names(self) -> bool {
        true
    }

    /// O(1): whether the new side takes instances and copies through the
    /// memo-aware `Checker::instance` and `Checker::copy` (R3b) and reads the
    /// declaration table. Below `Expand` a program has no abbreviation, so
    /// R1's `Graph::instance` and `Graph::copy` are the same operations and
    /// the structural tier needs nothing of R3b.
    fn memo_aware(self) -> bool {
        self >= Tier::Expand
    }

    /// O(1): whether `Op::Lower` runs the scoped `Checker::lower` (R3d). Only
    /// the full tier does: R3c depends on R3d. Generated programs have no
    /// scoped type, so in the lower tiers R1's `Graph::lower` is the same walk.
    fn scoped_lower(self) -> bool {
        self == Tier::Full
    }
}

/// [`Plan::with`]: both sides explain; see the module text.
pub(crate) const EXPLAIN: u16 = 1 << 0;
/// [`Plan::with`]: three late types with scopes; see the module text.
pub(crate) const SCOPED: u16 = 1 << 1;
/// [`Plan::with`]: `Op::Var`, `Op::Tuple` and `Op::Child`.
pub(crate) const BUILD: u16 = 1 << 2;

/// [`Plan::with`]: object types, closed and open, and a recursive
/// abbreviation through an object, nullary (`ro`) and with a parameter
/// (`po<'a>`). Unifying two of them is slice R3e's.
pub(crate) const OBJECTS: u16 = 1 << 4;
/// [`Plan::with`]: polymorphic variant types, closed, open and bounded, and
/// a recursive abbreviation through a variant (`rv`, `pv<'a>`). Unifying
/// two of them is slice R3f's.
pub(crate) const VARIANTS: u16 = 1 << 5;

/// A tier and what a case adds to it. 4 bytes, passed by value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Plan {
    pub tier: Tier,
    pub with: u16,
}

impl From<Tier> for Plan {
    /// O(1): the tier alone, as slices R3a to R3d run it.
    fn from(tier: Tier) -> Plan {
        Plan { tier, with: 0 }
    }
}

impl Plan {
    /// O(1): the tier with these additions.
    pub(crate) fn new(tier: Tier, with: u16) -> Plan {
        Plan { tier, with }
    }

    /// O(1): whether the plan has every bit of `bits`.
    pub(crate) fn has(self, bits: u16) -> bool {
        self.with & bits == bits
    }
}

/// One step of a case. Operands are numbered in creation order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    /// A new operand: an instance of the value's scheme.
    Instance(u16),
    /// A new operand: `instance` of an operand (a copy of its generic part).
    Copy(u16),
    BeginDef,
    EndDef,
    Generalize(u16),
    /// Lower an operand to the starting level plus this many definitions.
    Lower(u16, u8),
    /// Unify two operands; the only operation that can fail.
    Unify(u16, u16),
    /// A new operand: the expanded head of an operand.
    Expand(u16),
    /// Forget every memorized expansion (`Btype.cleanup_abbrev`).
    Cleanup,
    /// A new operand: a variable at the current level (`newvar`). [`BUILD`].
    Var,
    /// A new operand: a tuple of two operands at the current level
    /// (`newty (Ttuple [a; b])`). After an `EndDef` it is below the nodes
    /// it holds. [`BUILD`].
    Tuple(u16, u16),
    /// A new operand: child `n mod arity` of an operand's representative in
    /// `iter_type_expr`'s order (compiler/ml/btype.ml:250-257), or the
    /// operand itself when it has no child. [`BUILD`].
    Child(u16, u8),
}

/// A deliberately wrong new side, for the tests that prove the harness sees
/// a difference. `None` is the real thing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    None,
    /// `Generalize` does nothing.
    SkipGeneralize,
    /// A second `Instance` of a value returns the first one's node.
    ReuseInstance,
    /// `Lower` stops at the root instead of walking its children.
    ShallowLower,
    /// The trace of a failed unification loses its last pair. [`EXPLAIN`].
    ShortTrace,
    /// Every pair of a trace is reversed. [`EXPLAIN`].
    ReversedTrace,
    /// A failed unification leaves the levels the binding walk of
    /// `Mode::Success` writes: the new side runs in `Mode::Success`
    /// (decision 6 of 8.6). [`EXPLAIN`].
    SuccessLevels,
    /// The late types have no scope on the new side. [`SCOPED`].
    NoScopes,
    /// `Tuple` is made at the level of its first operand's representative
    /// instead of the current level. [`BUILD`].
    TupleAtChildLevel,
    /// A unification that binds a variable operand lowers every node of the
    /// other operand that is above the variable's level, also below a node
    /// that is not: what the binding walk did before decision 8 of 8.6
    /// (`update_level` stops there, compiler/ml/ctype.ml:586). [`BUILD`].
    UnprunedBinding,
}

/// What one side reports for one case.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Outcome {
    /// Index of the first operation that failed, when one did.
    pub failed: Option<usize>,
    /// The form of every operand; empty after a failure. Under [`EXPLAIN`]:
    /// one section per failed operation (its trace, and the graph it left
    /// when that differs from the graph before it), then the form.
    pub form: String,
    /// Failed operations after which the graph printed as before them, and
    /// those after which it did not. [`EXPLAIN`].
    pub unchanged: u32,
    pub changed: u32,
}

impl Outcome {
    /// O(1): the outcome of a case that ended at a failed operation.
    fn ended(index: usize) -> Outcome {
        Outcome {
            failed: Some(index),
            form: String::new(),
            unchanged: 0,
            changed: 0,
        }
    }
}

/// A generated program, compiled once by the old checker.
pub(crate) struct Program {
    pub source: String,
    pub unit: Arc<PortablePersStruct>,
    /// Exported value names, in declaration order.
    pub values: Vec<String>,
}

/// O(depth): one type expression in ReScript syntax. `nullary` and `unary`
/// name the abbreviations and abstract types in scope.
fn type_text(
    rng: &mut Rng,
    depth: u32,
    vars: &[&str],
    nullary: &[String],
    unary: &[String],
    out: &mut String,
) {
    type_text_with(rng, 0, depth, vars, nullary, unary, out)
}

/// [`type_text`] with the object and variant types of `with`
/// ([`OBJECTS`], [`VARIANTS`]): one position in four that is not a leaf.
/// Field names are drawn from `x`, `y`, `z` and tags from `A`, `B`, `C`,
/// each at most once and in that order.
fn type_text_with(
    rng: &mut Rng,
    with: u16,
    depth: u32,
    vars: &[&str],
    nullary: &[String],
    unary: &[String],
    out: &mut String,
) {
    let rows = with & (OBJECTS | VARIANTS);
    if rows != 0 && depth != 0 && rng.below(4) == 0 {
        let object = rows == OBJECTS || (rows != VARIANTS && rng.below(2) == 0);
        let members: Vec<usize> = (0..3).filter(|_| rng.below(2) == 0).collect();
        let members = if members.is_empty() { vec![0] } else { members };
        if object {
            out.push('{');
            if rng.below(3) == 0 {
                out.push_str("..");
            }
            for (index, member) in members.into_iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                let _ = write!(out, "\"{}\": ", ["x", "y", "z"][member]);
                type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
            }
            out.push('}');
        } else {
            out.push_str(["[", "[> ", "[< "][rng.below(3)]);
            for (index, member) in members.into_iter().enumerate() {
                if index != 0 {
                    out.push_str(" | ");
                }
                let _ = write!(out, "#{}", ["A", "B", "C"][member]);
                if rng.below(2) == 0 {
                    out.push('(');
                    type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
                    out.push(')');
                }
            }
            out.push(']');
        }
        return;
    }
    let leaf = depth == 0 || rng.below(3) == 0;
    if leaf {
        let choices = 2 + vars.len() + nullary.len();
        let pick = rng.below(choices);
        if pick == 0 {
            out.push_str("int");
        } else if pick == 1 {
            out.push_str("string");
        } else if pick < 2 + vars.len() {
            out.push_str(vars[pick - 2]);
        } else {
            out.push_str(&nullary[pick - 2 - vars.len()]);
        }
        return;
    }
    match rng.below(3) {
        0 if !unary.is_empty() => {
            out.push_str(&unary[rng.below(unary.len())]);
            out.push('<');
            type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
            out.push('>');
        }
        1 => {
            out.push('(');
            for i in 0..2 + rng.below(2) {
                if i != 0 {
                    out.push_str(", ");
                }
                type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
            }
            out.push(')');
        }
        _ => {
            // Parenthesised, so that an arrow can stand in any position.
            out.push_str("((");
            let labelled = rng.below(4) == 0;
            for i in 0..1 + rng.below(2) {
                if i != 0 {
                    out.push_str(", ");
                }
                if labelled && i == 0 {
                    out.push_str("~x: ");
                }
                type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
            }
            out.push_str(") => ");
            type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
            out.push(')');
        }
    }
}

/// O(program size): the source of one program. Declarations: two abstract
/// types, then (when the tier has them) up to five abbreviations, each
/// nullary or unary over the earlier ones, a unary one sometimes phantom.
/// Values: externals with random types over two type variables, and two
/// inferred values whose types share nodes.
///
/// With [`SCOPED`], after the abbreviations: `type s0` (abstract), `type s1
/// = body`, `type s2<'a> = body`, the bodies over the earlier types only.
pub(crate) fn program_source(rng: &mut Rng, plan: impl Into<Plan>) -> String {
    let plan = plan.into();
    let tier = plan.tier;
    let mut source = String::from("type t0\ntype t1<'a>\n");
    let mut nullary = vec!["t0".to_string()];
    let mut unary = vec!["t1".to_string()];
    if tier.abbreviations() {
        for index in 0..2 + rng.below(4) {
            let name = format!("a{index}");
            let mut body = String::new();
            if rng.below(2) == 0 {
                type_text(rng, 2, &[], &nullary, &unary, &mut body);
                let _ = writeln!(source, "type {name} = {body}");
                nullary.push(name);
            } else {
                // Without `'a` in the body the parameter is phantom (O9).
                let vars: &[&str] = if rng.below(4) == 0 { &[] } else { &["'a"] };
                type_text(rng, 2, vars, &nullary, &unary, &mut body);
                let _ = writeln!(source, "type {name}<'a> = {body}");
                unary.push(name);
            }
        }
    }
    if plan.has(SCOPED) {
        let mut body = String::new();
        type_text(rng, 2, &[], &nullary, &unary, &mut body);
        let _ = writeln!(source, "type s0\ntype s1 = {body}");
        let mut body = String::new();
        let vars: &[&str] = if rng.below(3) == 0 { &[] } else { &["'a"] };
        type_text(rng, 2, vars, &nullary, &unary, &mut body);
        let _ = writeln!(source, "type s2<'a> = {body}");
        nullary.push("s0".to_string());
        nullary.push("s1".to_string());
        unary.push("s2".to_string());
    }
    // Recursive abbreviations: decision 3 of 8.6 (inherited memo entries,
    // compiler/ml/ctype.ml:788-797).
    if plan.has(OBJECTS) {
        source.push_str("type rec ro = {\"hd\": int, \"tl\": ro}\n");
        source.push_str("type rec po<'a> = {\"hd\": 'a, \"tl\": po<'a>}\n");
        nullary.push("ro".to_string());
        unary.push("po".to_string());
    }
    if plan.has(VARIANTS) {
        source.push_str("type rec rv = [#Nil | #Cons(int, rv)]\n");
        source.push_str("type rec pv<'a> = [#Nil | #Cons('a, pv<'a>)]\n");
        nullary.push("rv".to_string());
        unary.push("pv".to_string());
    }
    for index in 0..3 + rng.below(4) {
        let mut body = String::new();
        type_text_with(rng, plan.with, 3, &["'a", "'b"], &nullary, &unary, &mut body);
        let _ = writeln!(source, "external v{index}: {body} = \"v{index}\"");
    }
    source.push_str("let dup = x => (x, x)\n");
    let last = nullary.last().unwrap();
    let _ = writeln!(source, "let share = (x: {last}) => (x, x)");
    source
}

/// O(the program): compile with the old checker. Panics with the source when
/// the generator wrote a program the old checker rejects.
pub(crate) fn compile(source: String) -> Program {
    let options = CompilerOptions {
        nopervasives: true,
        ..Default::default()
    };
    let compiled = compile_source_in_process(
        &source,
        "Case.res",
        "Case",
        &options,
        &ModuleRegistry::new(),
        false,
        None,
    );
    let compiled = match compiled {
        Ok(compiled) => compiled,
        Err(error) => panic!("generated program does not compile: {error:?}\n{source}"),
    };
    let unit = compiled.pers_struct.expect("published signature");
    let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
    let old = internalize_pers_struct(unit.clone(), &ctx);
    let values = old
        .ps_sig
        .iter()
        .filter_map(|item| match item {
            SignatureItem::SigValue(id, _) => Some(id.name().to_string()),
            _ => None,
        })
        .collect();
    Program {
        source,
        unit,
        values,
    }
}

/// O(length): a sequence of operations the tier allows. Operand indices are
/// always in range; `EndDef` never outnumbers `BeginDef`.
/// A plan without additions draws what its tier always drew: the cases of
/// R3a to R3d keep their seeds.
pub(crate) fn operations(rng: &mut Rng, plan: impl Into<Plan>, values: usize) -> Vec<Op> {
    let plan = plan.into();
    let tier = plan.tier;
    let mut ops = Vec::new();
    let mut operands = 0usize;
    let mut depth = 0u8;
    // [`BUILD`]: what follows an `EndDef`, last first: a tuple of two
    // operands made below them, a variable of that level, and their
    // unification, so that a binding meets a node above a node that is not
    // above the variable (decision 8 of 8.6).
    let mut follow: Vec<Op> = Vec::new();
    for _ in 0..4 + rng.below(13) {
        let operand = |rng: &mut Rng| rng.below(operands) as u16;
        let op = if let Some(op) = follow.pop() {
            op
        } else if operands == 0 {
            Op::Instance(rng.below(values) as u16)
        } else if plan.has(BUILD) && rng.below(4) == 0 {
            match rng.below(4) {
                0 => Op::Var,
                1 => Op::Tuple(operand(rng), operand(rng)),
                _ => Op::Child(operand(rng), rng.below(3) as u8),
            }
        } else {
            match rng.below(20) {
                0..=5 => Op::Instance(rng.below(values) as u16),
                6..=7 => Op::Copy(operand(rng)),
                8..=9 if depth < 4 => Op::BeginDef,
                10..=11 if depth > 0 => Op::EndDef,
                12..=14 => Op::Generalize(operand(rng)),
                15 => Op::Lower(operand(rng), rng.below(depth as usize + 1) as u8),
                16..=17 if tier == Tier::Structural || tier == Tier::Full => {
                    Op::Unify(operand(rng), operand(rng))
                }
                18 if tier >= Tier::Expand => Op::Expand(operand(rng)),
                19 if tier >= Tier::Expand => Op::Cleanup,
                _ => Op::Instance(rng.below(values) as u16),
            }
        };
        match op {
            Op::Instance(_) | Op::Copy(_) | Op::Expand(_) => operands += 1,
            Op::Var | Op::Tuple(..) | Op::Child(..) => operands += 1,
            Op::BeginDef => depth += 1,
            Op::EndDef => {
                depth -= 1;
                if plan.has(BUILD) && rng.below(2) == 0 {
                    let (tuple, var) = (operands as u16, operands as u16 + 1);
                    let unify = if rng.below(2) == 0 {
                        Op::Unify(var, tuple)
                    } else {
                        Op::Unify(tuple, var)
                    };
                    follow = vec![unify, Op::Var, Op::Tuple(operand(rng), operand(rng))];
                }
            }
            _ => {}
        }
        ops.push(op);
    }
    ops
}

/// The old checker's types of a case: the context, the environment the
/// unit's declarations are in, the schemes of its values and the level the
/// case starts at.
struct Old {
    ctx: TypeContext,
    env: Env,
    values: Vec<TypeExprRef>,
    base: i32,
}

/// O(the unit): the old checker's context for a case, built as the driver
/// builds one.
fn old_context(program: &Program, plan: Plan) -> Old {
    // Stamps start above the predefined types', as in a compilation
    // (`Ident.set_current_time 999`, compiler/ml/predef.ml).
    let ctx = TypeContext::new(Arc::new(IdGenerator::with_start_stamp(
        crate::types::predef::PREDEF_STAMP_BARRIER,
    )));
    // The unit's own types are named through the unit (`Case.a0`): they
    // resolve through the persistent environment, as for a dependent.
    let mut registry = ModuleRegistry::new();
    registry.register_module_arc(
        "Case",
        program.unit.clone(),
        InMemoryModuleInfo::new("Case.res".into(), true, Default::default(), false),
    );
    let mut persistent = PersistentEnv::from_registry(&registry);
    persistent.set_nopervasives(true);
    ctx.set_persistent_env(persistent);
    let unit = internalize_pers_struct(program.unit.clone(), &ctx);
    let mut env: Env = initial_env(&ctx);
    let mut values = Vec::new();
    let mut late = Vec::new();
    for item in unit.ps_sig.iter() {
        match item {
            SignatureItem::SigValue(_, value) => values.push(value.val_type),
            SignatureItem::SigType(id, declaration, _) => {
                if plan.has(SCOPED) && LATE.contains(&id.name()) {
                    late.push((id.name().to_string(), declaration.clone()));
                }
                env.add_type(*id, declaration.clone());
            }
            _ => {}
        }
    }
    // A unit is checked from a level above every binding time
    // (`Ctype.init_def (Ident.current_time ())`, compiler/ml/typemod.ml), so
    // that lowering a type to the unit's first level never fails the scope
    // test of `update_level` (compiler/ml/ctype.ml:591-598) for a predefined
    // type or a type of the unit. Without it the old side refused a
    // unification no compilation can refuse (seed 1000064 of the structural
    // tier: `int` bound to a variable of the starting level).
    ctx.init_def(ctx.current_stamp());
    let base = ctx.current_level();
    // The late types are bound after that level, as the types of a later
    // item are for a weak variable of this one: local identifiers with the
    // next three stamps, so that `get_level` (ctype.ml:562-569) is `base +
    // 1`, `+ 2`, `+ 3`. A type of the unit is named through the persistent
    // unit and has binding time 0, so every node that names a late type is
    // renamed to the local identifier, in the schemes and in the manifests.
    if plan.has(SCOPED) {
        assert_eq!(late.len(), LATE.len(), "{}", program.source);
        let mut renamed = Vec::new();
        for (offset, (name, declaration)) in late.iter().enumerate() {
            let id = ctx.create_ident(name.as_str());
            assert_eq!(id.stamp(), base + 1 + offset as i32, "late stamp");
            env.add_type(id, declaration.clone());
            renamed.push((name.clone(), id));
        }
        let mut seen = crate::fast_hash::AHashSet::default();
        let mut work: Vec<TypeExprRef> = values.clone();
        for item in unit.ps_sig.iter() {
            if let SignatureItem::SigType(_, declaration, _) = item {
                work.extend(declaration.type_manifest);
                work.extend(declaration.type_params.iter().copied());
            }
        }
        while let Some(ty) = work.pop() {
            let ty = ctx.repr(ty);
            if !seen.insert(ty) {
                continue;
            }
            let desc: TypeDesc = *ctx.get_desc(ty);
            if let TypeDesc::Tconstr { path, args, abbrev } = desc
                && let Some((_, id)) = renamed.iter().find(|(name, _)| name == path.last())
            {
                let path = crate::types::path::Path::pident(*id);
                ctx.set_desc(ty, TypeDesc::Tconstr { path, args, abbrev });
            }
            crate::types::btype::iter_type_expr(&ctx, ty, |child| work.push(child));
        }
    }
    Old {
        ctx,
        env,
        values,
        base,
    }
}

/// The late types of a [`SCOPED`] program, in scope order.
const LATE: [&str; 3] = ["s0", "s1", "s2"];

/// O(children): the children of an old node the two sides list in the same
/// order: an arrow's parameters and result, a tuple's elements, a
/// constructor's arguments. Any other node has none here.
fn old_children(ctx: &TypeContext, ty: TypeExprRef) -> Vec<TypeExprRef> {
    let desc: TypeDesc = *ctx.get_desc(ctx.repr(ty));
    match desc {
        TypeDesc::Tconstr { args, .. } => ctx.type_list(args).iter().collect(),
        TypeDesc::Ttuple(elements) => ctx.type_list(elements).iter().collect(),
        TypeDesc::Tarrow { args, ret } => {
            let mut children: Vec<TypeExprRef> =
                ctx.type_args(args).iter().map(|arg| arg.typ).collect();
            children.push(ret);
            children
        }
        _ => Vec::new(),
    }
}

/// O(printed nodes²): the form of every operand, and the text of a trace
/// whose nodes are numbered after the operands'.
fn old_forms(
    old: &Old,
    plan: Plan,
    operands: &[TypeExprRef],
    trace: &[(TypeExprRef, TypeExprRef)],
) -> (String, String) {
    let mut form = String::new();
    let mut seen = Vec::new();
    for (index, &operand) in operands.iter().enumerate() {
        let _ = write!(form, "{index} = ");
        old_form(&old.ctx, old.base, plan.tier.names(), operand, &mut seen, &mut form);
        form.push('\n');
    }
    let mut pairs = String::new();
    for &(left, right) in trace {
        pairs.push_str("  ");
        old_form(&old.ctx, old.base, plan.tier.names(), left, &mut seen, &mut pairs);
        pairs.push_str(" ~ ");
        old_form(&old.ctx, old.base, plan.tier.names(), right, &mut seen, &mut pairs);
        pairs.push('\n');
    }
    (form, pairs)
}

/// O(1) plus the texts: record a failed operation of an [`EXPLAIN`] case.
fn record_failure(outcome: &mut Outcome, index: usize, before: &str, after: (String, String)) {
    outcome.failed.get_or_insert(index);
    let (form, trace) = after;
    let _ = write!(outcome.form, "! {index} trace\n{trace}");
    if form == before {
        outcome.unchanged += 1;
    } else {
        outcome.changed += 1;
        let _ = write!(outcome.form, "! {index} left\n{form}");
    }
}

/// O(operations + printed nodes²): the old checker's side of a case.
pub(crate) fn run_old(program: &Program, plan: impl Into<Plan>, ops: &[Op]) -> Outcome {
    let plan = plan.into();
    let old = old_context(program, plan);
    let (ctx, env, base) = (&old.ctx, &old.env, old.base);
    let explain = plan.has(EXPLAIN);
    let mut outcome = Outcome {
        failed: None,
        form: String::new(),
        unchanged: 0,
        changed: 0,
    };
    let mut operands: Vec<TypeExprRef> = Vec::new();
    for (index, op) in ops.iter().enumerate() {
        let before = match op {
            Op::Unify(..) | Op::Lower(..) if explain => old_forms(&old, plan, &operands, &[]).0,
            _ => String::new(),
        };
        let mut failure = None;
        match *op {
            Op::Instance(value) => operands.push(ctype::instance(ctx, old.values[value as usize])),
            Op::Copy(operand) => operands.push(ctype::instance(ctx, operands[operand as usize])),
            Op::BeginDef => ctx.begin_def(),
            Op::EndDef => ctx.end_def(),
            Op::Generalize(operand) => ctype::generalize(ctx, operands[operand as usize]),
            Op::Lower(operand, level) => {
                let (level, ty) = (base + i32::from(level), operands[operand as usize]);
                if plan.has(SCOPED) {
                    // `update_level` with the environment
                    // (compiler/ml/ctype.ml:633-640). Its trace pair is the
                    // escaping node and a fresh variable; see `Fault` and
                    // section 8.6 for why it is not compared.
                    if ctype::update_level_checked(ctx, env, level, ty).is_err() {
                        failure = Some(Vec::new());
                    }
                } else {
                    ctype::update_level(ctx, level, ty);
                }
            }
            Op::Unify(left, right) => {
                let mut state = ctype::UnifyState::new();
                state.set_env(env);
                let result = ctype::unify(
                    ctx,
                    &mut state,
                    operands[left as usize],
                    operands[right as usize],
                );
                match result {
                    Ok(()) => {}
                    Err(ctype::TypeError::Unify(trace)) => failure = Some(trace),
                    Err(_) => failure = Some(Vec::new()),
                }
            }
            Op::Expand(operand) => {
                operands.push(ctype::expand_head(ctx, env, operands[operand as usize]))
            }
            Op::Cleanup => ctx.clear_abbrev_memos(),
            Op::Var => operands.push(ctx.new_var(None)),
            Op::Tuple(left, right) => operands
                .push(ctx.new_tuple(vec![operands[left as usize], operands[right as usize]])),
            Op::Child(operand, n) => {
                let ty = operands[operand as usize];
                let children = old_children(ctx, ty);
                operands.push(match children.len() {
                    0 => ty,
                    len => children[n as usize % len],
                });
            }
        }
        if let Some(trace) = failure {
            if !explain {
                return Outcome::ended(index);
            }
            let after = old_forms(&old, plan, &operands, &trace);
            record_failure(&mut outcome, index, &before, after);
        }
    }
    outcome.form.push_str(&old_forms(&old, plan, &operands, &[]).0);
    outcome
}

/// O(nodes reachable × nodes seen): print one old node; see the module text.
fn old_form(
    ctx: &TypeContext,
    base: i32,
    names: bool,
    ty: TypeExprRef,
    seen: &mut Vec<TypeExprRef>,
    out: &mut String,
) {
    let ty = ctx.repr(ty);
    if let Some(number) = seen.iter().position(|&other| other == ty) {
        let _ = write!(out, "@{number}");
        return;
    }
    let _ = write!(out, "&{}", seen.len());
    seen.push(ty);
    let level = ctx.get_level(ty);
    if level == GENERIC_LEVEL {
        out.push_str("[G]");
    } else {
        let _ = write!(out, "[{}]", level - base);
    }
    let desc: TypeDesc = *ctx.get_desc(ty);
    match desc {
        TypeDesc::Tvar(name) => {
            out.push('\'');
            if let (true, Some(name)) = (names, name) {
                out.push_str(name.as_str());
            }
        }
        TypeDesc::Tconstr { path, args, .. } => {
            out.push_str(path.last());
            let args: Vec<TypeExprRef> = ctx.type_list(args).iter().collect();
            if !args.is_empty() {
                out.push('<');
                for (index, arg) in args.into_iter().enumerate() {
                    if index != 0 {
                        out.push_str(", ");
                    }
                    old_form(ctx, base, names, arg, seen, out);
                }
                out.push('>');
            }
        }
        TypeDesc::Ttuple(elements) => {
            let elements: Vec<TypeExprRef> = ctx.type_list(elements).iter().collect();
            out.push('(');
            for (index, element) in elements.into_iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                old_form(ctx, base, names, element, seen, out);
            }
            out.push(')');
        }
        TypeDesc::Tarrow { args, ret } => {
            let params: Vec<(Option<&'static str>, bool, TypeExprRef)> = ctx
                .type_args(args)
                .iter()
                .map(|arg| (arg.label().label_name(), arg.label().is_optional(), arg.typ))
                .collect();
            out.push_str("fn(");
            for (index, (label, optional, typ)) in params.into_iter().enumerate() {
                if index != 0 {
                    out.push_str(", ");
                }
                if let Some(label) = label {
                    let _ = write!(out, "~{label}{}: ", if optional { "?" } else { "" });
                }
                old_form(ctx, base, names, typ, seen, out);
            }
            out.push_str(") => ");
            old_form(ctx, base, names, ret, seen, out);
        }
        TypeDesc::Tobject { fields } => {
            out.push_str("obj{");
            old_form(ctx, base, names, fields, seen, out);
            out.push('}');
        }
        TypeDesc::Tfield { name, mutability, typ, rest } => {
            let mutable = ctx.mutability_repr(mutability)
                == crate::types::asttypes::MutableFlag::Mutable;
            let _ = write!(out, "{}{}: ", name.as_str(), if mutable { "!" } else { "" });
            old_form(ctx, base, names, typ, seen, out);
            out.push_str("; ");
            old_form(ctx, base, names, rest, seen, out);
        }
        TypeDesc::Tnil => out.push_str("nil"),
        TypeDesc::Tvariant(row) => {
            use crate::types::type_expr::RowField;
            // `row_repr` (compiler/ml/btype.ml:126-135): the fields of a chain
            // of rows, outermost first, with the innermost row's flags.
            let row = crate::types::btype::row_repr(ctx, &ctx.row_desc(row));
            let _ = write!(
                out,
                "[{}{}",
                if row.row_closed { "closed " } else { "" },
                if row.row_fixed { "fixed " } else { "" }
            );
            for (label, field) in row.row_fields.iter() {
                let _ = write!(out, "#{label}");
                match crate::types::btype::row_field_repr(ctx, field) {
                    RowField::Rpresent(None) => {}
                    RowField::Rpresent(Some(ty)) => {
                        out.push('(');
                        old_form(ctx, base, names, ty, seen, out);
                        out.push(')');
                    }
                    RowField::Reither { constant, types, matched, .. } => {
                        let _ = write!(
                            out,
                            "?{}{}(",
                            if constant { "c" } else { "" },
                            if matched { "m" } else { "" }
                        );
                        for ty in types {
                            old_form(ctx, base, names, ty, seen, out);
                            out.push(' ');
                        }
                        out.push(')');
                    }
                    RowField::Rabsent => out.push('-'),
                }
                out.push(' ');
            }
            out.push_str("| ");
            old_form(ctx, base, names, crate::types::btype::row_more(ctx, &row), seen, out);
            if let Some((path, arguments)) = &row.row_name {
                let _ = write!(out, " as {}<", path.last());
                for &argument in arguments {
                    old_form(ctx, base, names, argument, seen, out);
                    out.push(' ');
                }
                out.push('>');
            }
            out.push(']');
        }
        TypeDesc::Tunivar(name) => {
            out.push('!');
            if let Some(name) = name {
                out.push_str(name.as_str());
            }
        }
        // The body first, then the bound variables: the slots of the
        // published node (tc/segment.rs, `ExtraDescriptor::Poly`).
        TypeDesc::Tpoly { body, vars } => {
            let vars: Vec<TypeExprRef> = ctx.type_list(vars).iter().collect();
            out.push_str("poly(");
            old_form(ctx, base, names, body, seen, out);
            out.push(';');
            for var in vars {
                out.push(' ');
                old_form(ctx, base, names, var, seen, out);
            }
            out.push(')');
        }
        _ => out.push_str("?unsupported"),
    }
}

/// The new side of a case: the converted segment, a checker over a graph of
/// it, and the scheme root of every value. In the kernel tier the checker
/// only holds the graph: every operation is R1's.
pub(crate) struct New {
    pub segment: Segment,
    pub checker: Checker,
    pub tier: Tier,
    pub plan: Plan,
    pub roots: Vec<SchemeRoot>,
    pub operands: Vec<Ty>,
    /// First instance of each value, for [`Fault::ReuseInstance`].
    first: Vec<Option<Ty>>,
}

impl New {
    /// O(the unit): convert the program's publication with `from_old`.
    pub(crate) fn convert(program: &Program, plan: impl Into<Plan>) -> New {
        let plan = plan.into();
        let tier = plan.tier;
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let segment = program
            .unit
            .with_published_graph(&ctx, |published| {
                from_old(Input::new(
                    &published.graph,
                    &published.signature,
                    "Case",
                    None,
                    &published.names,
                    [0; 32],
                ))
            })
            .expect("published graph");
        let pools = &segment.signature;
        let roots: Vec<SchemeRoot> = pools
            .ordered_items
            .iter()
            .filter(|item| item.kind == SignatureKind::Value)
            .map(|item| pools.roots[pools.values[item.declaration as usize].ty as usize])
            .collect();
        assert_eq!(roots.len(), program.values.len(), "{}", program.source);
        let mut checker = Checker::new(segment.graph(), TypeTable::default());
        // Without a plan bit no generated program has an object, a variant
        // row, a universal variable or a package, and the descriptor pools
        // stay empty.
        if plan.with & (OBJECTS | VARIANTS) != 0 {
            checker.extras = super::rows::Extras::from_segment(&segment);
        }
        if tier.memo_aware() {
            checker.types = TypeTable::from_segment(&segment);
        }
        if plan.has(EXPLAIN) {
            checker.g.mode = Mode::Explain;
        }
        let mut new = New {
            first: vec![None; roots.len()],
            segment,
            checker,
            tier,
            plan,
            roots,
            operands: Vec::new(),
        };
        if plan.has(SCOPED) {
            new.scope_late_types();
        }
        new
    }

    /// O(paths): give the late types their scopes: a graph starts at level
    /// 1, so `s0`, `s1`, `s2` are bound at levels 2, 3 and 4. Every `paths`
    /// row whose last name is a late type's is one (the unit's own
    /// identifier and the path through the unit).
    fn scope_late_types(&mut self) {
        for index in 0..self.segment.signature.paths.len() {
            let name = match self.segment.signature.paths[index] {
                PathRow::Ident(ident) => self.segment.signature.identifiers[ident as usize].name,
                PathRow::Dot { name, .. } => name,
                PathRow::Apply { .. } => continue,
            };
            let Some(offset) = LATE.iter().position(|late| *late == self.string(name)) else {
                continue;
            };
            let row = &mut self.checker.types.rows[index];
            if row.scope == 0 {
                self.checker.types.scoped += 1;
            }
            row.scope = 2 + offset as u32;
        }
    }

    /// O(1): when a unification of these two operands binds a variable
    /// operand (the left one first, compiler/ml/ctype.ml:2242-2243), its
    /// level and the other operand.
    fn bound_variable(&mut self, left: Ty, right: Ty) -> Option<(u32, Ty)> {
        let left = self.checker.g.repr(left);
        let right = self.checker.g.repr(right);
        let (l, r) = (self.checker.g.nodes[left.0 as usize], self.checker.g.nodes[right.0 as usize]);
        if left == right {
            None
        } else if l.tag() == VAR {
            Some((l.level, right))
        } else if r.tag() == VAR {
            Some((r.level, left))
        } else {
            None
        }
    }

    /// O(nodes): [`Fault::UnprunedBinding`]: lower every node reachable from
    /// `ty` that is above `level`, with no cut.
    fn lower_unpruned(&mut self, ty: Ty, level: u32) {
        let mut seen = vec![false; self.checker.g.nodes.len()];
        let mut work = vec![ty];
        while let Some(ty) = work.pop() {
            let ty = self.checker.g.repr(ty);
            if std::mem::replace(&mut seen[ty.0 as usize], true) {
                continue;
            }
            if self.checker.g.nodes[ty.0 as usize].level > level {
                self.checker.g.nodes[ty.0 as usize].level = level;
            }
            work.extend(self.children(ty));
        }
    }

    /// O(arity): the children of a node, in the old side's order
    /// (`old_children`); an extended node has none here.
    fn children(&mut self, ty: Ty) -> Vec<Ty> {
        let ty = self.checker.g.repr(ty);
        let node = self.checker.g.nodes[ty.0 as usize];
        if node.head & super::segment::EXTENDED != 0 {
            return Vec::new();
        }
        let g = &self.checker.g;
        match node.tag() {
            ARROW => (0..node.arity())
                .map(|index| g.params[(node.b + index) as usize].ty)
                .chain([Ty(node.a)])
                .collect(),
            CONSTR => (0..node.arity())
                .map(|index| g.lists[(node.b + 1 + index) as usize])
                .collect(),
            TUPLE => (0..node.arity())
                .map(|index| g.lists[(node.b + index) as usize])
                .collect(),
            _ => Vec::new(),
        }
    }

    /// O(template): an instance of a value's scheme, as R2's tests take one.
    pub(crate) fn instance(&mut self, value: usize) -> Ty {
        let root = self.roots[value];
        let template = self.segment.templates[root.template as usize];
        let base = if self.tier.memo_aware() {
            self.checker.instance(template)
        } else {
            self.checker.g.instance(template)
        };
        if root.ty.0 & RELATIVE != 0 {
            Ty(base.0 + (root.ty.0 & !RELATIVE))
        } else {
            root.ty
        }
    }

    /// O(1) plus the operation: apply one operation. `Err` is a failed
    /// unification. The tiers above `Kernel` call the R3 checker here.
    fn apply(&mut self, op: Op, fault: Fault) -> Result<(), ()> {
        match op {
            Op::Instance(value) => {
                let value = value as usize;
                let ty = match (fault, self.first[value]) {
                    (Fault::ReuseInstance, Some(first)) => first,
                    _ => self.instance(value),
                };
                if self.first[value].is_none() {
                    self.first[value] = Some(ty);
                }
                self.operands.push(ty);
            }
            Op::Copy(operand) => {
                let source = self.operands[operand as usize];
                let ty = if self.tier.memo_aware() {
                    self.checker.copy(source)
                } else {
                    self.checker.g.copy(source)
                };
                self.operands.push(ty);
            }
            Op::BeginDef => self.checker.g.begin_def(),
            Op::EndDef => self.checker.g.end_def(),
            Op::Generalize(operand) => {
                // From the tier that has a memo, a generalization forgets
                // the nullary memo first (compiler/ml/ctype.ml:519), as the
                // old side's `ctype::generalize` does.
                if fault != Fault::SkipGeneralize {
                    let ty = self.operands[operand as usize];
                    if self.tier.memo_aware() {
                        self.checker.generalize(ty);
                    } else {
                        self.checker.g.generalize(ty);
                    }
                }
            }
            Op::Lower(operand, level) => {
                let ty = self.operands[operand as usize];
                let level = 1 + u32::from(level);
                if fault == Fault::ShallowLower {
                    let ty = self.checker.g.repr(ty);
                    let node = self.checker.g.nodes[ty.0 as usize];
                    if node.level > level {
                        self.checker.g.nodes[ty.0 as usize].level = level;
                    }
                } else if !self.tier.scoped_lower() {
                    self.checker.g.lower(ty, level);
                } else {
                    // Without late types the old side lowers without an
                    // environment (`ctype::update_level`): no scope clashes.
                    let lowered = self.checker.lower(ty, level);
                    assert!(lowered.is_ok() || self.plan.has(SCOPED), "no scoped type");
                    return lowered.map_err(|_| ());
                }
            }
            Op::Unify(left, right) => {
                let (left, right) = (self.operands[left as usize], self.operands[right as usize]);
                let bound = self.bound_variable(left, right);
                let result = self.checker.unify(left, right).map_err(|_| ());
                if let (Fault::UnprunedBinding, Ok(()), Some((level, ty))) = (fault, result, bound) {
                    self.lower_unpruned(ty, level);
                }
                return result;
            }
            Op::Expand(operand) => {
                // `ctype::expand_head` is OCaml's `expand_head`.
                let ty = self
                    .checker
                    .expand_head(self.operands[operand as usize], ExpandMode::Safe)
                    .expect("safe expansion does not clash");
                self.operands.push(ty);
            }
            Op::Cleanup => self.checker.cleanup_abbrev(),
            Op::Var => {
                let serial = self.checker.g.nodes.len() as u32;
                let level = self.checker.g.level;
                let ty = self.checker.g.push(Node {
                    head: VAR,
                    level,
                    a: NONE,
                    b: serial,
                });
                self.operands.push(ty);
            }
            Op::Tuple(left, right) => {
                let (left, right) = (self.operands[left as usize], self.operands[right as usize]);
                let mut level = self.checker.g.level;
                if fault == Fault::TupleAtChildLevel {
                    let left = self.checker.g.repr(left);
                    level = self.checker.g.nodes[left.0 as usize].level;
                }
                let b = self.checker.g.lists.len() as u32;
                self.checker.g.lists.extend_from_slice(&[left, right]);
                let ty = self.checker.g.push(Node {
                    head: TUPLE | 2 << 8,
                    level,
                    a: 0,
                    b,
                });
                self.operands.push(ty);
            }
            Op::Child(operand, n) => {
                let ty = self.operands[operand as usize];
                let children = self.children(ty);
                self.operands.push(match children.len() {
                    0 => ty,
                    len => children[n as usize % len],
                });
            }
        }
        Ok(())
    }

    /// O(printed nodes): the form of every operand; see the module text.
    pub(crate) fn form(&mut self) -> String {
        self.forms(&[]).0
    }

    /// O(printed nodes): the form of every operand, and the text of a trace
    /// whose nodes are numbered after the operands'.
    pub(crate) fn forms(&mut self, trace: &[[Ty; 2]]) -> (String, String) {
        let mut form = String::new();
        let mut seen = vec![NONE; self.checker.g.nodes.len()];
        let mut count = 0;
        let operands = self.operands.clone();
        for (index, operand) in operands.into_iter().enumerate() {
            let _ = write!(form, "{index} = ");
            self.node_form(operand, &mut seen, &mut count, &mut form);
            form.push('\n');
        }
        let mut pairs = String::new();
        for &[left, right] in trace {
            pairs.push_str("  ");
            self.node_form(left, &mut seen, &mut count, &mut pairs);
            pairs.push_str(" ~ ");
            self.node_form(right, &mut seen, &mut count, &mut pairs);
            pairs.push('\n');
        }
        (form, pairs)
    }

    /// O(bytes): the text of a segment string.
    fn string(&self, index: u32) -> &str {
        let pools = &self.segment.signature;
        let range = pools.strings[index as usize];
        std::str::from_utf8(&pools.bytes[range.start as usize..(range.start + range.len) as usize])
            .expect("utf-8 name")
    }

    /// O(nodes reachable): print one new node.
    fn node_form(&mut self, ty: Ty, seen: &mut [u32], count: &mut u32, out: &mut String) {
        let ty = self.checker.g.repr(ty);
        if seen[ty.0 as usize] != NONE {
            let _ = write!(out, "@{}", seen[ty.0 as usize]);
            return;
        }
        let _ = write!(out, "&{count}");
        seen[ty.0 as usize] = *count;
        *count += 1;
        let node = self.checker.g.nodes[ty.0 as usize];
        if node.level == GENERIC {
            out.push_str("[G]");
        } else {
            // A fresh graph starts at level 1 (tc/graph.rs, `Graph::default`).
            let _ = write!(out, "[{}]", i64::from(node.level) - 1);
        }
        match node.tag() {
            VAR => {
                out.push('\'');
                if self.tier.names() && node.a != NONE {
                    out.push_str(self.string(node.a));
                }
            }
            CONSTR if node.head & super::segment::EXTENDED == 0 => {
                let name = match self.segment.signature.paths[node.a as usize] {
                    PathRow::Ident(ident) => self.segment.signature.identifiers[ident as usize].name,
                    PathRow::Dot { name, .. } => name,
                    PathRow::Apply { .. } => NONE,
                };
                if name == NONE {
                    out.push_str("?apply");
                } else {
                    out.push_str(self.string(name));
                }
                if node.arity() != 0 {
                    out.push('<');
                    for index in 0..node.arity() {
                        if index != 0 {
                            out.push_str(", ");
                        }
                        let child = self.checker.g.lists[(node.b + 1 + index) as usize];
                        self.node_form(child, seen, count, out);
                    }
                    out.push('>');
                }
            }
            TUPLE if node.head & super::segment::EXTENDED == 0 => {
                out.push('(');
                for index in 0..node.arity() {
                    if index != 0 {
                        out.push_str(", ");
                    }
                    let child = self.checker.g.lists[(node.b + index) as usize];
                    self.node_form(child, seen, count, out);
                }
                out.push(')');
            }
            ARROW => {
                out.push_str("fn(");
                for index in 0..node.arity() {
                    if index != 0 {
                        out.push_str(", ");
                    }
                    let param = self.checker.g.params[(node.b + index) as usize];
                    if param.label != NONE {
                        let optional = if param.label & 1 != 0 { "?" } else { "" };
                        let _ = write!(out, "~{}{optional}: ", self.string(param.label >> 1));
                    }
                    self.node_form(param.ty, seen, count, out);
                }
                out.push_str(") => ");
                self.node_form(Ty(node.a), seen, count, out);
            }
            TUPLE => self.extended_form(node, seen, count, out),
            _ => out.push_str("?unsupported"),
        }
    }

    /// O(1): the last component of a path row.
    fn path_name(&self, path: u32) -> &str {
        match self.segment.signature.paths[path as usize] {
            PathRow::Ident(ident) => {
                self.string(self.segment.signature.identifiers[ident as usize].name)
            }
            PathRow::Dot { name, .. } => self.string(name),
            PathRow::Apply { .. } => "?apply",
        }
    }

    /// O(nodes reachable): print one extended node (`TUPLE | EXTENDED`) as
    /// `old_form` prints the old descriptor: an object, a field, the end of
    /// a field list, or a variant. A chain of rows (a row whose `more` is a
    /// row) prints as one, the fields outermost first with the innermost
    /// row's flags (`row_repr`, compiler/ml/btype.ml:126-135).
    fn extended_form(&mut self, node: Node, seen: &mut [u32], count: &mut u32, out: &mut String) {
        use super::segment::{ExtraDescriptor, RowFieldKind};
        let slot = |new: &New, node: Node, index: u32| new.checker.g.lists[(node.b + index) as usize];
        match self.checker.extras.descriptors[node.a as usize] {
            ExtraDescriptor::Object => {
                out.push_str("obj{");
                self.node_form(slot(self, node, 0), seen, count, out);
                out.push('}');
            }
            ExtraDescriptor::Field { name, mutability } => {
                // A cell with its high bit set is a link to another cell.
                let mut cell = self.checker.extras.mutabilities[mutability as usize];
                while cell & 1 << 31 != 0 {
                    cell = self.checker.extras.mutabilities[(cell & !(1 << 31)) as usize];
                }
                let _ = write!(out, "{}{}: ", self.string(name), if cell != 0 { "!" } else { "" });
                self.node_form(slot(self, node, 0), seen, count, out);
                out.push_str("; ");
                self.node_form(slot(self, node, 1), seen, count, out);
            }
            ExtraDescriptor::Nil => out.push_str("nil"),
            ExtraDescriptor::Variant(first) => {
                // Collect the chain first: the flags are the innermost row's.
                let mut chain = vec![(node, first)];
                let more = loop {
                    let (owner, row) = *chain.last().expect("chain");
                    let more = slot(self, owner, self.checker.extras.variants[row as usize].more);
                    let more = self.checker.g.repr(more);
                    let inner = self.checker.g.nodes[more.0 as usize];
                    match inner.head & super::segment::EXTENDED != 0 {
                        true => match self.checker.extras.descriptors[inner.a as usize] {
                            ExtraDescriptor::Variant(row) => chain.push((inner, row)),
                            _ => break more,
                        },
                        false => break more,
                    }
                };
                let last = self.checker.extras.variants[chain.last().expect("chain").1 as usize];
                let _ = write!(
                    out,
                    "[{}{}",
                    if last.closed { "closed " } else { "" },
                    if last.fixed { "fixed " } else { "" }
                );
                for &(owner, row) in &chain {
                    let fields = self.checker.extras.variants[row as usize].fields;
                    for index in fields.start..fields.start + fields.len {
                        let mut field = self.checker.extras.row_fields[index as usize];
                        while field.link != NONE {
                            field = self.checker.extras.row_fields[field.link as usize];
                        }
                        let _ = write!(out, "#{}", self.string(field.name));
                        let types = field.types;
                        match field.kind {
                            RowFieldKind::Present if types.len == 0 => {}
                            RowFieldKind::Present => {
                                out.push('(');
                                self.node_form(slot(self, owner, types.start), seen, count, out);
                                out.push(')');
                            }
                            RowFieldKind::Either { constant, matched } => {
                                let _ = write!(
                                    out,
                                    "?{}{}(",
                                    if constant { "c" } else { "" },
                                    if matched { "m" } else { "" }
                                );
                                for index in types.start..types.start + types.len {
                                    self.node_form(slot(self, owner, index), seen, count, out);
                                    out.push(' ');
                                }
                                out.push(')');
                            }
                            RowFieldKind::Absent => out.push('-'),
                        }
                        out.push(' ');
                    }
                }
                out.push_str("| ");
                self.node_form(more, seen, count, out);
                if last.name != NONE {
                    let (owner, _) = *chain.last().expect("chain");
                    let _ = write!(out, " as {}<", self.path_name(last.name));
                    let arguments = last.name_arguments;
                    for index in arguments.start..arguments.start + arguments.len {
                        self.node_form(slot(self, owner, index), seen, count, out);
                        out.push(' ');
                    }
                    out.push('>');
                }
                out.push(']');
            }
            ExtraDescriptor::Univar(name) => {
                out.push('!');
                if name != NONE {
                    out.push_str(self.string(name));
                }
            }
            ExtraDescriptor::Poly => {
                out.push_str("poly(");
                self.node_form(slot(self, node, 0), seen, count, out);
                out.push(';');
                for index in 1..node.arity() {
                    out.push(' ');
                    self.node_form(slot(self, node, index), seen, count, out);
                }
                out.push(')');
            }
            _ => out.push_str("?unsupported"),
        }
    }
}

/// O(operations + printed nodes): the new graph's side of a case.
pub(crate) fn run_new(program: &Program, plan: impl Into<Plan>, ops: &[Op], fault: Fault) -> Outcome {
    let plan = plan.into();
    let mut new = New::convert(program, plan);
    let explain = plan.has(EXPLAIN);
    if fault == Fault::SuccessLevels {
        new.checker.g.mode = Mode::Success;
    }
    if fault == Fault::NoScopes {
        for row in &mut new.checker.types.rows {
            row.scope = 0;
        }
        new.checker.types.scoped = 0;
    }
    let mut outcome = Outcome {
        failed: None,
        form: String::new(),
        unchanged: 0,
        changed: 0,
    };
    for (index, &op) in ops.iter().enumerate() {
        let before = match op {
            Op::Unify(..) | Op::Lower(..) if explain => new.form(),
            _ => String::new(),
        };
        if new.apply(op, fault).is_err() {
            if !explain {
                return Outcome::ended(index);
            }
            // A failed lowering has no trace on either side (`run_old`).
            let mut trace = match op {
                Op::Unify(..) => new.checker.trace.clone(),
                _ => Vec::new(),
            };
            match fault {
                Fault::ShortTrace => {
                    trace.pop();
                }
                Fault::ReversedTrace => trace.iter_mut().for_each(|pair| pair.reverse()),
                _ => {}
            }
            let after = new.forms(&trace);
            record_failure(&mut outcome, index, &before, after);
        }
    }
    outcome.form.push_str(&new.form());
    outcome
}

/// Both sides of one case. `Err` is the report a failing test prints: the
/// seed, the program, the operations and both outcomes.
pub(crate) fn compare(
    seed: u64,
    program: &Program,
    plan: impl Into<Plan>,
    ops: &[Op],
    fault: Fault,
) -> Result<Outcome, String> {
    let plan = plan.into();
    let old = run_old(program, plan, ops);
    let new = run_new(program, plan, ops, fault);
    if old == new {
        return Ok(old);
    }
    Err(format!(
        "differential mismatch, seed {seed}\n--- program\n{}--- operations\n{ops:?}\n--- old: failed {:?}\n{}--- new: failed {:?}\n{}",
        program.source, old.failed, old.form, new.failed, new.form,
    ))
}

/// What a run of many cases saw; the callers assert it is not vacuous.
#[derive(Debug, Default)]
pub(crate) struct Coverage {
    pub cases: usize,
    /// Cases in which a unification failed.
    pub failures: usize,
    /// Cases whose form names a node twice (`@`): sharing was compared.
    pub sharing: usize,
    /// Cases whose form has a generic node and a node that is not.
    pub mixed_levels: usize,
    /// [`EXPLAIN`]: failed operations whose trace has more than one pair,
    /// those after which the graph printed as before, and those after which
    /// it did not.
    pub deep_traces: usize,
    pub unchanged: usize,
    pub changed: usize,
}

/// O(the program): the program and the operations of one case seed
/// (`program seed × 1,000,003 + sequence`), as [`run_plan`] draws them.
pub(crate) fn case(plan: Plan, case_seed: u64) -> (Program, Vec<Op>) {
    let mut rng = Rng(case_seed / 1_000_003);
    let program = compile(program_source(&mut rng, plan));
    let mut rng = Rng(case_seed);
    let ops = operations(&mut rng, plan, program.values.len());
    (program, ops)
}

/// `programs` programs from consecutive seeds, `per_program` operation
/// sequences each: what the cases that agree saw, and the report of every
/// case that does not, with its seed.
pub(crate) fn run_plan(
    plan: impl Into<Plan>,
    first_seed: u64,
    programs: u64,
    per_program: u64,
) -> (Coverage, Vec<(u64, String)>) {
    let plan = plan.into();
    let mut coverage = Coverage::default();
    let mut mismatches = Vec::new();
    for seed in first_seed..first_seed + programs {
        let mut rng = Rng(seed);
        let program = compile(program_source(&mut rng, plan));
        for sequence in 0..per_program {
            // Each sequence has its own seed, printed on failure.
            let case_seed = seed.wrapping_mul(1_000_003).wrapping_add(sequence);
            let mut rng = Rng(case_seed);
            let ops = operations(&mut rng, plan, program.values.len());
            match compare(case_seed, &program, plan, &ops, Fault::None) {
                Ok(outcome) => {
                    coverage.cases += 1;
                    coverage.failures += usize::from(outcome.failed.is_some());
                    coverage.sharing += usize::from(outcome.form.contains('@'));
                    coverage.mixed_levels += usize::from(
                        outcome.form.contains("[G]") && outcome.form.contains("[0]"),
                    );
                    coverage.deep_traces += deep_traces(&outcome.form);
                    coverage.unchanged += outcome.unchanged as usize;
                    coverage.changed += outcome.changed as usize;
                }
                Err(report) => mismatches.push((case_seed, report)),
            }
        }
    }
    (coverage, mismatches)
}

/// [`run_plan`]; panics with the report of the first mismatch.
pub(crate) fn run_cases(
    plan: impl Into<Plan>,
    first_seed: u64,
    programs: u64,
    per_program: u64,
) -> Coverage {
    let (coverage, mismatches) = run_plan(plan, first_seed, programs, per_program);
    if let Some((seed, report)) = mismatches.first() {
        panic!("case seed {seed}\n{report}");
    }
    coverage
}

/// [`run_plan`] for a plan on which the old checker is known to differ from
/// OCaml: the seeds that differ must be exactly `known`. A seed that is
/// missing means the old checker or the new one changed there: read the
/// report of section 8.6 for that seed before the list is edited.
#[cfg(test)]
pub(crate) fn run_cases_except(plan: Plan, known: &[u64]) -> Coverage {
    let (coverage, mismatches) = run_plan(plan, 1, 100, 100);
    let seeds: Vec<u64> = mismatches.iter().map(|(seed, _)| *seed).collect();
    if seeds != known {
        let unknown = mismatches.iter().find(|(seed, _)| !known.contains(seed));
        panic!(
            "{plan:?} differs on {seeds:?}, known {known:?}\n{}",
            unknown.map_or("", |(_, report)| report.as_str())
        );
    }
    coverage
}

/// What the pair of a failed top-level unification looked like when unify2
/// took it (compiler/ml/ctype.ml:2276-2303), read on a replay of the
/// operations before it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct PairShape {
    /// The left head is an abbreviation that expands and the right head is
    /// its own expansion, both structures: unify3 runs on the swapped pair
    /// and the trace below it is reversed (ctype.ml:2299-2303).
    pub swapped: bool,
    /// `create_recursion` (ctype.ml:2308): the side unify3 takes as `t2` was
    /// expanded and the other side's expanded head occurs in it, so the
    /// repair of ctype.ml:2428-2436 was pending when the failure unwound.
    pub recursion: bool,
}

/// O(the case): the shape of the pair of `ops[index]`, a unification, on a
/// replay of `ops[..index]` on the new side.
pub(crate) fn pair_shape(program: &Program, plan: Plan, ops: &[Op], index: usize) -> PairShape {
    let Op::Unify(left, right) = ops[index] else {
        return PairShape::default();
    };
    let mut new = New::convert(program, plan);
    for &op in &ops[..index] {
        // A failed operation of an explained case leaves what it leaves.
        let _ = new.apply(op, Fault::None);
    }
    let c = &mut new.checker;
    let (t1, t2) = (c.g.repr(new.operands[left as usize]), c.g.repr(new.operands[right as usize]));
    let (Ok(x1), Ok(x2)) = (c.expand_head(t1, ExpandMode::Unif), c.expand_head(t2, ExpandMode::Unif))
    else {
        return PairShape::default();
    };
    let (t1, t2, x1, x2) = (c.g.repr(t1), c.g.repr(t2), c.g.repr(x1), c.g.repr(x2));
    let structure = |c: &Checker, ty: Ty| c.g.nodes[ty.0 as usize].tag() != VAR;
    if x1 == x2 || !structure(c, x1) || !structure(c, x2) {
        return PairShape::default();
    }
    let swapped = !(t1 == x1 || t2 != x2);
    let recursion = if swapped {
        t1 != x1 && c.deep_occur(x2, t1)
    } else {
        t2 != x2 && c.deep_occur(x1, t2)
    };
    PairShape { swapped, recursion }
}

/// O(text): the failed operations of an [`EXPLAIN`] form: the index of
/// each and the number of pairs of its trace.
pub(crate) fn failed_traces(form: &str) -> Vec<(usize, usize)> {
    let mut traces = Vec::new();
    let mut open = false;
    for line in form.lines() {
        let header = line.strip_prefix("! ").and_then(|rest| rest.strip_suffix(" trace"));
        if let Some(index) = header {
            traces.push((index.parse().expect("operation index"), 0));
            open = true;
        } else if open && line.starts_with("  ") {
            traces.last_mut().expect("open trace").1 += 1;
        } else {
            open = false;
        }
    }
    traces
}

/// O(text): the failed operations of an [`EXPLAIN`] form whose trace has
/// more than one pair.
pub(crate) fn deep_traces(form: &str) -> usize {
    failed_traces(form).iter().filter(|(_, pairs)| *pairs > 1).count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_is_small() {
        assert_eq!(std::mem::size_of::<Op>(), 6);
        assert_eq!(std::mem::size_of::<Fault>(), 1);
        assert_eq!(std::mem::size_of::<Tier>(), 1);
        assert_eq!(std::mem::size_of::<Plan>(), 4);
    }

    /// The fixed program of the self-tests: sharing inside a scheme, a ground
    /// structure, an abbreviation, a labelled parameter.
    const FIXED: &str = "type t0\ntype t1<'a>\ntype a0 = int\n\
        external v0: ('a, t1<'a>) => ('a, 'a) = \"v0\"\n\
        external v1: (a0, t1<(int, string)>) = \"v1\"\n\
        external v2: (~x: 'a, 'b) => t1<'b> = \"v2\"\n\
        external v3: (int, t1<(int, string)>) = \"v3\"\n\
        let dup = x => (x, x)\n";

    #[test]
    fn the_two_sides_agree_on_a_fixed_case() {
        let program = compile(FIXED.to_string());
        assert_eq!(program.values, ["v0", "v1", "v2", "v3", "dup"]);
        let ops = [
            Op::BeginDef,
            Op::Instance(0),
            Op::Instance(0),
            Op::Instance(4),
            Op::EndDef,
            Op::Generalize(0),
            Op::Copy(0),
            Op::Lower(1, 0),
            Op::Instance(1),
            Op::Instance(2),
        ];
        let outcome =
            compare(0, &program, Tier::Kernel, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(outcome.failed, None);
        // The form is not vacuous: it shows sharing inside one instance, a
        // generic and a lowered operand, a label and both constructor forms.
        for needle in ["@", "[G]", "[0]", "[1]", "~x: ", "t1<", "a0", "fn("] {
            assert!(outcome.form.contains(needle), "{needle} not in\n{}", outcome.form);
        }
        // `v0` has one variable in four positions: three back references.
        let first = outcome.form.lines().next().unwrap();
        assert_eq!(first.matches('@').count(), 3, "{first}");
    }

    /// Each deliberately wrong operation is reported, and the report names
    /// the seed. A harness that passed these would prove nothing.
    #[test]
    fn a_wrong_operation_is_reported() {
        let program = compile(FIXED.to_string());
        let cases: [(Fault, &[Op]); 3] = [
            (
                Fault::SkipGeneralize,
                &[Op::BeginDef, Op::Instance(0), Op::EndDef, Op::Generalize(0)],
            ),
            (Fault::ReuseInstance, &[Op::Instance(0), Op::Instance(0)]),
            (
                Fault::ShallowLower,
                &[Op::BeginDef, Op::Instance(1), Op::Lower(0, 0)],
            ),
        ];
        for (fault, ops) in cases {
            compare(77, &program, Tier::Kernel, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
            let report = compare(77, &program, Tier::Kernel, ops, fault)
                .expect_err("the fault must be seen");
            assert!(report.contains("seed 77"), "{report}");
            assert!(report.contains("--- old") && report.contains("--- new"), "{report}");
        }
    }

    /// The same wrong operations are found by generated cases, not only by
    /// the hand-written ones: for each fault some seed of the first 200
    /// sequences reports it.
    #[test]
    fn generated_cases_find_each_fault() {
        let mut rng = Rng(1);
        let program = compile(program_source(&mut rng, Tier::Kernel));
        for fault in [Fault::SkipGeneralize, Fault::ReuseInstance, Fault::ShallowLower] {
            let found = (0..200u64).any(|seed| {
                let mut rng = Rng(seed);
                let ops = operations(&mut rng, Tier::Kernel, program.values.len());
                compare(seed, &program, Tier::Kernel, &ops, fault).is_err()
            });
            assert!(found, "{fault:?} not found by 200 generated cases\n{}", program.source);
        }
    }

    /// The kernel tier, on what exists on both sides today: R1's instance,
    /// copy, generalize and lower against the old checker's, through R2's
    /// conversion. 24 programs with abbreviations, 100 sequences each.
    #[test]
    fn kernel_tier_agrees_on_generated_cases() {
        let coverage = run_cases(Tier::Kernel, 1, 24, 100);
        assert_eq!(coverage.cases, 2400);
        assert_eq!(coverage.failures, 0, "no kernel operation can fail");
        // Not vacuous. Measured on the first run: 2,175 cases compare a
        // shared node, 35 have a generic and a lowered operand at once.
        assert!(coverage.sharing * 4 > coverage.cases, "{coverage:?}");
        assert!(coverage.mixed_levels >= 24, "{coverage:?}");
    }

    /// 10,000 cases of unification on programs without abbreviations.
    #[test]
    fn structural_tier_agrees_on_generated_cases() {
        let coverage = run_cases(Tier::Structural, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 20 > coverage.cases, "{coverage:?}");
        assert!((coverage.cases - coverage.failures) * 20 > coverage.cases, "{coverage:?}");
    }

    /// 10,000 cases of expansion, the two memos and their cleanup, with the
    /// memo-aware instance and copy (O11).
    #[test]
    fn expand_tier_agrees_on_generated_cases() {
        let coverage = run_cases(Tier::Expand, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert_eq!(coverage.failures, 0);
    }

    /// 10,000 cases of everything on programs with abbreviations: the
    /// acceptance test of R3c, and of every later slice.
    #[test]
    fn full_tier_agrees_on_generated_cases() {
        let coverage = run_cases(Tier::Full, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 20 > coverage.cases, "{coverage:?}");
        assert!((coverage.cases - coverage.failures) * 20 > coverage.cases, "{coverage:?}");
    }

    /// The old side of the higher tiers runs today, so the generator is
    /// known to produce unifications that succeed and that fail, and
    /// expansions that change the head, before any of R3 is built.
    #[test]
    fn old_side_of_the_full_tier_is_not_vacuous() {
        let (mut ok, mut failed, mut expanded) = (0, 0, 0);
        for seed in 1..=12u64 {
            let mut rng = Rng(seed);
            let program = compile(program_source(&mut rng, Tier::Full));
            for sequence in 0..100u64 {
                let mut rng = Rng(seed * 1_000_003 + sequence);
                let ops = operations(&mut rng, Tier::Full, program.values.len());
                if !ops.iter().any(|op| matches!(op, Op::Unify(..))) {
                    continue;
                }
                let outcome = run_old(&program, Tier::Full, &ops);
                if outcome.failed.is_some() {
                    failed += 1;
                } else {
                    ok += 1;
                    expanded += usize::from(ops.iter().any(|op| matches!(op, Op::Expand(_))));
                }
            }
        }
        assert!(ok >= 50 && failed >= 50 && expanded >= 5, "{ok} {failed} {expanded}");
    }

    /// The old checker unifies an abbreviation with its expansion: the
    /// declaration table of the generated program reaches the old side.
    #[test]
    fn old_side_expands_the_programs_abbreviations() {
        let program = compile(FIXED.to_string());
        // v1 is `(a0, t1<(int, string)>)` and v3 the same with `int` for
        // `a0`: they unify only through the declaration `type a0 = int`.
        let ops = [Op::Instance(1), Op::Instance(3), Op::Unify(0, 1)];
        let outcome = run_old(&program, Tier::Full, &ops);
        assert_eq!(outcome.failed, None, "{}", outcome.form);
        // dup's instance is an arrow: no declaration makes it a tuple.
        let ops = [Op::Instance(1), Op::Instance(4), Op::Unify(0, 1)];
        assert_eq!(run_old(&program, Tier::Full, &ops).failed, Some(2));
    }

    /// The fixed program of the second skeleton's self-tests: a late
    /// abstract type below a constructor that does not expand (`v0`) and
    /// below one that does (`v4`), and two tuples that differ in one child.
    const FIXED_SCOPED: &str = "type t0\ntype t1<'a>\ntype a0<'a> = int\n\
        type s0\ntype s1 = int\ntype s2<'a> = int\n\
        external v0: (t1<s0>, int) = \"v0\"\n\
        external v1: 'a = \"v1\"\n\
        external v2: (int, string) = \"v2\"\n\
        external v3: (int, int) = \"v3\"\n\
        external v4: (a0<s0>, int) = \"v4\"\n\
        let dup = x => (x, x)\n";

    /// A variable of the starting level against a type two definitions up.
    const BIND_BELOW: [Op; 5] = [
        Op::Var,
        Op::BeginDef,
        Op::BeginDef,
        Op::Instance(0),
        Op::Unify(0, 1),
    ];

    /// Each wrong operation of the second skeleton is reported on a
    /// hand-written case that agrees without the fault.
    #[test]
    fn a_wrong_operation_of_a_plan_is_reported() {
        let program = compile(FIXED_SCOPED.to_string());
        let explain = Plan::new(Tier::Full, EXPLAIN);
        let scoped = Plan::new(Tier::Full, SCOPED);
        let build = Plan::new(Tier::Full, BUILD);
        let clash: &[Op] = &[Op::Instance(2), Op::Instance(3), Op::Unify(0, 1)];
        let below: &[Op] = &[Op::BeginDef, Op::Instance(2), Op::EndDef, Op::Tuple(0, 0)];
        let binding: &[Op] = &[
            Op::BeginDef,
            Op::Instance(2),
            Op::EndDef,
            Op::Tuple(0, 0),
            Op::Var,
            Op::Unify(2, 1),
        ];
        let cases: [(Plan, Fault, &[Op]); 6] = [
            (explain, Fault::ShortTrace, clash),
            (explain, Fault::ReversedTrace, clash),
            (explain, Fault::SuccessLevels, clash),
            (scoped, Fault::NoScopes, &BIND_BELOW),
            (build, Fault::TupleAtChildLevel, below),
            (build, Fault::UnprunedBinding, binding),
        ];
        for (plan, fault, ops) in cases {
            compare(78, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
            let report =
                compare(78, &program, plan, ops, fault).expect_err("the fault must be seen");
            assert!(report.contains("seed 78"), "{fault:?} {report}");
        }
    }

    /// The trace of a failed unification is compared pair by pair, numbered
    /// with the operands: observed on the old checker, the pair of the two
    /// tuples and then the pair of the children that clash
    /// (`Unify ((t1, t2) :: trace)`, compiler/ml/ctype.ml:2272). The graph
    /// does not print as before the failure: the two `int` were linked
    /// before the second children clashed (ctype.ml:2255-2256), and a
    /// failure in the explaining mode undoes path compression only.
    #[test]
    fn the_explained_trace_of_a_fixed_case() {
        let program = compile(FIXED_SCOPED.to_string());
        let plan = Plan::new(Tier::Full, EXPLAIN);
        let ops = [Op::Instance(2), Op::Instance(3), Op::Unify(0, 1), Op::Instance(1)];
        let outcome = compare(0, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(outcome.failed, Some(2));
        assert_eq!((outcome.unchanged, outcome.changed), (0, 1), "{}", outcome.form);
        assert_eq!(
            outcome.form,
            "! 2 trace\n  @0 ~ @3\n  @2 ~ @4\n\
             ! 2 left\n\
             0 = &0[0](&1[0]int, &2[0]string)\n\
             1 = &3[0](@1, &4[0]int)\n\
             0 = &0[0](&1[0]int, &2[0]string)\n\
             1 = &3[0](@1, &4[0]int)\n\
             2 = &5[0]'\n"
        );
    }

    /// 10,000 cases in the explaining mode: which operations failed, every
    /// trace and the graph after every failure. Seed 35000137 differs and is
    /// not classified (section 8.6, decision 12): after a failed unification
    /// of generic operands, the new side links a later instance's nullary
    /// constructor to the node the failed unification memorized and the old
    /// side does not.
    #[test]
    fn explain_plan_agrees_on_generated_cases() {
        let coverage = run_cases_except(Plan::new(Tier::Full, EXPLAIN), &[35_000_137]);
        assert_eq!(coverage.cases, 9_999);
        // Observed: 2,223 failing cases, 317 traces of more than one pair,
        // 2,215 failures that leave the graph as it was and 503 that do not
        // (a binding made before the clash stays, compiler/ml/ctype.ml:2732).
        assert!(coverage.failures >= 2_000, "{coverage:?}");
        assert!(coverage.deep_traces >= 300, "{coverage:?}");
        assert!(coverage.unchanged >= 2_000 && coverage.changed >= 400, "{coverage:?}");
    }

    /// 10,000 cases with made variables, tuples and children, in
    /// `Mode::Success`: the generator reaches a binding to a type that
    /// holds a node above a node that is not above the variable (decision 8
    /// of 8.6), and the two sides agree on all of them.
    #[test]
    fn build_plan_agrees_on_generated_cases() {
        let plan = Plan::new(Tier::Full, BUILD);
        let coverage = run_cases(plan, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures >= 1_500, "{coverage:?}");
    }

    /// The same in the explaining mode. The seven seeds that differ are the
    /// old checker lowering a type before its occurrence check fails, where
    /// `unify1_var` checks first (`occur env t1 t2` before `update_level`,
    /// compiler/ml/ctype.ml:2216-2225; decision 6 of 8.6): read by hand for
    /// 7000101 and 15000055, the others print the same difference (the
    /// level of the tuple a variable occurs in).
    #[test]
    fn explained_build_plan_agrees_on_generated_cases() {
        let known = [
            7_000_101, 15_000_055, 36_000_190, 63_000_218, 70_000_303, 72_000_280, 98_000_380,
        ];
        let coverage = run_cases_except(Plan::new(Tier::Full, EXPLAIN | BUILD), &known);
        assert!(coverage.deep_traces >= 200, "{coverage:?}");
    }

    /// 10,000 cases with late types, in `Mode::Success`. Four seeds differ
    /// (section 8.6, decision 13): 16000145 is the old checker's nullary
    /// shortcut lowering without the environment, where OCaml's expands a
    /// type below its scope (`update_level !env t1.level t2`,
    /// compiler/ml/ctype.ml:2255); 49000200 and 49000205 are the retry of
    /// `update_level` forgetting the memos (`backtrack snap`,
    /// ctype.ml:638-639 and btype.ml:773-781) so that unify2's second
    /// expansion is a new node; 81000306 is not classified.
    #[test]
    fn scoped_plan_agrees_on_generated_cases() {
        let known = [16_000_145, 49_000_200, 49_000_205, 81_000_306];
        let coverage = run_cases_except(Plan::new(Tier::Full, SCOPED), &known);
        assert!(coverage.failures >= 2_000, "{coverage:?}");
        let known = [49_000_183];
        run_cases_except(Plan::new(Tier::Full, SCOPED | BUILD), &known);
    }

    /// Every wrong operation of the second skeleton is found by generated
    /// cases of its plan, not only by the hand-written ones.
    #[test]
    fn generated_cases_find_each_fault_of_a_plan() {
        let cases = [
            (EXPLAIN, Fault::ShortTrace),
            (EXPLAIN, Fault::ReversedTrace),
            (EXPLAIN, Fault::SuccessLevels),
            (SCOPED, Fault::NoScopes),
            (BUILD, Fault::TupleAtChildLevel),
            (BUILD, Fault::UnprunedBinding),
        ];
        for (with, fault) in cases {
            let plan = Plan::new(Tier::Full, with);
            let found = (1..=20u64).any(|seed| {
                (0..100u64).any(|sequence| {
                    let case_seed = seed * 1_000_003 + sequence;
                    let (program, ops) = case(plan, case_seed);
                    compare(case_seed, &program, plan, &ops, Fault::None).is_ok()
                        && compare(case_seed, &program, plan, &ops, fault).is_err()
                })
            });
            assert!(found, "{fault:?} not found by 2,000 generated cases");
        }
    }

    /// Seed 2000091 of the explaining mode reaches the reversed trace below
    /// a swapped unify3 (compiler/ml/ctype.ml:2299-2303): the left operand
    /// is an abbreviation that expands, the right one is its own expansion,
    /// and the clash is one pair down, so the pair below the swap is
    /// written reversed and both sides print it in the same order.
    #[test]
    fn explain_reaches_the_reversed_trace_below_a_swapped_unify3() {
        let plan = Plan::new(Tier::Full, EXPLAIN);
        let (program, ops) = case(plan, 2_000_091);
        let outcome =
            compare(2_000_091, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(failed_traces(&outcome.form), [(7, 2)]);
        let shape = pair_shape(&program, plan, &ops, 7);
        assert!(shape.swapped && !shape.recursion, "{shape:?}");
        // Reversing the trace on one side is seen: the order is compared.
        compare(2_000_091, &program, plan, &ops, Fault::ReversedTrace).expect_err("order");
    }

    /// Seeds 2000018 and 13000074 of the explaining mode with made nodes
    /// reach a clash while `create_recursion` holds
    /// (compiler/ml/ctype.ml:2308): an abbreviation against a type that
    /// occurs in its argument, the heads clash, and the repair of
    /// ctype.ml:2428-2436 is dropped with the failure. No case of the first
    /// 10,000 fails *inside* the repair or below such a pair: the second
    /// expansion of a type that expanded a moment before clashes only
    /// through a constrained parameter, and the generator declares none.
    #[test]
    fn explain_reaches_a_clash_with_the_recursion_repair_pending() {
        let plan = Plan::new(Tier::Full, EXPLAIN | BUILD);
        for (seed, index) in [(2_000_018u64, 15usize), (13_000_074, 6)] {
            let (program, ops) = case(plan, seed);
            let outcome =
                compare(seed, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
            assert!(failed_traces(&outcome.form).contains(&(index, 1)), "{}", outcome.form);
            assert!(pair_shape(&program, plan, &ops, index).recursion);
        }
    }

    /// What the old checker leaves when the retry of a lowering clashes
    /// too (the one recorded difference of R3d): the levels the second pass
    /// wrote stay ("Levels should be restored", compiler/ml/ctype.ml:599),
    /// so the tuple and `t1<s0>` are at the variable's level after the
    /// failure, and the trace ends with the escaping constructor against a
    /// new variable of the target level (`Unify [(ty, newvar2 level)]`,
    /// ctype.ml:599). Observed today.
    #[test]
    fn old_checker_keeps_the_levels_of_a_failed_retry() {
        let program = compile(FIXED_SCOPED.to_string());
        let plan = Plan::new(Tier::Full, EXPLAIN | SCOPED);
        let outcome = run_old(&program, plan, &BIND_BELOW);
        assert_eq!(outcome.failed, Some(4));
        assert_eq!(
            outcome.form,
            "! 4 trace\n  @0 ~ @1\n  @3 ~ &5[0]'\n\
             ! 4 left\n\
             0 = &0[0]'\n\
             1 = &1[0](&2[0]t1<&3[2]s0>, &4[2]int)\n\
             0 = &0[0]'\n\
             1 = &1[0](&2[0]t1<&3[2]s0>, &4[2]int)\n"
        );
    }

    /// The correction of R3d (slice R3k, section 8.6, decision 14): in the
    /// explaining mode a lowering whose retry clashes keeps what the retry
    /// wrote and adds the escaping pair to the trace, as the old checker
    /// and OCaml do. Reaches: R3k. The hand-written case, and the first
    /// generated one that shows the difference in a later operation's
    /// result (seed 1000039: the levels kept at operation 10 decide what
    /// operation 13 lowers).
    #[test]
    #[ignore = "R3k build"]
    fn a_failed_retry_keeps_its_levels_in_the_explaining_mode() {
        let program = compile(FIXED_SCOPED.to_string());
        let plan = Plan::new(Tier::Full, EXPLAIN | SCOPED);
        compare(0, &program, plan, &BIND_BELOW, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        let plan = Plan::new(Tier::Full, EXPLAIN | SCOPED | BUILD);
        let (program, ops) = case(plan, 1_000_039);
        compare(1_000_039, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
    }

    /// Recursive abbreviations through an object and through a variant,
    /// nullary and with a parameter (decision 3 of 8.6).
    const RECURSIVE: &str = "type rec ro = {\"hd\": int, \"tl\": ro}\n\
        type rec po<'a> = {\"hd\": 'a, \"tl\": po<'a>}\n\
        type rec rv = [#Nil | #Cons(int, rv)]\n\
        type rec pv<'a> = [#Nil | #Cons('a, pv<'a>)]\n\
        external v0: ro = \"v0\"\n\
        external v1: po<string> = \"v1\"\n\
        external v2: rv = \"v2\"\n\
        external v3: pv<string> = \"v3\"\n";

    /// What the old checker shows for a recursive abbreviation today
    /// (observed). The copy an expansion makes of the abbreviation's own
    /// constructor is a link to the node being expanded: for a nullary one
    /// through the memo all nullary constructors share, and for one with a
    /// parameter through the memo entry the expanding node wrote before its
    /// body was copied (`find_repr p !abbrevs`, `Some ty when repr ty != t
    /// -> Tlink ty`, compiler/ml/ctype.ml:780-782, with `abbreviations :=
    /// abbrev` set by `subst`, ctype.ml:1126). The new side agrees on the
    /// nullary ones today.
    #[test]
    fn old_checker_links_a_recursive_occurrence_to_the_node_being_expanded() {
        let program = compile(RECURSIVE.to_string());
        let plan = Plan::new(Tier::Expand, OBJECTS | VARIANTS);
        let expected = [
            "0 = &0[0]ro\n\
             1 = &1[0]obj{&2[0]hd: &3[0]poly(&4[0]int;); &5[0]tl: &6[0]poly(@0;); &7[0]nil}\n\
             2 = @0\n",
            "0 = &0[0]po<&1[0]string>\n\
             1 = &2[0]obj{&3[0]hd: &4[0]poly(@1;); &5[0]tl: &6[0]poly(@0;); &7[0]nil}\n\
             2 = &8[0]po<&9[0]string>\n",
            "0 = &0[0]rv\n\
             1 = &1[0][closed #Nil #Cons(&2[0](&3[0]int, @0)) | &4[0]nil]\n\
             2 = @0\n",
            "0 = &0[0]pv<&1[0]string>\n\
             1 = &2[0][closed #Nil #Cons(&3[0](@1, @0)) | &4[0]nil]\n\
             2 = &5[0]pv<&6[0]string>\n",
        ];
        for (value, expected) in expected.into_iter().enumerate() {
            let ops = [Op::Instance(value as u16), Op::Expand(0), Op::Instance(value as u16)];
            assert_eq!(run_old(&program, plan, &ops).form, expected);
            if value % 2 == 0 {
                compare(0, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
            }
        }
    }

    /// Instance, copy, generalize and lower on programs with objects and
    /// variants: 10,000 cases, on what exists on both sides today.
    #[test]
    fn kernel_tier_agrees_on_objects_and_variants() {
        let coverage = run_cases(Plan::new(Tier::Kernel, OBJECTS | VARIANTS), 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.sharing * 4 > coverage.cases * 3, "{coverage:?}");
    }

    /// The old side of the object and variant plans runs today: generated
    /// unifications of such programs succeed and fail (observed: 883 and
    /// 317 of 1,200 with objects, 917 and 283 with variants).
    #[test]
    fn old_side_of_the_object_and_variant_plans_is_not_vacuous() {
        for with in [OBJECTS, VARIANTS] {
            let plan = Plan::new(Tier::Full, with);
            let (mut ok, mut failed, mut rows) = (0, 0, 0);
            for seed in 1..=12u64 {
                for sequence in 0..100u64 {
                    let (program, ops) = case(plan, seed * 1_000_003 + sequence);
                    let outcome = run_old(&program, plan, &ops);
                    match outcome.failed {
                        Some(_) => failed += 1,
                        None => ok += 1,
                    }
                    rows += usize::from(outcome.form.contains("obj{") || outcome.form.contains("#"));
                }
            }
            assert!(ok >= 600 && failed >= 200 && rows >= 600, "{with}: {ok} {failed} {rows}");
        }
    }

    /// The correction of R3b (slice R3m, section 8.6, decision 16): a
    /// constructor with arguments that an expansion copies is a link to the
    /// expanding node, or to a node whose expansion made that one, when it
    /// names the same type. Reaches: R3m. Today 89 of 10,000 cases differ
    /// with objects, 159 with variants.
    #[test]
    #[ignore = "R3m build"]
    fn expand_tier_agrees_on_recursive_abbreviations() {
        let program = compile(RECURSIVE.to_string());
        let plan = Plan::new(Tier::Expand, OBJECTS | VARIANTS);
        for value in [1, 3] {
            let ops = [Op::Instance(value), Op::Expand(0), Op::Instance(value)];
            compare(0, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
        let coverage = run_cases(plan, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
    }

    /// 10,000 cases of everything on programs with objects, in both modes:
    /// the acceptance test of R3e. Reaches: R3m, R3e.
    #[test]
    #[ignore = "R3e build"]
    fn object_plan_agrees_on_generated_cases() {
        let coverage = run_cases(Plan::new(Tier::Full, OBJECTS), 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        run_cases(Plan::new(Tier::Full, OBJECTS | BUILD), 1, 100, 100);
    }

    /// 10,000 cases of everything on programs with variants, and with both:
    /// the acceptance test of R3f. Reaches: R3m, R3e, R3f.
    #[test]
    #[ignore = "R3f build"]
    fn variant_plan_agrees_on_generated_cases() {
        let coverage = run_cases(Plan::new(Tier::Full, VARIANTS), 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        run_cases(Plan::new(Tier::Full, OBJECTS | VARIANTS | BUILD), 1, 100, 100);
    }

    /// The mechanical check of the first skeleton turn's second lesson:
    /// every ignored test of R3 says which slices it reaches (`Reaches:` in
    /// its doc comment), reaches its own slice, and reaches no slice that is
    /// not built before it (section 8.1). What a test reaches is read from
    /// its text: a plan bit with the full tier reaches the slice that
    /// unifies those types, a recursive abbreviation reaches R3m from the
    /// tier that expands, a failed lowering in the explaining mode reaches
    /// R3k, and a call of a method whose body is `todo!("R3x")` reaches
    /// R3x.
    #[test]
    fn ignored_tests_name_the_slices_they_reach() {
        let before: [(&str, &[&str]); 8] = [
            ("R3k", &[]),
            ("R3m", &[]),
            ("R3e", &["R3m"]),
            ("R3f", &["R3m", "R3e"]),
            ("R3g", &["R3m", "R3e"]),
            ("R3h", &["R3m", "R3e", "R3f", "R3g"]),
            ("R3i", &["R3m", "R3e", "R3f", "R3g"]),
            ("R3j", &["R3m", "R3e", "R3f", "R3g"]),
        ];
        // Method name -> slice, from the bodies that are still `todo!`.
        let mut methods: Vec<(String, String)> = Vec::new();
        for source in [
            include_str!("rows.rs"),
            include_str!("relate.rs"),
            include_str!("unify.rs"),
        ] {
            let mut name = String::new();
            for line in source.lines() {
                let line = line.trim_start();
                if let Some(rest) = line.strip_prefix("pub fn ").or(line.strip_prefix("fn ")) {
                    name = rest.split(['(', '<']).next().unwrap_or("").to_string();
                }
                if let Some(at) = line.find("todo!(\"R3") {
                    methods.push((name.clone(), line[at + 7..at + 10].to_string()));
                }
            }
        }
        assert!(methods.iter().any(|(name, slice)| name == "unify_fields" && slice == "R3e"));
        let mut checked = 0;
        for source in [include_str!("differential.rs"), include_str!("r3_tests.rs")] {
            let lines: Vec<&str> = source.lines().collect();
            for (at, line) in lines.iter().enumerate() {
                let Some(slice) = line
                    .trim_start()
                    .strip_prefix("#[ignore = \"")
                    .and_then(|rest| rest.strip_suffix(" build\"]"))
                else {
                    continue;
                };
                let Some((_, allowed)) = before.iter().find(|(name, _)| *name == slice) else {
                    panic!("line {}: unknown slice {slice}", at + 1);
                };
                // The doc comment above, and the body down to the closing
                // brace in column one.
                let mut doc: Vec<&str> = lines[..at]
                    .iter()
                    .rev()
                    .take_while(|line| !line.trim_start().starts_with('}') && !line.is_empty())
                    .copied()
                    .collect();
                doc.reverse();
                let doc = doc.join(" ");
                let body: String = lines[at..]
                    .iter()
                    .take_while(|line| **line != "}" && **line != "    }")
                    .copied()
                    .collect::<Vec<_>>()
                    .join("\n");
                let name = body.lines().find(|line| line.contains("fn ")).unwrap_or("");
                let listed = doc
                    .split("Reaches:")
                    .nth(1)
                    .unwrap_or_else(|| panic!("no `Reaches:` above {name}"));
                // The list ends at the first full stop.
                let listed: Vec<&str> = listed
                    .split('.')
                    .next()
                    .unwrap_or("")
                    .split(|c: char| !c.is_alphanumeric())
                    .filter(|word| word.starts_with("R3") && word.len() == 3)
                    .collect();
                assert!(listed.contains(&slice), "{name} does not reach its own slice");
                for reached in &listed {
                    assert!(
                        *reached == slice || allowed.contains(reached),
                        "{name} ({slice}) reaches {reached}, which is not built before it"
                    );
                }
                let mut reaches: Vec<&str> = Vec::new();
                let full = body.contains("Tier::Full");
                let rows = body.contains("OBJECTS") || body.contains("VARIANTS");
                for (needle, reached) in [("OBJECTS", "R3e"), ("VARIANTS", "R3f")] {
                    if full && body.contains(needle) {
                        reaches.push(reached);
                    }
                }
                if rows && (full || body.contains("Tier::Expand")) {
                    reaches.push("R3m");
                }
                if body.contains("EXPLAIN") && body.contains("SCOPED") {
                    reaches.push("R3k");
                }
                for (method, reached) in &methods {
                    if body.contains(&format!(".{method}(")) {
                        reaches.push(reached);
                    }
                }
                for reached in reaches {
                    assert!(listed.contains(&reached), "{name} reaches {reached} and does not say so");
                }
                checked += 1;
            }
        }
        assert_eq!(checked, 4, "ignored R3 tests checked");
    }
}
