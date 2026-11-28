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
//! - [`OBJECTS`], [`VARIANTS`], [`UNIVARS`], [`PATTERN`], [`INSTANCES`],
//!   [`RELATIONS`]: the types and operations of slices R3e to R3i and
//!   R3s.
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

/// [`Plan::with`]: a field of a generated object type that is not its
/// first is `@set` (mutable) one time in two, and the form prints the class of every field's
/// mutability cell: `name^k` (`name!^k` when mutable), `k` numbering the
/// classes at their first visit across the operands of the case, as nodes
/// are numbered. Two fields that share a cell print one number; two equal
/// cells print two (section 8.6, decisions 17 and 27).
pub(crate) const CELLS: u16 = 1 << 6;

/// [`Plan::with`]: the form prints the class of the reference of every
/// field that is still `Reither` (`row_field option ref`,
/// compiler/ml/types.mli:160-169): `#A?^k(..)`, `k` numbering the classes
/// at their first visit across the operands of the case. Two fields that
/// share a reference print one number (section 8.6, decision 34). The
/// operations get [`Op::GeneralizeStructure`], which is what leaves a row
/// variable below its generic row, and so makes a copy share references
/// (`keep`, compiler/ml/ctype.ml:806; btype.ml:374).
pub(crate) const REFS: u16 = 1 << 7;

/// [`Plan::with`]: polymorphic types with bound variables and universal
/// variables (slice R3g; section 8.6, decision 49). With [`OBJECTS`] a
/// position that is not a leaf is a row one time in two, and a field of a
/// generated object type is polymorphic one time in two: `"x": 'p. ('p,
/// T)`, `"x": 'p 'q. ('p, 'q, T)` or `"x": 'q 'p. ('q, 'p, T)`, with `T`
/// over the bound variables and the variables in scope (so an inner
/// binder's body names an outer binder's variable, and two fields bind
/// the same names in a different order); with [`VARIANTS`] too, the body
/// is one time in four an arrow from a row whose row variable is the
/// first bound variable (`([> #A(int)] as 'p) => (T)`, `([< #A(int) | #B]
/// as 'p) => ('q, T)`). The operations get [`Op::Univar`], [`Op::Poly`] and
/// [`Op::Inside`]:
/// a polymorphic type made of any operand over any universal variable
/// (also one that an enclosing type binds already), and the body of a
/// polymorphic type as an operand of its own, where its variables are
/// outside their binder. Both forms print a polymorphic type as
/// `poly(body; variables)`, the variables in the order of the binder
/// list, and a universal variable as `!name`, each numbered as a node:
/// two types whose binders pair by position and not by name print
/// different names at one position and the same back references.
pub(crate) const UNIVARS: u16 = 1 << 8;
/// Pattern mode (slice R3h; section 8.6, decision 61). The program
/// declares two abstract types `n0` and `n1`, which both sides make
/// locally abstract types of two newtype levels (the level the case
/// starts at, and one above it), an abstract type with a parameter
/// `k<'a>` (not injective) and a data type `d<'a>` (injective); its
/// values have types over them. The operations get [`Op::Gadt`]. Both
/// sides end their form with the equations in force, one line a type
/// that has one, sorted by name: `= name := body`.
pub(crate) const PATTERN: u16 = 1 << 9;
/// GADT instances (slice R3s; section 8.6, decisions 103 and 110), on
/// top of [`PATTERN`]. A case gets [`Op::Scope`] before a pattern
/// unification; [`Op::Copy`] and [`Op::Lower`] run WITH the environment
/// of the case on both sides (`instance env`, compiler/ml/ctype.ml:
/// 846-851; `update_level env`, 633-640), and a pattern unification that
/// fails drops the whole environment it made (`Checker::leave_case`).
/// Without the bit no case has a scope, and the old checker, which adds
/// a member only to a set that exists, judges nothing of the slice.
pub(crate) const INSTANCES: u16 = 1 << 10;

/// The relations (slice R3i; section 8.12, decision 116). The operations
/// get [`Op::Moregeneral`], [`Op::Equal`] and [`Op::Matches`], and a
/// sequence that makes two generalized instances of one value, the
/// second unified with an operand first, so that a scheme is compared
/// with an instance of itself. A relation makes no operand and cannot
/// fail: its answer is a line of the form (`3: equal = true`), ahead of
/// the operands, and what it left in the graph is in the operands' form.
pub(crate) const RELATIONS: u16 = 1 << 11;

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
    /// A new operand: list slot `n mod arity` of an operand's representative
    /// when that is an object, a field or a polymorphic type (an object:
    /// its field list; a field: its type, then the rest; a polymorphic
    /// type: its body, then its variables), otherwise what `Child` gives.
    /// Never generated: hand-written cases use it to reach a node inside an
    /// object.
    Slot(u16, u8),
    /// `generalize_structure` of an operand at the current level
    /// (compiler/ml/ctype.ml:524-544, 672): the structure above the current
    /// level becomes generic, a variable above it comes down to it. What
    /// an annotation's type is after `Typetexp` made it. [`REFS`],
    /// [`CELLS`].
    GeneralizeStructure(u16),
    /// A new operand: a universal variable with no name at the current
    /// level (`newty (Tunivar None)`). [`UNIVARS`].
    Univar,
    /// A new operand: `newty (Tpoly (body, [variable]))` at the current
    /// level, of the operand `body` and the operand `variable` when that
    /// one's representative is a universal variable; otherwise the
    /// operand `body` itself. Nothing checks that the variable is free of
    /// another binder: a case binds one variable twice, which is how a
    /// binder is already known when `enter_poly` meets it
    /// (compiler/ml/ctype.ml:1656-1669). [`UNIVARS`].
    Poly(u16, u16),
    /// A new operand: what [`Op::Slot`] gives, and while that is a
    /// polymorphic type without variables, its body. So the operand is
    /// never a `Tpoly (t, [])`: against a type that is not polymorphic
    /// OCaml refuses one (`_, _ -> raise (Unify [])`, compiler/ml/ctype.ml:
    /// 2424) and the old checker unifies its body (section 8.6, decision
    /// 49), and no generated case is to meet that. [`UNIVARS`].
    Inside(u16, u8),
    /// Unify two operands in pattern mode at the current level as the
    /// newtype level (`unify_gadt`, compiler/ml/ctype.ml:2739-2750;
    /// `Checker::unify_pattern`): bit 0 of the third field is
    /// `generate_equations`, bit 1 `assume_injective` (`unify_gadt`
    /// itself is 3; unify3 installs 1 and 0 for the arguments of a
    /// constructor, ctype.ml:2352, 2368). The equations it adds stay in
    /// force for the rest of the case. [`PATTERN`].
    Gadt(u16, u16, u8),
    /// A scope of GADT instances at the current level
    /// (`Env.add_gadt_instance_level lev env`, compiler/ml/env.ml:
    /// 1307-1308; `Checker::enter_instance_scope`), for the rest of the
    /// case: a pattern unification at this level then adds its
    /// equations at the level of a set that exists. [`INSTANCES`].
    Scope,
    /// `moregeneral env inst_nongen pattern subject`
    /// (compiler/ml/ctype.ml:3104-3124; `Checker::moregeneral`): the
    /// first operand as the pattern scheme, the second as the subject,
    /// the flag `inst_nongen`. What it links stays. [`RELATIONS`].
    Moregeneral(u16, u16, bool),
    /// `equal env rename [left] [right]` (compiler/ml/ctype.ml:
    /// 3372-3376; `Checker::equal`), the flag `rename`. Both sides then
    /// forget every memorized expansion, as [`Op::Cleanup`] does
    /// (decision 115: what the memos hold after it is not compared).
    /// [`RELATIONS`].
    Equal(u16, u16, bool),
    /// `matches env ty pattern` (compiler/ml/ctype.ml:3167-3179;
    /// `Checker::matches`); then the cleanup of [`Op::Equal`].
    /// [`RELATIONS`].
    Matches(u16, u16),
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
    /// An instance of a value has the first two bound variables of every
    /// polymorphic type in the other order: what pairing by name instead
    /// of by position looks like in the form. [`UNIVARS`].
    SwappedBinders,
    /// [`Op::Gadt`] unifies in expression mode: no equation, no
    /// reification, a link where pattern mode assumes. [`PATTERN`].
    ExpressionMode,
    /// A relation answers the opposite. [`RELATIONS`].
    WrongAnswer,
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
    // [`UNIVARS`]: a row one position in two, an object three rows in four.
    let (share, objects) = if with & UNIVARS != 0 { (2, 4) } else { (4, 2) };
    if rows != 0 && depth != 0 && rng.below(share) == 0 {
        let object = rows == OBJECTS || (rows != VARIANTS && rng.below(objects) != 0);
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
                // The parser takes an attribute on a field that is not the
                // first of an inline object type.
                if with & CELLS != 0 && index != 0 && rng.below(2) == 0 {
                    out.push_str("@set ");
                }
                let _ = write!(out, "\"{}\": ", ["x", "y", "z"][member]);
                if with & UNIVARS != 0 && rng.below(2) == 0 {
                    // [`UNIVARS`]: a polymorphic field. The body names
                    // every bound variable (one that it does not name is
                    // not bound: compiler/ml/typetexp.ml:563-568 keeps the
                    // variables that are still universal and occur), then
                    // a type over the variables in scope and the bound
                    // ones; a name bound again shadows.
                    let bound: &[&str] = [&["'p"][..], &["'p", "'q"], &["'q", "'p"]][rng.below(3)];
                    let mut scope: Vec<&str> = vars.to_vec();
                    for name in bound {
                        out.push_str(name);
                        out.push(' ');
                        if !scope.contains(name) {
                            scope.push(name);
                        }
                    }
                    out.pop();
                    out.push_str(". ");
                    let mut named = 0;
                    if with & VARIANTS != 0 && rng.below(4) == 0 {
                        // A row whose row variable is the first bound
                        // variable, on the left of an arrow.
                        let row = ["[> #A(int)]", "[< #A(int) | #B]"][rng.below(2)];
                        let _ = write!(out, "({row} as {}) => ", bound[0]);
                        named = 1;
                    }
                    out.push('(');
                    for name in &bound[named..] {
                        out.push_str(name);
                        out.push_str(", ");
                    }
                    type_text_with(rng, with, depth - 1, &scope, nullary, unary, out);
                    out.push(')');
                } else {
                    type_text_with(rng, with, depth - 1, vars, nullary, unary, out);
                }
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
    if plan.has(PATTERN) {
        source.push_str(PATTERN_TYPES);
        for name in NEWTYPES {
            nullary.push(name.to_string());
        }
        unary.push("k".to_string());
        unary.push("d".to_string());
    }
    for index in 0..3 + rng.below(4) {
        let mut body = String::new();
        type_text_with(rng, plan.with, 3, &["'a", "'b"], &nullary, &unary, &mut body);
        let _ = writeln!(source, "external v{index}: {body} = \"v{index}\"");
    }
    if plan.has(PATTERN) {
        source.push_str(PATTERN_VALUES);
        if plan.has(VARIANTS) {
            source.push_str(PATTERN_ROWS);
        }
    }
    source.push_str("let dup = x => (x, x)\n");
    let last = nullary.last().unwrap();
    let _ = writeln!(source, "let share = (x: {last}) => (x, x)");
    source
}

/// The predefined types a generated program names.
const PREDEFINED: [&str; 6] = ["int", "string", "unit", "float", "bool", "array"];

/// The two types a [`PATTERN`] case makes locally abstract.
const NEWTYPES: [&str; 2] = ["n0", "n1"];

/// The declarations of a [`PATTERN`] program: the two locally abstract
/// types, an abstract type with a parameter and a data type with one.
const PATTERN_TYPES: &str = "type n0\ntype n1\ntype k<'a>\ntype d<'a> = D('a)\n";

/// The values of a [`PATTERN`] program, after the generated ones: a
/// locally abstract type against a structure and against the other one,
/// constructors of one path with arguments (abstract: `k`; a data type:
/// `d`), and a function over both.
const PATTERN_VALUES: &str = "external q0: (n0, n1, int, (int, t0)) => unit = \"q0\"\n\
     external q1: (k<n0>, k<int>, k<n1>, k<'a>) => unit = \"q1\"\n\
     external q2: (d<n0>, d<int>, d<n1>, d<'a>) => unit = \"q2\"\n\
     external q3: (n0 => n1, int => t0, (n1, n0) => 'a) => unit = \"q3\"\n";

/// With [`VARIANTS`]: rows that clash and are compatible (`#A` over a
/// locally abstract type against `#A` over `int`, a tag the other closed
/// row lacks), and rows that clash and are not (a constant tag against
/// one with an argument).
const PATTERN_ROWS: &str = "external q4: ([#A(n0) | #B], [#A(int) | #B], [#A(int) | #C], [#A | #B]) => unit = \"q4\"\n\
     external q5: ([> #A(n0)], [< #A(int) | #B], [#C(n1)]) => unit = \"q5\"\n";

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
    // [`UNIVARS`]: the operands made by `Op::Univar`.
    let mut univars: Vec<u16> = Vec::new();
    for _ in 0..4 + rng.below(13) {
        let operand = |rng: &mut Rng| rng.below(operands) as u16;
        let op = if let Some(op) = follow.pop() {
            op
        } else if operands == 0 {
            Op::Instance(rng.below(values) as u16)
        } else if (plan.has(REFS) || plan.has(CELLS)) && rng.below(6) == 0 {
            Op::GeneralizeStructure(operand(rng))
        } else if plan.has(UNIVARS) && rng.below(4) == 0 {
            // [`UNIVARS`]: a universal variable, a polymorphic type over
            // one (three times in four over an operand that is a
            // universal variable, when there is one), what is inside an
            // operand (the body of a polymorphic type, its variables).
            match rng.below(4) {
                0 => Op::Univar,
                1 => {
                    let body = operand(rng);
                    let variable = if !univars.is_empty() && rng.below(4) != 0 {
                        univars[rng.below(univars.len())]
                    } else {
                        operand(rng)
                    };
                    Op::Poly(body, variable)
                }
                _ => Op::Inside(operand(rng), rng.below(3) as u8),
            }
        } else if plan.has(PATTERN) && rng.below(3) == 0 {
            // [`PATTERN`]: a pattern unification, twice in three as
            // `unify_gadt` runs it, or a part of an operand to unify.
            // Half of them are over an instance of one of the pattern
            // values ([`PATTERN_VALUES`], before `dup` and `share`):
            // one of its parameters against another, or against any
            // operand; `follow` is last first.
            match rng.below(6) {
                0..=2 => {
                    let count = if plan.has(VARIANTS) { 6 } else { 4 };
                    let value = values - 2 - count + rng.below(count);
                    let instance = operands as u16;
                    let flags = if rng.below(4) == 0 {
                        rng.below(3) as u8
                    } else {
                        3
                    };
                    let against = if rng.below(3) == 0 {
                        operand(rng)
                    } else {
                        instance + 2
                    };
                    follow = vec![
                        Op::Gadt(instance + 1, against, flags),
                        Op::Child(instance, rng.below(4) as u8),
                        Op::Child(instance, rng.below(4) as u8),
                    ];
                    // [`INSTANCES`]: two in three get a scope at the
                    // level of the pattern, popped just before it. The
                    // generator is asked only under the bit: the cases
                    // of every other plan are what they were.
                    if plan.has(INSTANCES) && rng.below(3) != 0 {
                        follow.insert(1, Op::Scope);
                    }
                    Op::Instance(value as u16)
                }
                3 | 4 if plan.has(INSTANCES) && rng.below(2) == 0 => {
                    follow = vec![Op::Gadt(operand(rng), operand(rng), 3)];
                    Op::Scope
                }
                3 => Op::Gadt(operand(rng), operand(rng), 3),
                4 => Op::Gadt(operand(rng), operand(rng), rng.below(3) as u8),
                _ => Op::Child(operand(rng), rng.below(4) as u8),
            }
        } else if plan.has(RELATIONS) && rng.below(3) == 0 {
            // [`RELATIONS`]: a relation of two operands; or of an operand
            // and a copy of it; or, `follow` being last first, two
            // instances of one value made inside a definition, the
            // second unified with an operand, both generalized, and the
            // first asked whether it is more general than the second
            // (and the other way round).
            let (a, b) = (operand(rng), operand(rng));
            let flag = rng.below(2) == 0;
            let next = operands as u16;
            match rng.below(10) {
                0 | 1 if depth < 4 => {
                    let value = rng.below(values) as u16;
                    let (general, special) = if rng.below(3) == 0 { (next + 1, next) } else { (next, next + 1) };
                    follow = vec![
                        Op::Equal(next, next + 1, true),
                        Op::Moregeneral(general, special, flag),
                        Op::Generalize(next + 1),
                        Op::Generalize(next),
                        Op::EndDef,
                        Op::Unify(next + 1, a),
                        Op::Instance(value),
                        Op::Instance(value),
                    ];
                    Op::BeginDef
                }
                2 => {
                    follow = vec![match rng.below(3) {
                        0 => Op::Equal(a, next, flag),
                        1 => Op::Matches(a, next),
                        _ => Op::Moregeneral(next, a, flag),
                    }];
                    Op::Copy(a)
                }
                3 | 4 => Op::Moregeneral(a, b, flag),
                5 | 6 => Op::Equal(a, b, flag),
                _ => Op::Matches(a, b),
            }
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
            Op::Var
            | Op::Tuple(..)
            | Op::Child(..)
            | Op::Slot(..)
            | Op::Poly(..)
            | Op::Inside(..) => operands += 1,
            Op::Univar => {
                univars.push(operands as u16);
                operands += 1;
            }
            Op::BeginDef => depth += 1,
            Op::EndDef => {
                depth -= 1;
                if !follow.is_empty() {
                    // The `EndDef` of a [`RELATIONS`] sequence: what
                    // follows it is drawn already. No other plan has an
                    // `EndDef` in `follow`.
                } else if plan.has(BUILD) && rng.below(2) == 0 {
                    let (tuple, var) = (operands as u16, operands as u16 + 1);
                    let unify = if rng.below(2) == 0 {
                        Op::Unify(var, tuple)
                    } else {
                        Op::Unify(tuple, var)
                    };
                    follow = vec![unify, Op::Var, Op::Tuple(operand(rng), operand(rng))];
                } else if (plan.has(REFS) || plan.has(CELLS)) && operands != 0 && rng.below(2) == 0
                {
                    // [`REFS`], [`CELLS`]: what follows an `EndDef`, last
                    // first: the newest operand becomes an annotation's
                    // type (a generic row over a row variable that is
                    // not), and is copied twice.
                    let newest = operands as u16 - 1;
                    follow = vec![
                        Op::Copy(newest),
                        Op::Copy(newest),
                        Op::GeneralizeStructure(newest),
                    ];
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
pub(crate) struct Old {
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
    let mut newtypes = Vec::new();
    for item in unit.ps_sig.iter() {
        match item {
            SignatureItem::SigValue(_, value) => values.push(value.val_type),
            SignatureItem::SigType(id, declaration, _) => {
                if plan.has(SCOPED) && LATE.contains(&id.name()) {
                    late.push((id.name().to_string(), declaration.clone()));
                }
                if plan.has(PATTERN) && NEWTYPES.contains(&id.name()) {
                    newtypes.push((id.name().to_string(), declaration.clone()));
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
    let mut renamed = Vec::new();
    if plan.has(SCOPED) {
        assert_eq!(late.len(), LATE.len(), "{}", program.source);
        for (offset, (name, declaration)) in late.iter().enumerate() {
            let id = ctx.create_ident(name.as_str());
            assert_eq!(id.stamp(), base + 1 + offset as i32, "late stamp");
            env.add_type(id, declaration.clone());
            renamed.push((name.clone(), id));
        }
    }
    // [`PATTERN`]: `n0` and `n1` are locally abstract types, as `(type
    // a)` declares one (`type_newtype_level = Some (level, level)`,
    // compiler/ml/typecore.ml, `Pexp_newtype`): local identifiers whose
    // declarations have the newtype levels `base` and `base + 1`.
    if plan.has(PATTERN) {
        assert_eq!(newtypes.len(), NEWTYPES.len(), "{}", program.source);
        for (offset, (name, declaration)) in newtypes.iter().enumerate() {
            let id = ctx.create_ident(name.as_str());
            let level = base + offset as i32;
            let mut declaration = (**declaration).clone();
            declaration.type_newtype_level = Some((level, level));
            env.add_type(id, declaration);
            renamed.push((name.clone(), id));
        }
    }
    if !renamed.is_empty() {
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

/// O(arity): [`Op::Slot`] on the old side: slot `n mod arity` of an
/// object, a field or a polymorphic type, otherwise the child
/// [`old_children`] gives, or the type itself when it has none.
fn old_slot(ctx: &TypeContext, ty: TypeExprRef, n: u8) -> TypeExprRef {
    let desc: TypeDesc = *ctx.get_desc(ctx.repr(ty));
    let children = match desc {
        TypeDesc::Tobject { fields } => vec![fields],
        TypeDesc::Tfield { typ, rest, .. } => vec![typ, rest],
        TypeDesc::Tpoly { body, vars } => {
            let mut slots = vec![body];
            slots.extend(ctx.type_list(vars).iter());
            slots
        }
        _ => old_children(ctx, ty),
    };
    match children.len() {
        0 => ty,
        len => children[n as usize % len],
    }
}

/// What a form has numbered so far on the old side: the nodes, and under
/// [`CELLS`] the classes of mutability cells.
struct OldSeen {
    nodes: Vec<TypeExprRef>,
    cells: Option<Vec<crate::types::type_expr::MutabilityRef>>,
    /// [`REFS`]: the references of `Reither` fields numbered so far.
    refs: Option<Vec<crate::types::type_expr::RowFieldRef>>,
    /// The bodies of equations: a `Tnil` prints as `nil`, with no number
    /// and no level. The body of an equation is `duplicate_type
    /// destination` (compiler/ml/ctype.ml:2095), `Subst.type_expr
    /// Subst.identity`, which keeps a variable and a universal variable
    /// and copies every other node as a generic one, `Tnil` included
    /// (compiler/ml/subst.ml:132-158). The old checker keeps a `Tnil` as
    /// the node it is (`subst_identity_copy_rec`, types/ctype.rs), so the
    /// `nil` of a body is the destination's on the old side, shared by
    /// two bodies of one destination, and a new generic node on the new
    /// one. Nothing reads the level or the identity of a `nil`; the
    /// difference is on record (CHECKER_REWRITE 8.6, decision 77) and
    /// not compared.
    bare_nil: bool,
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
    let mut seen = OldSeen {
        nodes: Vec::new(),
        cells: plan.has(CELLS).then(Vec::new),
        refs: plan.has(REFS).then(Vec::new),
        bare_nil: false,
    };
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
    run_old_until(program, plan.into(), ops, &mut None)
}

/// How many of `ops` the old checker is a judge of under [`PATTERN`]
/// (section 8.6, decision 62): the operations before the first pattern
/// unification that succeeds and leaves a structure of an operand a link.
/// In pattern mode OCaml records that the two structures are assumed
/// equal and links neither (`Pattern -> add_type_equality t1' t2'`,
/// compiler/ml/ctype.ml:2327-2331); the old checker links them, so its
/// graph after such an operation is not OCaml's. [`compare`] runs both
/// sides on this prefix. O(the case × operands).
pub(crate) fn old_judges(program: &Program, plan: Plan, ops: &[Op]) -> usize {
    let mut cut = Some(ops.len());
    run_old_until(program, plan, ops, &mut cut);
    cut.unwrap()
}

/// O(nodes): the structures `ty` reaches: every node that is not a
/// variable, a universal variable or a constructor (those OCaml links in
/// pattern mode as well, ctype.ml:2247, 2250-2253, 2315-2324).
fn old_structures(
    ctx: &TypeContext,
    ty: TypeExprRef,
    seen: &mut std::collections::HashSet<TypeExprRef>,
    out: &mut Vec<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !seen.insert(ty) {
        return;
    }
    if !matches!(
        *ctx.get_desc(ty),
        TypeDesc::Tvar { .. } | TypeDesc::Tunivar { .. } | TypeDesc::Tconstr { .. }
    ) {
        out.push(ty);
    }
    let mut children = Vec::new();
    crate::types::btype::iter_type_expr(ctx, ty, |child| children.push(child));
    for child in children {
        old_structures(ctx, child, seen, out);
    }
}

/// [`run_old`]; with `cut` set, stops at the first operation the old
/// checker is not a judge of ([`old_judges`]) and writes its index.
fn run_old_until(program: &Program, plan: Plan, ops: &[Op], cut: &mut Option<usize>) -> Outcome {
    let old = old_context(program, plan);
    let (ctx, base) = (&old.ctx, old.base);
    // The environment of the case: a pattern unification that succeeds
    // leaves its equations and its reified types in it.
    let mut current = old.env.clone();
    let explain = plan.has(EXPLAIN);
    let mut outcome = Outcome {
        failed: None,
        form: String::new(),
        unchanged: 0,
        changed: 0,
    };
    let mut operands: Vec<TypeExprRef> = Vec::new();
    // [`RELATIONS`]: the answers, one line each, ahead of the form.
    let mut relations = String::new();
    for (index, op) in ops.iter().enumerate() {
        let before = match op {
            Op::Unify(..) | Op::Lower(..) | Op::Gadt(..) if explain => {
                old_forms(&old, plan, &operands, &[]).0
            }
            _ => String::new(),
        };
        let mut failure = None;
        let env = &current;
        let mut refined = None;
        let mut answer = None;
        match *op {
            Op::Moregeneral(pattern, subject, inst_nongen) => {
                let (pattern, subject) = (operands[pattern as usize], operands[subject as usize]);
                answer = Some(("moregeneral", ctype::moregeneral(ctx, env, inst_nongen, pattern, subject)));
            }
            Op::Equal(left, right, rename) => {
                let (left, right) = (operands[left as usize], operands[right as usize]);
                answer = Some(("equal", ctype::equal(ctx, env, rename, &[left], &[right])));
                ctx.clear_abbrev_memos();
            }
            Op::Matches(ty, pattern) => {
                let (ty, pattern) = (operands[ty as usize], operands[pattern as usize]);
                answer = Some(("matches", ctype::matches(ctx, env, ty, pattern)));
                ctx.clear_abbrev_memos();
            }
            Op::Instance(value) => operands.push(ctype::instance(ctx, old.values[value as usize])),
            // `instance env` (ctype.ml:846-851): the copy of a member
            // joins the member's set.
            Op::Copy(operand) if plan.has(INSTANCES) => {
                operands.push(ctype::instance_in(ctx, env, operands[operand as usize]))
            }
            Op::Copy(operand) => operands.push(ctype::instance(ctx, operands[operand as usize])),
            Op::Scope => {
                let mut scoped = env.clone();
                scoped.add_gadt_instance_level(ctx, ctx.current_level());
                refined = Some(scoped);
            }
            Op::BeginDef => ctx.begin_def(),
            Op::EndDef => ctx.end_def(),
            Op::Generalize(operand) => ctype::generalize(ctx, operands[operand as usize]),
            Op::GeneralizeStructure(operand) => {
                ctype::generalize_structure(ctx, ctx.current_level(), operands[operand as usize])
            }
            Op::Lower(operand, level) => {
                let (level, ty) = (base + i32::from(level), operands[operand as usize]);
                if plan.has(SCOPED) || plan.has(INSTANCES) {
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
            Op::Univar => operands.push(ctx.new_univar(None)),
            Op::Poly(body, variable) => {
                let (body, variable) = (operands[body as usize], operands[variable as usize]);
                let bound = matches!(*ctx.get_desc(ctx.repr(variable)), TypeDesc::Tunivar(_));
                operands.push(if bound {
                    ctx.new_poly(body, vec![variable])
                } else {
                    body
                });
            }
            Op::Slot(operand, n) => operands.push(old_slot(ctx, operands[operand as usize], n)),
            Op::Inside(operand, n) => {
                let mut ty = old_slot(ctx, operands[operand as usize], n);
                while let TypeDesc::Tpoly { body, vars } = *ctx.get_desc(ctx.repr(ty))
                    && ctx.type_list(vars).iter().next().is_none()
                {
                    ty = body;
                }
                operands.push(ty);
            }
            Op::Gadt(left, right, flags) => {
                let mut structures = Vec::new();
                if cut.is_some() {
                    let mut seen = std::collections::HashSet::new();
                    for &operand in &operands {
                        old_structures(ctx, operand, &mut seen, &mut structures);
                    }
                }
                let (result, after) = old_gadt(
                    ctx,
                    env,
                    flags,
                    operands[left as usize],
                    operands[right as usize],
                );
                match result {
                    Ok(()) => {
                        if structures.iter().any(|&node| ctx.repr(node) != node) {
                            *cut = Some(index);
                            return outcome;
                        }
                        refined = Some(after);
                    }
                    Err(trace) => failure = Some(trace),
                }
            }
        }
        if let Some(answer) = answer {
            let _ = writeln!(relations, "{index}: {} = {}", answer.0, answer.1);
        }
        if let Some(env) = refined {
            current = env;
        }
        if let Some(trace) = failure {
            if !explain {
                return Outcome::ended(index);
            }
            let after = old_forms(&old, plan, &operands, &trace);
            record_failure(&mut outcome, index, &before, after);
        }
    }
    outcome.form.push_str(&relations);
    outcome.form.push_str(&old_forms(&old, plan, &operands, &[]).0);
    if plan.has(PATTERN) {
        outcome.form.push_str(&old_equations(&old, &current));
    }
    outcome
}

/// One pattern unification on the old checker, as `unify_pattern_types_gadt`
/// runs one (types/typecore.rs): a state in pattern mode with the two
/// flags of `flags` ([`Op::Gadt`]) and the current level as the newtype
/// level. Returns the result and the environment the state ends with:
/// the equations and the reified types of a success.
pub(crate) fn old_gadt(
    ctx: &TypeContext,
    env: &Env,
    flags: u8,
    left: TypeExprRef,
    right: TypeExprRef,
) -> (Result<(), Vec<(TypeExprRef, TypeExprRef)>>, Env) {
    let mut state = ctype::UnifyState::new();
    state.set_env(env);
    state.mode = crate::types::UnifyMode::Pattern;
    state.generate_equations = flags & 1 != 0;
    state.assume_injective = flags & 2 != 0;
    state.newtype_level = Some(ctx.current_level());
    let result = match ctype::unify(ctx, &mut state, left, right) {
        Ok(()) => Ok(()),
        Err(ctype::TypeError::Unify(trace)) => Err(trace),
        Err(_) => Err(Vec::new()),
    };
    let after = state.env().cloned().unwrap_or_else(|| env.clone());
    (result, after)
}

/// O(equations × printed nodes): the equations of `env`, one line a
/// type that has a local constraint, sorted by the type's name: `= name
/// := body`, the bodies numbered together (a body is generic: `[G]`).
pub(crate) fn old_equations(old: &Old, env: &Env) -> String {
    let mut equations: Vec<(String, TypeExprRef)> = env
        .iter_local_constraints()
        .filter_map(|(path, declaration)| {
            declaration
                .type_manifest
                .map(|body| (path.last().to_string(), body))
        })
        .collect();
    equations.sort_by(|left, right| left.0.cmp(&right.0));
    let mut out = String::new();
    let mut seen = OldSeen {
        nodes: Vec::new(),
        cells: None,
        refs: None,
        bare_nil: true,
    };
    for (name, body) in equations {
        let _ = write!(out, "= {name} := ");
        old_form(&old.ctx, old.base, true, body, &mut seen, &mut out);
        out.push('\n');
    }
    out
}

/// O(nodes reachable × nodes seen): print one old node; see the module text.
fn old_form(
    ctx: &TypeContext,
    base: i32,
    names: bool,
    ty: TypeExprRef,
    seen: &mut OldSeen,
    out: &mut String,
) {
    let ty = ctx.repr(ty);
    if seen.bare_nil && matches!(*ctx.get_desc(ty), TypeDesc::Tnil) {
        out.push_str("nil");
        return;
    }
    if let Some(number) = seen.nodes.iter().position(|&other| other == ty) {
        let _ = write!(out, "@{number}");
        return;
    }
    let _ = write!(out, "&{}", seen.nodes.len());
    seen.nodes.push(ty);
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
            let _ = write!(out, "{}{}", name.as_str(), if mutable { "!" } else { "" });
            if let Some(cells) = &mut seen.cells {
                let class = ctx.mutability_ref_repr(mutability);
                let number = cells.iter().position(|&other| other == class).unwrap_or_else(|| {
                    cells.push(class);
                    cells.len() - 1
                });
                let _ = write!(out, "^{number}");
            }
            out.push_str(": ");
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
                    RowField::Reither { constant, types, matched, link } => {
                        let _ = write!(
                            out,
                            "?{}{}",
                            if constant { "c" } else { "" },
                            if matched { "m" } else { "" }
                        );
                        if let Some(refs) = &mut seen.refs {
                            let number = refs.iter().position(|&other| other == link);
                            let number = number.unwrap_or_else(|| {
                                refs.push(link);
                                refs.len() - 1
                            });
                            let _ = write!(out, "^{number}");
                        }
                        out.push('(');
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
    /// [`CELLS`]: the classes of mutability cells one form has numbered.
    cells: Vec<Ty>,
    /// [`CELLS`]: per value, whether its template has an open row
    /// (`rows::template_has_open_row`): its instances duplicate cells.
    open: Vec<bool>,
    /// [`REFS`]: the classes of references one form has numbered: the
    /// handle of an unresolved reference node, or, for a field of an
    /// unopened node, the node and the field (bit 63 set): a reference
    /// nothing else holds.
    refs: Vec<u64>,
    /// [`PATTERN`]: the names of the locally abstract types `reify` made,
    /// by type index from the segment's last path on ([`FreshNames`]).
    fresh: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
    /// Set while the bodies of equations are printed: a `nil` prints as
    /// `nil`, as on the old side (`OldSeen::bare_nil`).
    bare_nil: bool,
    /// [`RELATIONS`]: the answers so far, one line each.
    relations: String,
    /// The index of the operation being applied.
    applied: usize,
}

/// The supplier of a [`PATTERN`] case (`rows::LocalDecls`): a fresh
/// abstract type gets the next type index after the segment's paths and
/// the name `get_new_abstract_name` gives it (compiler/ml/ctype.ml:
/// 908-922): `$'a`, then `$'a1`; `$0`, `$1` for a variable without a
/// name. The program has one data type, so two different data types are
/// never compared: `Clash`.
struct FreshNames {
    first: u32,
    strings: Vec<String>,
    names: std::rc::Rc<std::cell::RefCell<Vec<String>>>,
}

impl super::rows::LocalDecls for FreshNames {
    fn fresh_abstract(&mut self, name: u32) -> u32 {
        let prefix = match self.strings.get(name as usize) {
            Some(name) if !name.is_empty() => format!("$'{name}"),
            _ => "$".to_string(),
        };
        let mut names = self.names.borrow_mut();
        let spelled = |index: usize| {
            if index == 0 && !prefix.ends_with('$') {
                prefix.clone()
            } else {
                format!("{prefix}{index}")
            }
        };
        let mut index = 0;
        while names.contains(&spelled(index)) {
            index += 1;
        }
        names.push(spelled(index));
        self.first + names.len() as u32 - 1
    }

    fn compare(&mut self, _: &mut Checker, _: u32, _: u32) -> super::rows::DeclMatch {
        super::rows::DeclMatch::Clash
    }
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
        if plan.with & (OBJECTS | VARIANTS | UNIVARS) != 0 {
            checker.extras = super::rows::Extras::from_segment(&segment, &mut checker.g);
        }
        if tier.memo_aware() {
            checker.types = TypeTable::from_segment(&segment);
        }
        if plan.has(EXPLAIN) {
            checker.g.mode = Mode::Explain;
        }
        let open = roots
            .iter()
            .map(|root| {
                let template = segment.templates[root.template as usize];
                // The kernel tier is R1's instance: it has no duplicate.
                plan.has(CELLS)
                    && tier != Tier::Kernel
                    && super::rows::template_has_open_row(
                        &segment.template_nodes,
                        super::template::slots(&segment.template_lists, &segment.template_pools, template),
                        &checker.extras.descriptors,
                        template,
                    )
            })
            .collect();
        let mut new = New {
            first: vec![None; roots.len()],
            cells: Vec::new(),
            refs: Vec::new(),
            fresh: Default::default(),
            bare_nil: false,
            relations: String::new(),
            applied: 0,
            open,
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
        if plan.has(PATTERN) {
            new.declare_newtypes();
        }
        new
    }

    /// O(paths): [`PATTERN`]: `n0` and `n1` are locally abstract types of
    /// the newtype levels 1 and 2 (a graph starts at level 1), on every
    /// `paths` row that names one, with the scope `get_level` gives a
    /// newtype (its first level, compiler/ml/ctype.ml:562-569); and the
    /// supplier of fresh abstract types is installed.
    fn declare_newtypes(&mut self) {
        use super::expand::{NEWTYPE, Newtype};
        for index in 0..self.segment.signature.paths.len() {
            let name = match self.segment.signature.paths[index] {
                PathRow::Ident(ident) => self.segment.signature.identifiers[ident as usize].name,
                PathRow::Dot { name, .. } => name,
                PathRow::Apply { .. } => continue,
            };
            // The old side sees the unit from outside, as `Case`: its
            // types are paths through a module there and only the
            // predefined types are bare identifiers (`LOCAL`).
            if PREDEFINED.contains(&self.string(name)) {
                self.checker.types.set_local(index as u32);
                self.checker.types.set_predefined(index as u32);
            }
            let Some(offset) = NEWTYPES
                .iter()
                .position(|newtype| *newtype == self.string(name))
            else {
                continue;
            };
            let level = 1 + offset as u32;
            let types = &mut self.checker.types;
            types.newtypes.push(Newtype {
                level,
                expansion_level: level,
            });
            let row = &mut types.rows[index];
            row.flags |= NEWTYPE;
            row.newtype = types.newtypes.len() as u32 - 1;
            if level > 1 {
                if row.scope == 0 {
                    types.scoped += 1;
                }
                row.scope = level;
            }
        }
        let pools = &self.segment.signature;
        let strings = (0..pools.strings.len() as u32)
            .map(|at| self.string(at).to_string())
            .collect();
        self.checker.locals = Some(Box::new(FreshNames {
            first: pools.paths.len() as u32,
            strings,
            names: self.fresh.clone(),
        }));
    }

    /// O(equations × printed nodes): [`PATTERN`]: the equations in force
    /// (`Checker::equations`), as [`old_equations`] prints them: one line
    /// a type, sorted by name, the body the equation's own generic copy
    /// of its destination, the bodies numbered together.
    fn equations(&mut self) -> String {
        let mut equations: Vec<(String, Ty)> = Vec::new();
        for at in 0..self.checker.equations.len() {
            let index = self.checker.equations[at].type_index;
            let info = self.checker.types.info(index);
            // The body of an equation is a generic node of the graph
            // (`Checker::add_gadt_equation`), not a template.
            let manifest = self.checker.types.manifests[info.manifest as usize];
            equations.push((self.type_name(index), manifest.body));
        }
        equations.sort_by(|left, right| left.0.cmp(&right.0));
        let mut seen = vec![NONE; self.checker.g.nodes.len()];
        let mut count = 0;
        let mut out = String::new();
        // As `old_equations`: no class of a reference or of a cell, and
        // a `nil` without a number or a level.
        let plan = self.plan;
        self.plan.with &= !(REFS | CELLS);
        self.bare_nil = true;
        for (name, body) in equations {
            let _ = write!(out, "= {name} := ");
            self.node_form(body, &mut seen, &mut count, &mut out);
            out.push('\n');
        }
        self.plan = plan;
        self.bare_nil = false;
        out
    }

    /// O(1): the name a type index prints with: the last component of its
    /// path, or the name of a fresh abstract type.
    fn type_name(&self, index: u32) -> String {
        let paths = self.segment.signature.paths.len() as u32;
        if index >= paths {
            return self.fresh.borrow()[(index - paths) as usize].clone();
        }
        self.path_name(index).to_string()
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

    /// O(nodes made since `first`): [`Fault::SwappedBinders`]: exchange
    /// the first two bound variables of every polymorphic type among them.
    fn swap_binders(&mut self, first: usize) {
        for index in first..self.checker.g.nodes.len() {
            let node = self.checker.g.nodes[index];
            let poly = node.head & super::segment::EXTENDED != 0
                && node.tag() == TUPLE
                && node.arity() >= 3
                && matches!(
                    self.checker.extras.descriptors[node.a as usize],
                    super::segment::ExtraDescriptor::Poly
                );
            if poly {
                self.checker
                    .g
                    .lists
                    .swap(node.b as usize + 1, node.b as usize + 2);
            }
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

    /// O(arity): [`Op::Slot`] on the new side; see `old_slot`.
    fn slot(&mut self, ty: Ty, n: u8) -> Ty {
        use super::segment::{EXTENDED, ExtraDescriptor};
        let at = self.checker.g.repr(ty);
        let node = self.checker.g.nodes[at.0 as usize];
        let listed = node.head & EXTENDED != 0
            && node.arity() != 0
            && matches!(
                self.checker.extras.descriptors[node.a as usize],
                ExtraDescriptor::Object | ExtraDescriptor::Field { .. } | ExtraDescriptor::Poly
            );
        if listed {
            return self.checker.g.lists[(node.b + u32::from(n) % node.arity()) as usize];
        }
        let children = self.children(ty);
        match children.len() {
            0 => ty,
            len => children[n as usize % len],
        }
    }

    /// O(template): an instance of a value's scheme, as R2's tests take one.
    pub(crate) fn instance(&mut self, value: usize) -> Ty {
        let root = self.roots[value];
        let template = self.segment.templates[root.template as usize];
        let base = if self.open[value] {
            self.checker.instance_open(template)
        } else if self.tier.memo_aware() {
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
                let made = self.checker.g.nodes.len();
                let ty = match (fault, self.first[value]) {
                    (Fault::ReuseInstance, Some(first)) => first,
                    _ => self.instance(value),
                };
                if fault == Fault::SwappedBinders {
                    self.swap_binders(made);
                }
                if self.first[value].is_none() {
                    self.first[value] = Some(ty);
                }
                self.operands.push(ty);
            }
            Op::Scope => {
                let level = self.checker.g.level;
                self.checker.enter_instance_scope(level);
                // A scope is a new environment, and the next expansion
                // in a new environment forgets the memorized ones
                // (`check_abbrev_env`, compiler/ml/ctype.ml:1163-1167);
                // the walk says so with `Checker::set_env`.
                self.checker.cleanup_abbrev();
            }
            Op::Copy(operand) => {
                let source = self.operands[operand as usize];
                let ty = if self.plan.has(INSTANCES) {
                    self.checker.copy_in(source)
                } else if self.tier.memo_aware() {
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
            Op::GeneralizeStructure(operand) => {
                let ty = self.operands[operand as usize];
                let level = self.checker.g.level;
                if self.tier.memo_aware() {
                    self.checker.generalize_structure(ty, level);
                } else {
                    self.checker.g.generalize_structure(ty, level);
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
                } else if self.plan.has(INSTANCES) {
                    // With the environment, as the old side lowers
                    // under this bit.
                    return self.checker.lower(ty, level).map_err(|_| ());
                } else if !self.tier.scoped_lower() || !self.plan.has(SCOPED) {
                    // Without late types the old side lowers without an
                    // environment (`ctype::update_level`): no scope
                    // clashes, also when a pattern case has given `n1`
                    // and the types `reify` made a scope.
                    self.checker.g.lower(ty, level);
                } else {
                    return self.checker.lower(ty, level).map_err(|_| ());
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
            Op::Univar => {
                let a = self.checker.extras.univar(NONE);
                let (level, b) = (self.checker.g.level, self.checker.g.lists.len() as u32);
                let ty = self.checker.g.push(Node {
                    head: TUPLE | super::segment::EXTENDED,
                    level,
                    a,
                    b,
                });
                self.operands.push(ty);
            }
            Op::Poly(body, variable) => {
                let (body, variable) = (
                    self.operands[body as usize],
                    self.operands[variable as usize],
                );
                let variable_root = self.checker.g.repr(variable);
                if !self.checker.is_univar(variable_root) {
                    self.operands.push(body);
                    return Ok(());
                }
                let a = self.checker.extras.descriptors.len() as u32;
                self.checker
                    .extras
                    .descriptors
                    .push(super::segment::ExtraDescriptor::Poly);
                let (level, b) = (self.checker.g.level, self.checker.g.lists.len() as u32);
                self.checker.g.lists.extend_from_slice(&[body, variable]);
                let ty = self.checker.g.push(Node {
                    head: TUPLE | super::segment::EXTENDED | 2 << 8,
                    level,
                    a,
                    b,
                });
                self.operands.push(ty);
            }
            Op::Slot(operand, n) => {
                let slot = self.slot(self.operands[operand as usize], n);
                self.operands.push(slot);
            }
            Op::Inside(operand, n) => {
                use super::segment::{EXTENDED, ExtraDescriptor};
                let mut ty = self.slot(self.operands[operand as usize], n);
                loop {
                    let at = self.checker.g.repr(ty);
                    let node = self.checker.g.nodes[at.0 as usize];
                    let bare = node.head & EXTENDED != 0
                        && node.arity() == 1
                        && matches!(
                            self.checker.extras.descriptors[node.a as usize],
                            ExtraDescriptor::Poly
                        );
                    if !bare {
                        break;
                    }
                    ty = self.checker.g.lists[node.b as usize];
                }
                self.operands.push(ty);
            }
            Op::Moregeneral(pattern, subject, inst_nongen) => {
                let (pattern, subject) = (self.operands[pattern as usize], self.operands[subject as usize]);
                let answer = self.checker.moregeneral(inst_nongen, pattern, subject);
                self.answer("moregeneral", answer != (fault == Fault::WrongAnswer));
            }
            Op::Equal(left, right, rename) => {
                let (left, right) = (self.operands[left as usize], self.operands[right as usize]);
                let answer = self.checker.equal(rename, &[left], &[right]);
                self.checker.cleanup_abbrev();
                self.answer("equal", answer != (fault == Fault::WrongAnswer));
            }
            Op::Matches(ty, pattern) => {
                let (ty, pattern) = (self.operands[ty as usize], self.operands[pattern as usize]);
                let answer = self.checker.matches(ty, pattern);
                self.checker.cleanup_abbrev();
                self.answer("matches", answer != (fault == Fault::WrongAnswer));
            }
            Op::Gadt(left, right, flags) => {
                let (left, right) = (self.operands[left as usize], self.operands[right as usize]);
                if fault == Fault::ExpressionMode {
                    return self.checker.unify(left, right).map_err(|_| ());
                }
                let level = self.checker.g.level;
                // A caller that goes on after a failed pattern
                // unification drops the environment it made (`set_state`,
                // compiler/ml/typecore.ml:1299-1305), as the old side of
                // the harness does: the equations it added are cut.
                let equations = self.checker.equations.len();
                let mark = self.checker.case_mark();
                let result =
                    self.checker
                        .unify_pattern(level, flags & 1 != 0, flags & 2 != 0, left, right);
                if result.is_err() {
                    if self.plan.has(INSTANCES) {
                        // The whole environment: the reified types it
                        // made are local constraints too (decision 85).
                        self.checker.leave_case(mark);
                    } else {
                        self.checker.cut_equations(equations);
                    }
                }
                return result.map_err(|_| ());
            }
        }
        Ok(())
    }

    /// O(1) amortized: one answer line of a relation, numbered by the
    /// operation's index.
    fn answer(&mut self, relation: &str, answer: bool) {
        let _ = writeln!(self.relations, "{}: {relation} = {answer}", self.applied);
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
        self.cells.clear();
        self.refs.clear();
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
        if self.bare_nil {
            // As the old side's `OldSeen::bare_nil`.
            let node = self.checker.g.nodes[ty.0 as usize];
            if node.head & super::segment::EXTENDED != 0
                && matches!(
                    self.checker.extras.descriptors[node.a as usize],
                    super::segment::ExtraDescriptor::Nil
                )
            {
                out.push_str("nil");
                return;
            }
        }
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
                out.push_str(&self.type_name(node.a));
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
            TUPLE => self.extended_form(ty, node, seen, count, out),
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
    fn extended_form(&mut self, ty: Ty, node: Node, seen: &mut [u32], count: &mut u32, out: &mut String) {
        use super::segment::{ExtraDescriptor, RowFieldKind};
        let slot = |new: &New, node: Node, index: u32| new.checker.g.lists[(node.b + index) as usize];
        match self.checker.extras.descriptors[node.a as usize] {
            ExtraDescriptor::Object => {
                out.push_str("obj{");
                self.node_form(slot(self, node, 0), seen, count, out);
                out.push('}');
            }
            ExtraDescriptor::Field { name, mutability } => {
                let class = super::rows::cell_repr(&self.checker.g, Ty(mutability));
                let mutable = super::rows::cell_mutable(&self.checker.g, class);
                let _ = write!(out, "{}{}", self.string(name), if mutable { "!" } else { "" });
                if self.plan.has(CELLS) {
                    let number = self.cells.iter().position(|&other| other == class);
                    let number = number.unwrap_or_else(|| {
                        self.cells.push(class);
                        self.cells.len() - 1
                    });
                    let _ = write!(out, "^{number}");
                }
                out.push_str(": ");
                self.node_form(slot(self, node, 0), seen, count, out);
                out.push_str("; ");
                self.node_form(slot(self, node, 1), seen, count, out);
            }
            ExtraDescriptor::Nil => out.push_str("nil"),
            ExtraDescriptor::Variant(first) => {
                // Collect the chain first: the flags are the innermost row's.
                let mut chain = vec![(ty, node, first)];
                let more = loop {
                    let (_, owner, row) = *chain.last().expect("chain");
                    let more = slot(self, owner, self.checker.extras.variants[row as usize].more);
                    let more = self.checker.g.repr(more);
                    let inner = self.checker.g.nodes[more.0 as usize];
                    match inner.head & super::segment::EXTENDED != 0 {
                        true => match self.checker.extras.descriptors[inner.a as usize] {
                            ExtraDescriptor::Variant(row) => chain.push((more, inner, row)),
                            _ => break more,
                        },
                        false => break more,
                    }
                };
                let last = self.checker.extras.variants[chain.last().expect("chain").2 as usize];
                let _ = write!(
                    out,
                    "[{}{}",
                    if last.closed { "closed " } else { "" },
                    if last.fixed { "fixed " } else { "" }
                );
                // Each field as `row_field_repr` gives it (compiler/ml/
                // btype.ml:112-121): `rows::field_repr` follows the chain of
                // references from the field's slot.
                let mut types = Vec::new();
                for &(home, owner, row) in &chain {
                    let fields = self.checker.extras.variants[row as usize].fields;
                    for index in fields.start..fields.start + fields.len {
                        let field = self.checker.extras.row_fields[index as usize];
                        let repr =
                            super::rows::field_repr(&self.checker.g, owner.b, owner.arity(), field);
                        let _ = write!(out, "#{}", self.string(field.name));
                        match repr.kind {
                            RowFieldKind::Present if repr.first.0 == NONE => {}
                            RowFieldKind::Present => {
                                out.push('(');
                                self.node_form(repr.first, seen, count, out);
                                out.push(')');
                            }
                            RowFieldKind::Either { constant, matched } => {
                                let _ = write!(
                                    out,
                                    "?{}{}",
                                    if constant { "c" } else { "" },
                                    if matched { "m" } else { "" }
                                );
                                if self.plan.has(REFS) {
                                    let class = match repr.end.0 {
                                        NONE => 1 << 63 | u64::from(home.0) << 24 | u64::from(index),
                                        end => u64::from(end),
                                    };
                                    let number = self.refs.iter().position(|&other| other == class);
                                    let number = number.unwrap_or_else(|| {
                                        self.refs.push(class);
                                        self.refs.len() - 1
                                    });
                                    let _ = write!(out, "^{number}");
                                }
                                out.push('(');
                                types.clear();
                                super::rows::field_types(
                                    &self.checker.g,
                                    owner.b,
                                    owner.arity(),
                                    field,
                                    &mut types,
                                );
                                for &ty in &types {
                                    self.node_form(ty, seen, count, out);
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
                    let (_, owner, _) = *chain.last().expect("chain");
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
    // Descriptor rows are shared by every instance of a scheme: no
    // operation writes one in place (section 8.6, decision 27). The rows
    // the case starts with are compared after every operation.
    let frozen = (
        new.checker.extras.descriptors.clone(),
        new.checker.extras.variants.clone(),
        new.checker.extras.row_fields.clone(),
    );
    for (index, &op) in ops.iter().enumerate() {
        let extras = &new.checker.extras;
        assert!(
            extras.descriptors[..frozen.0.len()] == frozen.0[..]
                && extras.variants[..frozen.1.len()] == frozen.1[..]
                && extras.row_fields[..frozen.2.len()] == frozen.2[..],
            "a descriptor row was written in place before operation {index}: {ops:?}\n{}",
            program.source
        );
        let before = match op {
            Op::Unify(..) | Op::Lower(..) | Op::Gadt(..) if explain => new.form(),
            _ => String::new(),
        };
        new.applied = index;
        if new.apply(op, fault).is_err() {
            if !explain {
                return Outcome::ended(index);
            }
            // A failed lowering has no trace on either side (`run_old`).
            let mut trace = match op {
                Op::Unify(..) | Op::Gadt(..) => new.checker.trace.clone(),
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
    outcome.form.push_str(&new.relations);
    outcome.form.push_str(&new.form());
    if plan.has(PATTERN) {
        outcome.form.push_str(&new.equations());
    }
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
    // [`PATTERN`]: only the operations the old checker is a judge of.
    let ops = match plan.has(PATTERN) {
        true => &ops[..old_judges(program, plan, ops)],
        false => ops,
    };
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

    /// The same in the explaining mode. The six seeds that differ are the
    /// old checker lowering a type before its occurrence check fails, where
    /// `unify1_var` checks first (`occur env t1 t2` before `update_level`,
    /// compiler/ml/ctype.ml:2216-2225; decision 6 of 8.6): read by hand for
    /// 7000101 and 15000055, the others print the same difference (the
    /// level of the tuple a variable occurs in).
    #[test]
    fn explained_build_plan_agrees_on_generated_cases() {
        let known = [
            7_000_101, 15_000_055, 63_000_218, 70_000_303, 72_000_280, 98_000_380,
        ];
        let coverage = run_cases_except(Plan::new(Tier::Full, EXPLAIN | BUILD), &known);
        assert!(coverage.deep_traces >= 200, "{coverage:?}");
    }

    /// 10,000 cases with late types, in `Mode::Success`. Three seeds differ
    /// (section 8.6, decision 13): 16000145 is the old checker's nullary
    /// shortcut lowering without the environment, where OCaml's expands a
    /// type below its scope (`update_level !env t1.level t2`,
    /// compiler/ml/ctype.ml:2255); 49000200 and 49000205 are the retry of
    /// `update_level` forgetting the memos (`backtrack snap`,
    /// ctype.ml:638-639 and btype.ml:773-781) so that unify2's second
    /// expansion is a new node.
    #[test]
    fn scoped_plan_agrees_on_generated_cases() {
        let known = [16_000_145, 49_000_200, 49_000_205];
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

    /// Three abbreviations with a parameter that reach each other through
    /// objects: the chain of inherited memo entries has more than one row.
    const MUTUAL: &str = "type rec m1<'a> = {\"a\": 'a, \"n\": m2<'a>}\n\
        and m2<'a> = {\"a\": 'a, \"n\": m3<'a>}\n\
        and m3<'a> = {\"p\": m1<'a>, \"q\": m2<'a>}\n\
        external v0: m1<string> = \"v0\"\n";

    /// Operand 0 is an `m1<string>` node, 5 the `m2` node its expansion
    /// made, 10 the `m3` node the expansion of 5 made; then 10 is expanded.
    const CHAIN_KEPT: [Op; 12] = [
        Op::Instance(0),
        Op::Expand(0),
        Op::Slot(1, 0),
        Op::Slot(2, 1),
        Op::Slot(3, 0),
        Op::Slot(4, 0),
        Op::Expand(5),
        Op::Slot(6, 0),
        Op::Slot(7, 1),
        Op::Slot(8, 0),
        Op::Slot(9, 0),
        Op::Expand(10),
    ];

    /// As [`CHAIN_KEPT`], with every memo cleaned and 5 expanded again
    /// before 10 is expanded.
    const CHAIN_CLEANED: [Op; 14] = [
        Op::Instance(0),
        Op::Expand(0),
        Op::Slot(1, 0),
        Op::Slot(2, 1),
        Op::Slot(3, 0),
        Op::Slot(4, 0),
        Op::Expand(5),
        Op::Slot(6, 0),
        Op::Slot(7, 1),
        Op::Slot(8, 0),
        Op::Slot(9, 0),
        Op::Cleanup,
        Op::Expand(5),
        Op::Expand(10),
    ];

    /// Object types whose fields' cells an instance duplicates (an open
    /// row of the scheme: `v0`, `v2`, `v4`) or shares (a closed row: `v1`,
    /// `v3`).
    const CELL_PROGRAM: &str = "external v0: {.. \"a\": int, \"x\": int} => unit = \"v0\"\n\
        external v1: {\"a\": int, \"x\": int} => unit = \"v1\"\n\
        external v2: {.. \"a\": int, @set \"x\": int} => unit = \"v2\"\n\
        external v3: {\"a\": int, @set \"x\": int} => unit = \"v3\"\n\
        external v4: ({.. \"a\": int, \"x\": int} as 'r, 'r) => unit = \"v4\"\n";

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

    /// What the old checker shows for a chain of inherited entries today
    /// (observed). With every entry in place, the copies the expansion of
    /// the `m3` node makes of `m1<'a>` and `m2<'a>` are links to the two
    /// nodes whose expansions led to it (`@0`, `@7`): `find_repr` goes on
    /// through `Mlink` (compiler/ml/ctype.ml:720-724, 796-798). After a
    /// cleanup the list of the `m2` node is empty (`abbr := Mnil`,
    /// compiler/ml/btype.ml:626) and so ends there; the `m3` node still
    /// names that list, so when the `m2` node is expanded again its new
    /// entry is found (`@7`) and the `m1` node's is not (a new `m1` node).
    #[test]
    fn old_checker_inherits_entries_along_the_chain() {
        let program = compile(MUTUAL.to_string());
        let plan = Plan::new(Tier::Expand, OBJECTS);
        let kept = run_old(&program, plan, &CHAIN_KEPT).form;
        assert!(
            kept.ends_with(
                "11 = &16[0]obj{&17[0]p: &18[0]poly(@0;); &19[0]q: &20[0]poly(@7;); &21[0]nil}\n"
            ),
            "{kept}"
        );
        let cleaned = run_old(&program, plan, &CHAIN_CLEANED).form;
        assert!(
            cleaned.ends_with(
                "12 = &23[0]obj{&24[0]p: &25[0]poly(&26[0]m1<@1>;); &27[0]q: &28[0]poly(@7;); &29[0]nil}\n"
            ),
            "{cleaned}"
        );
    }

    /// The same two cases on both sides: the acceptance of the chain, of
    /// what a cleanup cuts and of what a later expansion revives (section
    /// 8.6, decision 26). Reaches: R3m.
    #[test]
    fn a_chain_of_inherited_entries_agrees() {
        let program = compile(MUTUAL.to_string());
        let plan = Plan::new(Tier::Expand, OBJECTS);
        for ops in [&CHAIN_KEPT[..], &CHAIN_CLEANED[..]] {
            compare(0, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
    }

    /// The cases of [`CELL_PROGRAM`]: two instances of an open row and two
    /// of a closed one; a promotion in each order and an instance after
    /// it; two closed rows that differ; a row closed by a unification and
    /// then asked for a mutable field; two copies of a generalized open
    /// row whose object is named twice.
    const CELL_CASES: [&[Op]; 6] = [
        &[Op::Instance(0), Op::Instance(0), Op::Instance(1), Op::Instance(1)],
        &[Op::Instance(0), Op::Instance(2), Op::Unify(0, 1), Op::Instance(0)],
        &[Op::Instance(2), Op::Instance(0), Op::Unify(0, 1)],
        &[Op::Instance(1), Op::Instance(3), Op::Unify(0, 1)],
        &[Op::Instance(1), Op::Instance(0), Op::Unify(0, 1), Op::Instance(2), Op::Unify(0, 2)],
        &[
            Op::Instance(4),
            Op::BeginDef,
            Op::Instance(4),
            Op::EndDef,
            Op::Generalize(1),
            Op::Copy(1),
            Op::Copy(1),
        ],
    ];

    /// What the old checker shows for mutability cells today (observed;
    /// section 8.6, decision 27). An instance of a scheme whose row ends in
    /// a generic variable has cells of its own (`^0 ^1`, then `^2 ^3`:
    /// `dup_mutability` when `row_terminator_generic`, compiler/ml/btype.ml:
    /// 462-506, 527-530); the instances of a closed row share the scheme's
    /// (`^4 ^5` twice). An immutable field of an open row unified with a
    /// mutable one is promoted (`x!`, compiler/ml/ctype.ml:2530-2532) in
    /// either order, and the scheme is untouched (the later instance has
    /// `x^3`, immutable). A closed immutable field against a mutable one is
    /// a clash (ctype.ml:2532, 2535), also when the row was closed by an
    /// earlier unification. A copy of a generalized open row duplicates
    /// once per copy, and the two names of one object in a copy are one
    /// node.
    #[test]
    fn old_checker_duplicates_the_cells_of_an_open_row() {
        let program = compile(CELL_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, OBJECTS | CELLS);
        let old = |case: usize| run_old(&program, plan, CELL_CASES[case]);
        assert_eq!(
            old(0).form,
            "0 = &0[0]fn(&1[0]obj{&2[0]a^0: &3[0]poly(&4[0]int;); &5[0]x^1: &6[0]poly(&7[0]int;); &8[0]'}) => &9[0]unit\n\
             1 = &10[0]fn(&11[0]obj{&12[0]a^2: &13[0]poly(&14[0]int;); &15[0]x^3: &16[0]poly(&17[0]int;); &18[0]'}) => &19[0]unit\n\
             2 = &20[0]fn(&21[0]obj{&22[0]a^4: &23[0]poly(&24[0]int;); &25[0]x^5: &26[0]poly(&27[0]int;); &28[0]nil}) => &29[0]unit\n\
             3 = &30[0]fn(&31[0]obj{&32[0]a^4: &33[0]poly(&34[0]int;); &35[0]x^5: &36[0]poly(&37[0]int;); &38[0]nil}) => &39[0]unit\n"
        );
        assert_eq!(
            old(1).form,
            "0 = &0[0]fn(&1[0]obj{&2[0]a^0: &3[0]poly(&4[0]int;); &5[0]x!^1: &6[0]poly(&7[0]int;); &8[0]'}) => &9[0]unit\n\
             1 = @0\n\
             2 = &10[0]fn(&11[0]obj{&12[0]a^2: &13[0]poly(&14[0]int;); &15[0]x^3: &16[0]poly(&17[0]int;); &18[0]'}) => &19[0]unit\n"
        );
        assert_eq!(
            old(2).form,
            "0 = &0[0]fn(&1[0]obj{&2[0]a^0: &3[0]poly(&4[0]int;); &5[0]x!^1: &6[0]poly(&7[0]int;); &8[0]'}) => &9[0]unit\n\
             1 = @0\n"
        );
        assert_eq!(old(3).failed, Some(2));
        assert_eq!(old(4).failed, Some(4));
        let copies = old(5).form;
        assert!(copies.contains("2 = &20[0]fn(&21[0]obj{&22[0]a^4:") && copies.contains("}, @21)"), "{copies}");
        assert!(copies.contains("3 = &30[0]fn(&31[0]obj{&32[0]a^6:") && copies.contains("}, @31)"), "{copies}");
    }

    /// The new side shares where the old side duplicates, until R3e: with
    /// cell classes printed, the kernel tier differs on generated cases
    /// (observed: 2,877 of 10,000 at 100 programs by 100 sequences; this
    /// test runs 10 by 100). So the classes are compared, and a new side
    /// without the duplicate is seen.
    #[test]
    fn cell_classes_show_a_missing_duplicate() {
        let (coverage, mismatches) = run_plan(Plan::new(Tier::Kernel, OBJECTS | CELLS), 1, 10, 100);
        assert_eq!(coverage.cases + mismatches.len(), 1_000);
        assert!(mismatches.len() >= 100, "{}", mismatches.len());
    }

    /// The cases of [`CELL_CASES`] on both sides: the duplicate of an
    /// instance and of a copy, the promotion, the clash of a closed row.
    /// Reaches: R3m, R3e.
    #[test]
    fn cells_agree_on_fixed_cases() {
        let program = compile(CELL_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, OBJECTS | CELLS);
        for (index, ops) in CELL_CASES.into_iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
        let plan = Plan::new(Tier::Full, OBJECTS | CELLS | EXPLAIN);
        for (index, ops) in CELL_CASES.into_iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
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
        for with in [OBJECTS, VARIANTS, OBJECTS | CELLS] {
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

    /// 10,000 cases of everything on programs with objects, with mutable
    /// fields and the classes of cells compared, and 10,000 more with made
    /// nodes: the acceptance test of R3e. A case that differs is read
    /// against the OCaml arm before either side is followed (decision 18).
    ///
    /// No seed is pinned. 31000122, 31000191 and 77000306 (and 77000265
    /// with BUILD) were one departure of the old checker (E4), now fixed:
    /// unify3 links the expanded head it chose to the ORIGINAL other side
    /// before the children (`occur !env t1' t2'; link_type t1' t2`,
    /// compiler/ml/ctype.ml:2330-2331), and the old checker's
    /// `unify_after_expansion` (types/ctype.rs) linked the two expanded
    /// heads to each other instead whenever the abbreviation expands to its
    /// own argument (`type id<'a> = 'a`). It now follows OCaml's order, so
    /// both lists are empty (decision 20: a list only ever shrinks).
    /// Reaches: R3m, R3e.
    #[test]
    fn object_plan_agrees_on_generated_cases() {
        let known: [u64; 0] = [];
        let coverage = run_cases_except(Plan::new(Tier::Full, OBJECTS | CELLS), &known);
        // `cases` counts the cases that agree: the pinned ones are not in it.
        assert_eq!(coverage.cases + known.len(), 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        run_cases_except(Plan::new(Tier::Full, OBJECTS | CELLS | BUILD), &[]);
        run_cases(Plan::new(Tier::Full, OBJECTS | CELLS | EXPLAIN), 1, 20, 100);
    }

    /// The program of the reference cases: a row whose two tags are
    /// `Reither` (`a`), an open row with one of them present (`g`), a
    /// closed row without it (`c`), and the first two again beside a
    /// component that clashes (`h`, `k`).
    const REF_PROGRAM: &str = "external a: [< #A(int) | #B] => unit = \"a\"\n\
        external g: [> #A(int)] => unit = \"g\"\n\
        external c: [#B] => unit = \"c\"\n\
        external h: ([< #A(int) | #B], int) => unit = \"h\"\n\
        external k: ([> #A(int)], string) => unit = \"k\"\n";

    /// The cases of [`REF_PROGRAM`]. An annotation's type is an instance
    /// made one definition deep and then `generalize_structure`d: its row
    /// is generic and its row variable is not.
    const ANNOTATION: [Op; 6] = [
        Op::BeginDef,
        Op::Instance(0),
        Op::EndDef,
        Op::GeneralizeStructure(0),
        Op::Copy(0),
        Op::Copy(0),
    ];
    const GENERALIZED: [Op; 6] = [
        Op::BeginDef,
        Op::Instance(0),
        Op::EndDef,
        Op::Generalize(0),
        Op::Copy(0),
        Op::Copy(0),
    ];

    /// O(1): `ops` followed by `more`.
    fn then(ops: &[Op], more: &[Op]) -> Vec<Op> {
        [ops, more].concat()
    }

    /// What the old checker shows for the references of `Reither` fields
    /// today (observed; section 8.6, decision 34). Two instances of a
    /// scheme have references of their own (`^0 ^1`, then `^2 ^3`), and so
    /// have two copies of a generalized type: `let e = if keep then e else
    /// ref None` with `keep = more.level <> generic_level`
    /// (compiler/ml/btype.ml:374, ctype.ml:806). Two copies of an
    /// annotation's type share the references of the type they copy, and
    /// its row variable (`@3`); each has its own copy of the argument type.
    #[test]
    fn old_checker_shares_the_references_of_an_annotation() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS);
        let old = |ops: &[Op]| run_old(&program, plan, ops).form;
        assert_eq!(
            old(&[Op::Instance(0), Op::Instance(0)]),
            "0 = &0[0]fn(&1[0][closed #A?^0(&2[0]int ) #B?c^1() | &3[0]']) => &4[0]unit\n\
             1 = &5[0]fn(&6[0][closed #A?^2(&7[0]int ) #B?c^3() | &8[0]']) => &9[0]unit\n"
        );
        assert_eq!(
            old(&ANNOTATION),
            "0 = &0[G]fn(&1[G][closed #A?^0(&2[G]int ) #B?c^1() | &3[0]']) => &4[G]unit\n\
             1 = &5[0]fn(&6[0][closed #A?^0(&7[0]int ) #B?c^1() | @3]) => &8[0]unit\n\
             2 = &9[0]fn(&10[0][closed #A?^0(&11[0]int ) #B?c^1() | @3]) => &12[0]unit\n"
        );
        assert_eq!(
            old(&GENERALIZED),
            "0 = &0[G]fn(&1[G][closed #A?^0(&2[G]int ) #B?c^1() | &3[G]']) => &4[G]unit\n\
             1 = &5[0]fn(&6[0][closed #A?^2(&7[0]int ) #B?c^3() | &8[0]']) => &9[0]unit\n\
             2 = &10[0]fn(&11[0][closed #A?^4(&12[0]int ) #B?c^5() | &13[0]']) => &14[0]unit\n"
        );
    }

    /// A resolution is seen by every holder of the reference (observed).
    /// One copy of the annotation's type is unified with `[> #A(int)]`:
    /// `Reither (false, tl, _, e1), Rpresent (Some t2)` sets `e1`
    /// (compiler/ml/ctype.ml:2711-2713), and the type itself and its other
    /// copy have `#A` present too, each with its *own* argument
    /// (`Rpresent (Some (List.hd tl))`, btype.ml:117: nodes 2, 7 and 11).
    /// With copies of a generalized type only the copy that was unified
    /// changes. Unified with the closed `[#B]`, `#A` is absent for every
    /// holder (`filter_row_fields`, ctype.ml:388-397), `#B` is present
    /// (ctype.ml:2726-2727) and the row variable all three share is `Tnil`
    /// (the static row, ctype.ml:2634-2636). A copy taken after the
    /// resolution has the resolved field and shares what is left (`^0`).
    #[test]
    fn old_checker_resolves_a_shared_reference_for_every_holder() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS);
        let old = |ops: &[Op]| run_old(&program, plan, ops).form;
        assert_eq!(
            old(&then(&ANNOTATION, &[Op::Instance(1), Op::Unify(1, 3)])),
            "0 = &0[G]fn(&1[G][closed #A(&2[G]int) #B?c^0() | &3[0]']) => &4[G]unit\n\
             1 = &5[0]fn(&6[0][closed #A(&7[0]int) #B?c^0() | @3]) => &8[0]unit\n\
             2 = &9[0]fn(&10[0][closed #A(&11[0]int) #B?c^0() | @3]) => &12[0]unit\n\
             3 = @5\n"
        );
        assert_eq!(
            old(&then(&GENERALIZED, &[Op::Instance(1), Op::Unify(1, 3)])),
            "0 = &0[G]fn(&1[G][closed #A?^0(&2[G]int ) #B?c^1() | &3[G]']) => &4[G]unit\n\
             1 = &5[0]fn(&6[0][closed #A(&7[0]int) #B?c^2() | &8[0]']) => &9[0]unit\n\
             2 = &10[0]fn(&11[0][closed #A?^3(&12[0]int ) #B?c^4() | &13[0]']) => &14[0]unit\n\
             3 = @5\n"
        );
        assert_eq!(
            old(&then(&ANNOTATION, &[Op::Instance(2), Op::Unify(1, 3)])),
            "0 = &0[G]fn(&1[G][closed #A- #B | &2[0]nil]) => &3[G]unit\n\
             1 = &4[0]fn(&5[0][closed #B | @2]) => &6[0]unit\n\
             2 = &7[0]fn(&8[0][closed #A- #B | @2]) => &9[0]unit\n\
             3 = @4\n"
        );
        let after = old(&[
            Op::BeginDef,
            Op::Instance(0),
            Op::EndDef,
            Op::GeneralizeStructure(0),
            Op::Copy(0),
            Op::Instance(1),
            Op::Unify(1, 2),
            Op::Copy(0),
        ]);
        assert!(
            after.ends_with("3 = &9[0]fn(&10[0][closed #A(&11[0]int) #B?c^0() | @3]) => &12[0]unit\n"),
            "{after}"
        );
    }

    /// A failed unification leaves what it resolved (observed, in the
    /// explaining mode): the two rows are unified before the second
    /// components clash, and afterwards `#A` is present and the two
    /// operands hold one row node. `set_row_field` logs `Crow`
    /// (compiler/ml/btype.ml:742-744) and a failure undoes path compression
    /// only (btype.ml:792-800); the descriptor put back is the arrow's
    /// (`t1'.desc <- d1`, ctype.ml:2437), not the row's.
    #[test]
    fn old_checker_keeps_a_resolution_after_a_failed_unification() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS | EXPLAIN);
        let old = run_old(&program, plan, &[Op::Instance(3), Op::Instance(4), Op::Unify(0, 1)]);
        assert_eq!(old.failed, Some(2));
        assert!(
            old.form.ends_with(
                "0 = &0[0]fn(&1[0][closed #A(&2[0]int) #B?c^0() | &3[0]'], &4[0]int) => &5[0]unit\n\
                 1 = &6[0]fn(@1, &7[0]string) => &8[0]unit\n"
            ),
            "{}",
            old.form
        );
    }

    /// A field resolved to `Rabsent` is no longer a parent of its types
    /// (`iter_row`, compiler/ml/btype.ml:229-236, visits what
    /// `row_field_repr` gives), also for a holder the unification did not
    /// touch (observed). The annotation `([< #A('a) | #B], 'a) => unit`
    /// is copied twice two definitions deep; the row of the first copy is
    /// unified with `[#B]`; the row of the second copy is then lowered to
    /// the starting level. It comes down (`&9[0]`) and the variable its
    /// `#A` named stays where it was (`&3[1]`).
    #[test]
    fn old_checker_does_not_reach_the_types_of_an_absent_field() {
        let program = compile(
            "external p: ([< #A('a) | #B], 'a) => unit = \"p\"\n\
             external c: [#B] => unit = \"c\"\n"
                .to_string(),
        );
        let ops = [
            Op::BeginDef,
            Op::BeginDef,
            Op::Instance(0),
            Op::EndDef,
            Op::GeneralizeStructure(0),
            Op::Copy(0),
            Op::Copy(0),
            Op::Child(1, 0),
            Op::Instance(1),
            Op::Child(4, 0),
            Op::Unify(3, 5),
            Op::Child(2, 0),
            Op::Lower(6, 0),
        ];
        let old = run_old(&program, Plan::new(Tier::Full, VARIANTS | REFS), &ops);
        assert_eq!(
            old.form,
            "0 = &0[G]fn(&1[G][closed #A- #B | &2[0]nil], &3[1]') => &4[G]unit\n\
             1 = &5[1]fn(&6[1][closed #B | @2], @3) => &7[1]unit\n\
             2 = &8[1]fn(&9[0][closed #A- #B | @2], @3) => &10[1]unit\n\
             3 = @6\n\
             4 = &11[1]fn(@6) => &12[1]unit\n\
             5 = @6\n\
             6 = @9\n"
        );
    }

    /// The classes are compared: the kernel tier's copy is R1's, which
    /// knows no reference, so a field of a node it copies has a class of
    /// its own. It agrees where the old checker makes new references (two
    /// instances, two copies of a generalized type) and differs where the
    /// old checker shares them (two copies of an annotation's type), on
    /// the fixed case and on generated ones (observed: 70 of 10,000).
    #[test]
    fn reference_classes_show_a_missing_share() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Kernel, VARIANTS | REFS);
        compare(1, &program, plan, &[Op::Instance(0), Op::Instance(0)], Fault::None)
            .unwrap_or_else(|e| panic!("{e}"));
        compare(2, &program, plan, &GENERALIZED, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        let report = compare(3, &program, plan, &ANNOTATION, Fault::None)
            .expect_err("a copy without the shared references must be seen");
        assert!(report.contains("seed 3") && report.contains("#A?^2("), "{report}");
        let (coverage, mismatches) = run_plan(plan, 1, 100, 100);
        assert_eq!(coverage.cases + mismatches.len(), 10_000);
        assert!(mismatches.len() >= 20, "{}", mismatches.len());
    }

    /// The fixed cases of [`REF_PROGRAM`] that make no copy, on both
    /// sides, with the classes of references printed: a `Reither` row
    /// against an open row with one of its tags present, in both orders;
    /// against a closed row without it; against another instance of
    /// itself; and, in the explaining mode, the rows unified before a
    /// later component clashes, in both orders.
    /// Reaches: R3m, R3f.
    #[test]
    fn variant_rows_agree_on_fixed_cases() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS);
        let cases: [&[Op]; 5] = [
            &[Op::Instance(0), Op::Instance(1), Op::Unify(0, 1), Op::Instance(0)],
            &[Op::Instance(1), Op::Instance(0), Op::Unify(0, 1)],
            &[Op::Instance(0), Op::Instance(2), Op::Unify(0, 1)],
            &[Op::Instance(0), Op::Instance(0), Op::Unify(0, 1)],
            &[Op::Instance(2), Op::Instance(1), Op::Unify(0, 1)],
        ];
        for (index, ops) in cases.into_iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
        let plan = Plan::new(Tier::Full, VARIANTS | REFS | EXPLAIN);
        for (index, ops) in [[3, 4], [4, 3]].into_iter().enumerate() {
            let ops = [Op::Instance(ops[0]), Op::Instance(ops[1]), Op::Unify(0, 1)];
            compare(10 + index as u64, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
    }

    /// The copies of an annotation's type and of a generalized type on
    /// both sides (the cases of `old_checker_shares_the_references_of_an_
    /// annotation` and `old_checker_resolves_a_shared_reference_for_every_
    /// holder`), then 10,000 cases of everything on programs with
    /// variants, with the classes of references compared, and 10,000 with
    /// objects and made nodes too: the acceptance test of R3f and R3n
    /// together. A generated case copies rows, so it needs both. A case
    /// that differs is read against the OCaml arm before either side is
    /// followed (decision 18); a seed where the old checker departs from
    /// ctype.ml is pinned with `run_cases_except` and its cause by the
    /// reviewer, not by the builder.
    /// Reaches: R3m, R3e, R3f, R3n.
    #[test]
    fn variant_plan_agrees_on_generated_cases() {
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS);
        let cases: [Vec<Op>; 6] = [
            ANNOTATION.to_vec(),
            GENERALIZED.to_vec(),
            then(&ANNOTATION, &[Op::Instance(1), Op::Unify(1, 3)]),
            then(&GENERALIZED, &[Op::Instance(1), Op::Unify(1, 3)]),
            then(&ANNOTATION, &[Op::Instance(2), Op::Unify(1, 3)]),
            then(&ANNOTATION, &[Op::Instance(1), Op::Unify(1, 3), Op::Copy(0), Op::Copy(1)]),
        ];
        for (index, ops) in cases.iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
        let coverage = run_cases(plan, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        run_cases(Plan::new(Tier::Full, OBJECTS | VARIANTS | REFS | BUILD), 1, 100, 100);
        run_cases(Plan::new(Tier::Full, VARIANTS | REFS | EXPLAIN), 1, 20, 100);
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
        let before: [(&str, &[&str]); 13] = [
            ("R3s", &["R3m", "R3e", "R3f", "R3n", "R3g", "R3h", "R3r", "R3q"]),
            ("R3q", &["R3m", "R3e", "R3f", "R3n", "R3g", "R3h", "R3r"]),
            ("R3r", &["R3m", "R3e", "R3f", "R3n", "R3g", "R3h"]),
            ("R3p", &["R3m", "R3e"]),
            ("R3k", &[]),
            ("R3m", &[]),
            ("R3e", &["R3m"]),
            ("R3f", &["R3m", "R3e"]),
            ("R3n", &["R3m", "R3e", "R3f"]),
            ("R3g", &["R3m", "R3e", "R3f", "R3n"]),
            ("R3h", &["R3m", "R3e", "R3f", "R3n", "R3g"]),
            ("R3i", &["R3m", "R3e", "R3f", "R3n", "R3g", "R3p", "R3h", "R3r", "R3q", "R3s"]),
            ("R3j", &["R3m", "R3e", "R3f", "R3n", "R3g", "R3p", "R3h", "R3r", "R3q", "R3s", "R3i"]),
        ];
        // Method name -> slice, from the bodies that are still `todo!`.
        fn scan(source: &str, methods: &mut Vec<(String, String)>) {
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
        // The scanner is checked on a body of its own and not on a method
        // of a slice: every slice removes its own `todo!`.
        let mut sample = Vec::new();
        scan("    pub fn sample<T>(&self) -> T {\n        todo!(\"R3z\")\n    }", &mut sample);
        assert_eq!(sample, [("sample".to_string(), "R3z".to_string())]);
        let mut methods: Vec<(String, String)> = Vec::new();
        for source in [
            include_str!("rows.rs"),
            include_str!("relate.rs"),
            include_str!("unify.rs"),
            include_str!("expand.rs"),
        ] {
            scan(source, &mut methods);
        }
        // Every ignored test of the two files is checked: an `ignore` that
        // does not name its slice as "R3x build" is not skipped silently.
        // The number itself is not pinned: each slice removes its own.
        let (mut checked, mut ignored) = (0, 0);
        for source in [include_str!("differential.rs"), include_str!("r3_tests.rs")] {
            let lines: Vec<&str> = source.lines().collect();
            for (at, line) in lines.iter().enumerate() {
                if line.trim_start().starts_with("#[ignore") {
                    ignored += 1;
                }
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
                for (needle, reached) in [
                    ("OBJECTS", "R3e"),
                    ("VARIANTS", "R3f"),
                    ("UNIVAR", "R3g"),
                    ("PATTERN", "R3h"),
                ] {
                    if full && body.contains(needle) {
                        reaches.push(reached);
                    }
                }
                if rows && (full || body.contains("Tier::Expand")) {
                    reaches.push("R3m");
                }
                // A copy of a row is R3n's: a generated case (every plan
                // draws `Op::Copy`), or a fixed one that copies.
                if full
                    && body.contains("VARIANTS")
                    && ["run_cases", "Op::Copy", "ANNOTATION", "GENERALIZED"]
                        .iter()
                        .any(|needle| body.contains(needle))
                {
                    reaches.push("R3n");
                }
                // A hand-built variant row reaches R3f.
                if ["variant_at(", "tag_pair("].iter().any(|needle| body.contains(needle)) {
                    reaches.push("R3f");
                }
                // A hand-built test: a type marked INHERITS, or the marks
                // themselves, is R3m's.
                if body.contains("inheriting(") || body.contains("INHERITS") {
                    reaches.push("R3m");
                }
                // A hand-built object (`obj(`, a field, a scheme of one)
                // reaches R3e.
                if ["obj(", "field_at(", "object_scheme(", "instance_open("]
                    .iter()
                    .any(|needle| body.contains(needle))
                {
                    reaches.push("R3e");
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
        assert_eq!(checked, ignored, "an ignored R3 test does not name its slice");
    }

    /// A mutability cell shared under an annotation (section 8.6, decision
    /// 48; observed). `generalize_structure` leaves the row variable of an
    /// open row below its generic fields (`&8[0]'`), so the row's last
    /// node is not generic and a copy shares the cells
    /// (`row_terminator_generic`, compiler/ml/btype.ml:478-506; `^0 ^1`
    /// three times). One copy unified with a row whose `x` is mutable
    /// promotes the one class (compiler/ml/ctype.ml:2530-2532): the
    /// annotation and the other copy have `x!` too. Both sides agree
    /// today, in both modes.
    #[test]
    fn old_checker_shares_the_cells_of_an_annotation() {
        let program = compile(CELL_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, OBJECTS | CELLS);
        let ops = [
            Op::BeginDef,
            Op::Instance(0),
            Op::EndDef,
            Op::GeneralizeStructure(0),
            Op::Copy(0),
            Op::Copy(0),
            Op::Instance(2),
            Op::Unify(1, 3),
        ];
        assert_eq!(
            run_old(&program, plan, &ops).form,
            "0 = &0[G]fn(&1[G]obj{&2[G]a^0: &3[G]poly(&4[G]int;); &5[G]x!^1: &6[G]poly(&7[G]int;); &8[0]'}) => &9[G]unit\n\
             1 = &10[0]fn(&11[0]obj{&12[0]a^0: &13[0]poly(&14[0]int;); &15[0]x!^1: &16[0]poly(&17[0]int;); @8}) => &18[0]unit\n\
             2 = &19[0]fn(&20[0]obj{&21[0]a^0: &22[0]poly(&23[0]int;); &24[0]x!^1: &25[0]poly(&26[0]int;); @8}) => &27[0]unit\n\
             3 = @10\n"
        );
        compare(0, &program, plan, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        let explain = Plan::new(Tier::Full, OBJECTS | CELLS | EXPLAIN);
        compare(1, &program, explain, &ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        // The generated cases of the object plan make such an annotation
        // and copy it: some seed of the first 300 draws the three
        // operations in that order on one operand.
        let reached = (0..300u64).any(|sequence| {
            let (_, ops) = case(plan, 1_000_003 + sequence);
            ops.windows(3).any(|w| {
                matches!(w, [Op::GeneralizeStructure(a), Op::Copy(b), Op::Copy(c)] if a == b && b == c)
            })
        });
        assert!(reached, "no generated case copies an annotation twice");
    }

    /// The fixed-row rule of `copy_row` on the old checker (section 8.6,
    /// decision 47; observed). The row is built by hand: closed, `row_fixed`,
    /// two `Reither` fields that are not matched. `Ctype.copy` passes
    /// `fixed = true` (`copy_row copy true row keep more'`,
    /// compiler/ml/ctype.ml:868), so each copied field is matched
    /// (`let m = if row.row_fixed then fixed else m`, compiler/ml/btype.ml:
    /// 375: `?m`, `?cm`) and the copy stays fixed (`row_fixed =
    /// row.row_fixed && fixed`, btype.ml:389). With a generic row variable
    /// the copy has references of its own (`^2 ^3`); with one that is not
    /// generic it shares the source's (`^0 ^1`, `keep`, btype.ml:374) and
    /// the source's own fields stay unmatched.
    #[test]
    fn old_checker_matches_the_fields_of_a_fixed_row_it_copies() {
        use crate::types::type_expr::{RowDesc, RowField};
        let program = compile(REF_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, VARIANTS | REFS);
        let old = old_context(&program, plan);
        let ctx = &old.ctx;
        let mut forms = Vec::new();
        for generic in [true, false] {
            let more = if generic {
                ctx.new_generic_var(None)
            } else {
                ctx.new_var(None)
            };
            let either = |constant: bool, types: Vec<TypeExprRef>| RowField::Reither {
                constant,
                types,
                matched: false,
                link: ctx.alloc_row_field(None),
            };
            let fields = vec![
                ("A".into(), either(false, vec![ctx.new_generic_var(None)])),
                ("B".into(), either(true, Vec::new())),
            ];
            let row = ctx.new_generic_type(TypeDesc::Tvariant(ctx.new_row_desc(RowDesc {
                row_fields: fields.into(),
                row_more: more,
                row_closed: true,
                row_fixed: true,
                row_name: None,
            })));
            let copy = ctype::instance(ctx, row);
            forms.push(old_forms(&old, plan, &[row, copy], &[]).0);
        }
        assert_eq!(
            forms[0],
            "0 = &0[G][closed fixed #A?^0(&1[G]' ) #B?c^1() | &2[G]']\n\
             1 = &3[0][closed fixed #A?m^2(&4[0]' ) #B?cm^3() | &5[0]']\n"
        );
        assert_eq!(
            forms[1],
            "0 = &0[G][closed fixed #A?^0(&1[G]' ) #B?c^1() | &2[0]']\n\
             1 = &3[0][closed fixed #A?m^0(&4[0]' ) #B?cm^1() | @2]\n"
        );
    }

    /// O(text): whether a form prints a row that a copy reads as fixed
    /// with a `Reither` field that is not matched (`#A?^`, `#A?c^`,
    /// `#A?(`, `#A?c(`): a row printed `[fixed ...]` or `[closed fixed
    /// ...]`, or a row over a constructor, which a copy makes fixed
    /// (PR#6163, compiler/ml/ctype.ml:826-830: `| {desc = Tconstr _} when
    /// not row.row_fixed -> {row with row_fixed = true}`). The tail of a
    /// row is what follows `| `: a node printed in full (`&7[1]` and its
    /// form) or a reference to one printed before (`@7`). A tail is a
    /// constructor when its form is none of the three others a row can
    /// end in (`'` a variable, `!` a universal variable, `nil`:
    /// `row_fixed`, btype.ml:153-160).
    fn fixed_row_with_an_unmatched_field(form: &str) -> bool {
        let bytes = form.as_bytes();
        // Per printed node, whether its form is a constructor's.
        let mut constructors: Vec<bool> = Vec::new();
        let is_constructor = |rest: &str| !(rest.starts_with('\'') || rest.starts_with('!') || rest.starts_with("nil"));
        // Per open bracket: (a fixed row, a row with an unmatched field).
        let mut open: Vec<(bool, bool)> = Vec::new();
        for (at, &byte) in bytes.iter().enumerate() {
            match byte {
                b'&' => {
                    let digits = form[at + 1..].bytes().take_while(u8::is_ascii_digit).count();
                    let number: usize = form[at + 1..at + 1 + digits].parse().unwrap();
                    let rest = &form[at + 1 + digits..];
                    let rest = &rest[rest.find(']').map_or(0, |close| close + 1)..];
                    if constructors.len() <= number {
                        constructors.resize(number + 1, false);
                    }
                    constructors[number] = is_constructor(rest);
                }
                b'[' => {
                    let rest = &form[at + 1..];
                    open.push((rest.starts_with("fixed ") || rest.starts_with("closed fixed "), false));
                }
                b']' => {
                    open.pop();
                }
                b'?' => {
                    let rest = form[at + 1..].trim_start_matches('c');
                    if rest.starts_with('^') || rest.starts_with('(') {
                        match open.last_mut() {
                            Some((true, _)) => return true,
                            Some((false, unmatched)) => *unmatched = true,
                            None => {}
                        }
                    }
                }
                b'|' if open.last() == Some(&(false, true)) && form[at..].starts_with("| ") => {
                    let rest = &form[at + 2..];
                    let over_constructor = match rest.as_bytes().first() {
                        Some(b'@') => {
                            let digits = rest[1..].bytes().take_while(u8::is_ascii_digit).count();
                            let number: usize = rest[1..1 + digits].parse().unwrap();
                            constructors.get(number) == Some(&true)
                        }
                        Some(b'&') => {
                            let rest = &rest[rest.find(']').map_or(0, |close| close + 1)..];
                            is_constructor(rest)
                        }
                        _ => false,
                    };
                    if over_constructor {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// What would notice that the fixed-row rule of `copy_row` became
    /// reachable (section 8.6, decision 47): no generated case of the
    /// plans with variants and universal variables prints, on the old
    /// side, a fixed row with a `Reither` field that is not matched; so no
    /// copy of such a case can change a field's `m`. A row is fixed with
    /// such a field only after `reify` (compiler/ml/ctype.ml:1841-1855,
    /// R3h) or `rigidify` (ctype.ml:3139-3147, R3i), or when `instance_poly
    /// ~fixed:false` copies it (ctype.ml:1061-1069). The scanner is
    /// checked on the hand-built row of the test above. Observed: 546 of
    /// the 4,000 cases print a fixed row.
    ///
    /// A row over a constructor is watched too (eighth skeleton turn;
    /// the first of "Corrections after the review of the seventh turn",
    /// item 5): `copy_refs` reads it as fixed (PR#6163, ctype.ml:826-830)
    /// whatever its flag, so such a row with an unmatched field would
    /// reach `match_unmatched` from a plan without patterns. The scanner
    /// is checked on four hand-written forms: a row over a constructor
    /// printed in full and one printed as a reference, each with an
    /// unmatched field (found), and the same rows over a variable and
    /// with matched fields (not found).
    #[test]
    fn no_generated_case_has_a_fixed_row_with_an_unmatched_field() {
        assert!(fixed_row_with_an_unmatched_field(
            "0 = &0[G][closed fixed #A?^0(&1[G]' ) #B?c^1() | &2[G]']\n"
        ));
        assert!(fixed_row_with_an_unmatched_field("0 = &0[1][#A?^0(&1[1]' ) | &2[1]n0]\n"));
        assert!(fixed_row_with_an_unmatched_field(
            "0 = &0[1]n0\n1 = &1[1][closed #A?c^0() | @0]\n"
        ));
        assert!(!fixed_row_with_an_unmatched_field(
            "0 = &0[1]'\n1 = &1[1][closed #A?c^0() | @0] &2[1][#A?^1() | &3[1]nil] &4[1][#A?^2() | &5[G]!a]\n"
        ));
        assert!(!fixed_row_with_an_unmatched_field("0 = &0[1][#A?m^0(&1[1]' ) #B | &2[1]n0]\n"));
        assert!(!fixed_row_with_an_unmatched_field(
            "1 = &3[0][closed fixed #A?m^2(&4[0]' ) #B?cm^3() | &5[0]'] &6[0][closed #A?^4() | &7[0]']\n"
        ));
        let mut fixed_rows = 0;
        for with in [VARIANTS | REFS, OBJECTS | VARIANTS | REFS | UNIVARS] {
            let plan = Plan::new(Tier::Full, with);
            for seed in 1..=20u64 {
                for sequence in 0..100u64 {
                    let (program, ops) = case(plan, seed * 1_000_003 + sequence);
                    let form = run_old(&program, plan, &ops).form;
                    assert!(
                        !fixed_row_with_an_unmatched_field(&form),
                        "seed {}\n{}{form}",
                        seed * 1_000_003 + sequence,
                        program.source
                    );
                    fixed_rows += usize::from(form.contains("fixed "));
                }
            }
        }
        // Not vacuous: the cases do print fixed rows.
        println!("fixed rows: {fixed_rows}");
        assert!(fixed_rows >= 50, "{fixed_rows}");
    }

    /// The program of the fixed cases with universal variables: one bound
    /// variable under two names (`v0`, `v1`), two in each order and with
    /// each as the result (`v2`, `v3`, `v4`), a binder inside a binder
    /// whose body names the outer variable (`v5`, `v6`), a row whose row
    /// variable is bound (`v7` open, `v8` with two `Reither` tags), and an
    /// arrow without any (`v9`).
    const UNIVAR_PROGRAM: &str = "external v0: {\"f\": 'a. 'a => 'a} => unit = \"v0\"\n\
        external v1: {\"f\": 'b. 'b => 'b} => unit = \"v1\"\n\
        external v2: {\"f\": 'a 'b. ('a, 'b) => 'a} => unit = \"v2\"\n\
        external v3: {\"f\": 'b 'a. ('b, 'a) => 'b} => unit = \"v3\"\n\
        external v4: {\"f\": 'a 'b. ('a, 'b) => 'b} => unit = \"v4\"\n\
        external v5: {\"f\": 'a. {\"g\": 'b. ('a, 'b) => 'a}} => unit = \"v5\"\n\
        external v6: {\"f\": 'a. {\"g\": 'b. ('b, 'a) => 'b}} => unit = \"v6\"\n\
        external v7: {\"f\": 'a. ([> #A(int)] as 'a) => 'a} => unit = \"v7\"\n\
        external v8: {\"f\": 'a. ([< #A(int) | #B] as 'a) => 'a} => unit = \"v8\"\n\
        external v9: 'a => 'a = \"v9\"\n";

    /// The plan of the fixed cases with universal variables.
    const UNIVAR_PLAN: u16 = OBJECTS | VARIANTS | REFS | UNIVARS;

    /// O(text): the pairs of the trace of failed operation `index` of an
    /// [`EXPLAIN`] form.
    fn trace_of(form: &str, index: usize) -> Vec<&str> {
        let header = format!("! {index} trace");
        form.lines()
            .skip_while(|line| *line != header)
            .skip(1)
            .take_while(|line| line.starts_with("  "))
            .map(str::trim)
            .collect()
    }

    /// Two instances of the values `left` and `right`, unified.
    fn two(left: u16, right: u16) -> [Op; 3] {
        [Op::Instance(left), Op::Instance(right), Op::Unify(0, 1)]
    }

    /// Hand-made polymorphic types of [`UNIVAR_PROGRAM`] whose inner
    /// binder is already known when `enter_poly` meets it. Left: a
    /// universal variable `u` (operand 0), `inner = poly((u, second); u)`
    /// (3), `outer = poly(inner; u)` (4): `u` is bound twice. Right: `u'`
    /// (5), `w'` (6), `inner' = poly((first, second'); w')` (8), `outer' =
    /// poly(inner'; u')` (9). Operand 1 is an arrow, for a body that
    /// clashes. Then `outer` is unified with `outer'`.
    fn known_binder(left_second: u16, right: [u16; 2]) -> [Op; 11] {
        [
            Op::Univar,
            Op::Instance(9),
            Op::Tuple(0, left_second),
            Op::Poly(2, 0),
            Op::Poly(3, 0),
            Op::Univar,
            Op::Univar,
            Op::Tuple(right[0], right[1]),
            Op::Poly(7, 6),
            Op::Poly(8, 5),
            Op::Unify(4, 9),
        ]
    }

    /// The self-test of [`UNIVARS`] (section 8.6, decision 49): the form
    /// prints the binder list in order and each universal variable as a
    /// node, so `v2` and `v3`, whose binders pair by position and not by
    /// name, print the names at the positions they have (observed), and
    /// the two sides agree today on what needs no unification: instances,
    /// copies, generalizations, a universal variable and a polymorphic
    /// type made by hand, the body of one as an operand.
    #[test]
    fn the_two_sides_agree_on_universal_variables() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        assert_eq!(program.values.len(), 10);
        let plan = Plan::new(Tier::Kernel, OBJECTS | VARIANTS | UNIVARS);
        let old = |value: u16| run_old(&program, plan, &[Op::Instance(value)]).form;
        assert_eq!(
            old(2),
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!a, &6[0]!b) => @5; @5 @6); &7[0]nil}) => &8[0]unit\n"
        );
        assert_eq!(
            old(3),
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!b, &6[0]!a) => @5; @5 @6); &7[0]nil}) => &8[0]unit\n"
        );
        // The row variable of `v7` is its bound variable (`@7` twice), and
        // such a row is fixed with matched fields (`make_fixed_univars`,
        // compiler/ml/typetexp.ml:677-703).
        assert_eq!(
            old(7),
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0][fixed #A(&6[0]int) | &7[0]!]) => @5; @7); &8[0]nil}) => &9[0]unit\n"
        );
        assert!(
            old(8).contains("[closed fixed #A?m(&6[0]int ) #B?cm() | &7[0]!]"),
            "{}",
            old(8)
        );
        for value in 0..10u16 {
            let ops = [
                Op::BeginDef,
                Op::Instance(value),
                Op::Instance(value),
                Op::EndDef,
                Op::Generalize(0),
                Op::Copy(0),
                Op::GeneralizeStructure(1),
                Op::Copy(1),
                Op::Univar,
                Op::Poly(2, 4),
                Op::Slot(0, 0),
                Op::Slot(6, 0),
                Op::Slot(7, 0),
                Op::Slot(8, 0),
                Op::Poly(9, 9),
                Op::Lower(5, 0),
            ];
            compare(u64::from(value), &program, plan, &ops, Fault::None)
                .unwrap_or_else(|e| panic!("{e}"));
        }
    }

    /// The deliberately wrong new side of [`UNIVARS`]: an instance whose
    /// polymorphic types have their first two bound variables in the other
    /// order is reported on the fixed case and by generated cases
    /// (observed: 819 of 1,000), so the order of a binder list is compared.
    #[test]
    fn a_swapped_binder_is_reported() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Kernel, OBJECTS | VARIANTS | UNIVARS);
        let report = compare(5, &program, plan, &[Op::Instance(2)], Fault::SwappedBinders)
            .expect_err("the swapped binders must be seen");
        assert!(
            report.contains("seed 5") && report.contains("; @6 @5)"),
            "{report}"
        );
        // One bound variable: nothing to swap, nothing reported.
        compare(6, &program, plan, &[Op::Instance(0)], Fault::SwappedBinders)
            .unwrap_or_else(|e| panic!("{e}"));
        let mut found = 0;
        for seed in 1..=10u64 {
            for sequence in 0..100u64 {
                let case_seed = seed * 1_000_003 + sequence;
                let (program, ops) = case(plan, case_seed);
                found += usize::from(
                    compare(case_seed, &program, plan, &ops, Fault::SwappedBinders).is_err(),
                );
            }
        }
        println!("swapped binders found: {found}");
        assert!(found >= 20, "{found}");
    }

    /// Instance, copy, generalize, lower and the hand-made nodes of
    /// [`UNIVARS`] on programs with polymorphic fields: 10,000 cases on
    /// what exists on both sides today.
    #[test]
    fn kernel_tier_agrees_on_universal_variables() {
        let coverage = run_cases(
            Plan::new(Tier::Kernel, OBJECTS | VARIANTS | UNIVARS),
            1,
            100,
            100,
        );
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.sharing * 4 > coverage.cases * 3, "{coverage:?}");
    }

    /// The old side of the plan with universal variables runs today and is
    /// not vacuous (observed, 1,200 cases: 978 without a failed
    /// unification and 222 with one; 821 print a universal variable, 299 a
    /// fixed row; in 238 a case that prints a universal variable unifies
    /// and nothing fails).
    #[test]
    fn old_side_of_the_univar_plan_is_not_vacuous() {
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN);
        let (mut ok, mut failed, mut bound, mut rows, mut unified) = (0, 0, 0, 0, 0);
        for seed in 1..=12u64 {
            for sequence in 0..100u64 {
                let (program, ops) = case(plan, seed * 1_000_003 + sequence);
                let outcome = run_old(&program, plan, &ops);
                match outcome.failed {
                    Some(_) => failed += 1,
                    None => ok += 1,
                }
                // A polymorphic type with a bound variable, and a row whose
                // row variable is a universal variable.
                let polymorphic = outcome.form.contains('!');
                bound += usize::from(polymorphic);
                rows += usize::from(outcome.form.contains("fixed "));
                unified += usize::from(
                    polymorphic
                        && outcome.failed.is_none()
                        && ops.iter().any(|op| matches!(op, Op::Unify(..))),
                );
            }
        }
        println!("univar plan, old side: {ok} {failed} {bound} {rows} {unified}");
        assert!(
            ok >= 500 && failed >= 200 && bound >= 300 && rows >= 20 && unified >= 100,
            "{ok} {failed} {bound} {rows} {unified}"
        );
    }

    /// Universal variables are paired by position in the binder lists,
    /// never by name (observed; `enter_poly` pairs `tl1` with `tl2` as
    /// lists, compiler/ml/ctype.ml:1670-1672, and `unify_univar` accepts a
    /// pair only when both are found in the two lists of one scope and are
    /// each other's partner or both free, ctype.ml:1544-1559). `'a. 'a =>
    /// 'a` unifies with `'b. 'b => 'b`, and `'a 'b. ('a, 'b) => 'a` with
    /// `'b 'a. ('b, 'a) => 'b`: the left variables are links to the right
    /// ones afterwards (`link_type t1 t2`, ctype.ml:2247). `'a 'b. ('a,
    /// 'b) => 'a` against `'a 'b. ('a, 'b) => 'b` fails at the result,
    /// where the first variable meets the second: the last pair of the
    /// trace is the two universal variables. A type of one variable
    /// against one of two fails at the bodies, an arrow of one parameter
    /// against one of two: two binder lists of different lengths with
    /// bodies that unify do not come from a program, because a variable
    /// its body does not name is not bound (`'a 'b. 'a => 'a` is `poly(fn(
    /// !a) => !a; !a)`, compiler/ml/typetexp.ml:563-568).
    #[test]
    fn old_checker_pairs_universal_variables_by_position() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
        let old = |ops: &[Op]| run_old(&program, plan, ops);
        assert_eq!(
            old(&two(0, 1)).form,
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!b) => @5; @5); &6[0]nil}) => &7[0]unit\n1 = @0\n"
        );
        assert_eq!(
            old(&two(2, 3)).form,
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!b, &6[0]!a) => @5; @5 @6); &7[0]nil}) => &8[0]unit\n1 = @0\n"
        );
        let clash = old(&two(2, 4));
        assert_eq!(clash.failed, Some(2));
        assert_eq!(
            trace_of(&clash.form, 2),
            [
                "@0 ~ @9",
                "@1 ~ @10",
                "&16[0]f: @3; &17[0]nil ~ &18[0]f: @12; &19[0]nil",
                "@3 ~ @12",
                "@4 ~ @13",
                "@5 ~ @6",
            ]
        );
        let lengths = old(&two(0, 2));
        assert_eq!(lengths.failed, Some(2));
        assert_eq!(trace_of(&lengths.form, 2).last(), Some(&"@4 ~ @12"));
    }

    /// What `unify_univar` answers for a variable bound in an outer scope
    /// (observed; compiler/ml/ctype.ml:1544-1559). The scopes are searched
    /// innermost first; a pair found in neither list of a scope goes on to
    /// the next (`None, None -> unify_univar t1 t2 rem`), so the outer
    /// variables of two instances of `v5` pair in the outer scope from
    /// inside the inner one. A variable of the outer scope against one the
    /// inner scope binds is refused at the inner scope (`| _ -> raise
    /// (Unify [])`: one found, the other not): `v5` against `v6`, at the
    /// first parameter, `!a` of the left against `!b` of the right.
    #[test]
    fn old_checker_searches_the_scopes_innermost_first() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
        let same = run_old(&program, plan, &two(5, 5));
        assert_eq!(
            same.form,
            "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]obj{&5[0]g: &6[0]poly(&7[0]fn(&8[0]!a, &9[0]!b) => @8; @9); &10[0]nil}; @8); &11[0]nil}) => &12[0]unit\n1 = @0\n"
        );
        let crossed = run_old(&program, plan, &two(5, 6));
        assert_eq!(crossed.failed, Some(2));
        let trace = trace_of(&crossed.form, 2);
        assert_eq!(trace.len(), 9, "{trace:?}");
        assert_eq!(trace[6..], ["@6 ~ @19", "@7 ~ @20", "@8 ~ @21"]);
        assert!(
            crossed
                .form
                .contains("&19[0]poly(&20[0]fn(&21[0]!b, &22[0]!a) => @21; @21)"),
            "{}",
            crossed.form
        );
    }

    /// The order question of `enter_poly` (section 8.6, decision 49;
    /// observed): the escape test comes BEFORE the scopes are pushed and
    /// before the bodies are unified (`if ... univars_escape ... then
    /// raise (Unify [])`, then `univar_pairs := ...`, then `f t1 t2`,
    /// compiler/ml/ctype.ml:1664-1674). In [`known_binder`] the left inner
    /// type binds `u` again, which the outer scope has paired with `u'`.
    /// - The right inner body names `u'`: the family of `u` (`u` and its
    ///   partner's list, ctype.ml:1612-1623) escapes. The trace is the two
    ///   outer types and the two inner types and nothing below them, and
    ///   the failure leaves the graph as it was.
    /// - The same with a left body that could not unify with the right
    ///   one (an arrow against `u'`): the same trace. A test after the
    ///   bodies would end at the pair of the arrow and `u'`.
    /// - The right inner body names only its own variable: no escape, the
    ///   bodies unify and `u` is a link to `w'`; `u'`, which no body
    ///   names, stays a node of its own.
    #[test]
    fn old_checker_tests_escape_before_the_bodies() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
        for ops in [
            known_binder(0, [6, 5]),
            known_binder(1, [6, 5]),
            known_binder(0, [5, 6]),
        ] {
            let escaped = run_old(&program, plan, &ops);
            assert_eq!(escaped.failed, Some(10));
            assert_eq!(trace_of(&escaped.form, 10), ["@5 ~ @10", "@4 ~ @9"]);
            assert_eq!(
                (escaped.unchanged, escaped.changed),
                (1, 0),
                "{}",
                escaped.form
            );
        }
        let paired = run_old(&program, plan, &known_binder(0, [6, 6]));
        assert_eq!(paired.failed, None);
        assert!(
            paired
                .form
                .ends_with("4 = &5[0]poly(@4; &6[0]!)\n5 = @6\n6 = @0\n7 = @3\n8 = @4\n9 = @5\n"),
            "{}",
            paired.form
        );
    }

    /// What an instance and a copy of a polymorphic type share and
    /// duplicate (observed). Every instance and every copy of a generic
    /// polymorphic type has bound variables of its own, and the body names
    /// them: `Tunivar` is copied like any generic node and keeps its name
    /// (`Tunivar _ as ty -> ty`, compiler/ml/btype.ml:536), the binders
    /// before the body (btype.ml:537-539). A row whose row variable is a
    /// bound variable ends in the copy of that variable (`@17`, `@27`),
    /// whichever of the row and the binder list is copied first
    /// (`Tsubst ty -> ty`, compiler/ml/ctype.ml:816; `norm_univar`,
    /// btype.ml:396-401). `generalize_structure` makes a universal
    /// variable generic (it is not a `Tvar`, ctype.ml:532-537), so a copy
    /// of an annotation's type duplicates it too. A copy of a type that is
    /// not generic is the type.
    #[test]
    fn old_checker_copies_the_bound_variables_with_their_type() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN);
        let ops = [
            Op::BeginDef,
            Op::Instance(7),
            Op::Copy(0),
            Op::EndDef,
            Op::Generalize(0),
            Op::Copy(0),
            Op::Copy(0),
        ];
        assert_eq!(
            run_old(&program, plan, &ops).form,
            "0 = &0[G]fn(&1[G]obj{&2[G]f: &3[G]poly(&4[G]fn(&5[G][fixed #A(&6[G]int) | &7[G]!]) => @5; @7); &8[G]nil}) => &9[G]unit\n\
             1 = @0\n\
             2 = &10[0]fn(&11[0]obj{&12[0]f: &13[0]poly(&14[0]fn(&15[0][fixed #A(&16[0]int) | &17[0]!]) => @15; @17); &18[0]nil}) => &19[0]unit\n\
             3 = &20[0]fn(&21[0]obj{&22[0]f: &23[0]poly(&24[0]fn(&25[0][fixed #A(&26[0]int) | &27[0]!]) => @25; @27); &28[0]nil}) => &29[0]unit\n"
        );
        let ops = [
            Op::BeginDef,
            Op::Instance(7),
            Op::EndDef,
            Op::GeneralizeStructure(0),
            Op::Copy(0),
        ];
        assert_eq!(
            run_old(&program, plan, &ops).form,
            "0 = &0[G]fn(&1[G]obj{&2[G]f: &3[G]poly(&4[G]fn(&5[G][fixed #A(&6[G]int) | &7[G]!]) => @5; @7); &8[G]nil}) => &9[G]unit\n\
             1 = &10[0]fn(&11[0]obj{&12[0]f: &13[0]poly(&14[0]fn(&15[0][fixed #A(&16[0]int) | &17[0]!]) => @15; @17); &18[0]nil}) => &19[0]unit\n"
        );
        // Both sides agree on these today: no unification.
        compare(
            0,
            &program,
            Plan::new(Tier::Kernel, OBJECTS | VARIANTS | UNIVARS),
            &ops,
            Fault::None,
        )
        .unwrap_or_else(|e| panic!("{e}"));
    }

    /// What a failed unification of two polymorphic types leaves
    /// (observed, in the explaining mode). `'a 'b. ('a, 'b) => 'a` (at the
    /// starting level) against `'a 'b. ('a, 'b) => 'b` (one definition
    /// up) fails at the result. Left behind: the levels unify2 lowered
    /// before the clash (the right type prints `[0]` everywhere,
    /// `update_level !env lv t2`, compiler/ml/ctype.ml:2284), and the two
    /// pairs of universal variables that were unified before it, linked
    /// (`link_type t1 t2`, ctype.ml:2247: the binder list of the right
    /// type is `@5 @6`, the left one's nodes). A failure puts back the
    /// descriptors of the linked structure nodes only (ctype.ml:2437). So
    /// the same unification the other way round then SUCCEEDS: the two
    /// binder lists are one pair of nodes, `!a` and `!b` are both free in
    /// their scope and pair (`set_univar r1 t2; set_univar r2 t1`,
    /// ctype.ml:1554-1556), and the type ends as `poly(fn(!a, !a) => !a;
    /// !a !a)`.
    #[test]
    fn old_checker_keeps_the_links_of_a_failed_polymorphic_unification() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
        let ops = [
            Op::Instance(2),
            Op::BeginDef,
            Op::Instance(4),
            Op::Unify(0, 1),
            Op::Unify(1, 0),
        ];
        let old = run_old(&program, plan, &ops);
        assert_eq!(failed_traces(&old.form), [(3, 6)]);
        assert_eq!(trace_of(&old.form, 3).last(), Some(&"@5 ~ @6"));
        assert!(
            old.form.contains(
                "! 3 left\n\
                 0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!a, &6[0]!b) => @5; @5 @6); &7[0]nil}) => &8[0]unit\n\
                 1 = &9[0]fn(&10[0]obj{&11[0]f: &12[0]poly(&13[0]fn(@5, @6) => @6; @5 @6); &14[0]nil}) => &15[0]unit\n"
            ),
            "{}",
            old.form
        );
        assert!(
            old.form.ends_with(
                "0 = &0[0]fn(&1[0]obj{&2[0]f: &3[0]poly(&4[0]fn(&5[0]!a, @5) => @5; @5 @5); &6[0]nil}) => &7[0]unit\n1 = @0\n"
            ),
            "{}",
            old.form
        );
    }

    /// A universal variable outside its binder (observed, in the
    /// explaining mode). Operand 5 is the body of `'a. 'a => 'a`, where
    /// `!a` is free; operand 7 is `!a` itself.
    /// - A variable against the body, in either order, and against `!a`:
    ///   refused by `occur_univar` (`unify1_var`, compiler/ml/ctype.ml:
    ///   2216-2219), whose pair is the universal variable and a new
    ///   variable (`raise (Unify [(ty, newgenvar ())])`, ctype.ml:1586),
    ///   after the pair of the unification. (The old checker makes that
    ///   variable at the current level, `[0]`; OCaml's is generic.)
    /// - `!a` against another universal variable with no scope open:
    ///   `unify_univar` has no list to search (`[] -> raise (Unify [])`,
    ///   ctype.ml:1559): one pair.
    /// - A variable against the polymorphic type itself (operand 4) is
    ///   bound: every universal variable of it is under its binder.
    #[test]
    fn old_checker_refuses_a_free_universal_variable() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
        let old = run_old(&program, plan, &FREE_UNIVAR);
        assert_eq!(failed_traces(&old.form), [(7, 2), (8, 2), (10, 2), (12, 1)]);
        assert_eq!(trace_of(&old.form, 7), ["@8 ~ @4", "@5 ~ &9[0]'"]);
        assert_eq!(trace_of(&old.form, 8), ["@4 ~ @8", "@5 ~ &9[0]'"]);
        assert_eq!(trace_of(&old.form, 10), ["@8 ~ @5", "@5 ~ &9[0]'"]);
        assert_eq!(trace_of(&old.form, 12), ["@5 ~ @9"]);
        assert!(old.form.ends_with("8 = &9[0]!\n9 = @3\n"), "{}", old.form);
    }

    /// The operations of `old_checker_refuses_a_free_universal_variable`.
    const FREE_UNIVAR: [Op; 15] = [
        Op::Instance(0),
        Op::Slot(0, 0),
        Op::Child(0, 0),
        Op::Slot(2, 0),
        Op::Slot(3, 0),
        Op::Slot(4, 0),
        Op::Var,
        Op::Unify(6, 5),
        Op::Unify(5, 6),
        Op::Slot(5, 1),
        Op::Unify(6, 7),
        Op::Univar,
        Op::Unify(7, 8),
        Op::Var,
        Op::Unify(9, 4),
    ];

    /// The fixed cases of [`UNIVAR_PROGRAM`] on both sides: every case
    /// the tests `old_checker_*` above observe, in `Mode::Success` and, for
    /// those whose trace has no pair of `occur_univar`, in the explaining
    /// mode (the old checker makes that pair's variable at the current
    /// level, OCaml and the new side at the generic level: section 8.6,
    /// decision 49).
    /// Reaches: R3m, R3e, R3f, R3n, R3g.
    #[test]
    fn universal_variables_agree_on_fixed_cases() {
        let program = compile(UNIVAR_PROGRAM.to_string());
        let mut cases: Vec<Vec<Op>> = Vec::new();
        for (left, right) in [
            (0, 1),
            (2, 3),
            (2, 4),
            (0, 2),
            (5, 5),
            (5, 6),
            (7, 7),
            (7, 8),
            (8, 8),
        ] {
            cases.push(two(left, right).to_vec());
            cases.push(two(right, left).to_vec());
        }
        for (second, right) in [(0, [6, 5]), (1, [6, 5]), (0, [5, 6]), (0, [6, 6])] {
            cases.push(known_binder(second, right).to_vec());
        }
        cases.push(vec![
            Op::Instance(2),
            Op::BeginDef,
            Op::Instance(4),
            Op::Unify(0, 1),
            Op::Unify(1, 0),
        ]);
        // The seven operations that make the operands of `FREE_UNIVAR`,
        // then one unification each: a variable bound to the whole
        // polymorphic type, two universal variables with no scope open.
        let base = &FREE_UNIVAR[..7];
        cases.push(then(base, &[Op::Var, Op::Unify(7, 4)]));
        cases.push(then(base, &[Op::Slot(5, 1), Op::Univar, Op::Unify(7, 8)]));
        let explained = cases.len();
        // Each refusal of `occur_univar`, as the last operation.
        cases.push(then(base, &[Op::Unify(6, 5)]));
        cases.push(then(base, &[Op::Unify(5, 6)]));
        cases.push(then(base, &[Op::Slot(5, 1), Op::Unify(6, 7)]));
        for (index, ops) in cases.iter().enumerate() {
            let plan = Plan::new(Tier::Full, UNIVAR_PLAN);
            compare(index as u64, &program, plan, ops, Fault::None)
                .unwrap_or_else(|e| panic!("{e}"));
            if index < explained {
                let plan = Plan::new(Tier::Full, UNIVAR_PLAN | EXPLAIN);
                compare(index as u64, &program, plan, ops, Fault::None)
                    .unwrap_or_else(|e| panic!("{e}"));
            }
        }
    }

    /// The corner of decision 53 on the old checker, built by hand
    /// (section 8.6, decision 58; observed). Two `Reither` fields inside
    /// two polymorphic types: `#A` with the types `[(u, x); x]` on the
    /// left and `[(u', x'); x']` on the right. Each side would gain the
    /// other's two types; the tuples hold a universal variable and are
    /// unified instead, which makes `x` and `x'` one node; the lists the
    /// fields gain were computed BEFORE that unification
    /// (compiler/ml/ctype.ml:2685-2706):
    ///
    /// ```text
    /// let tl2' = remq tl2 tl1 and tl1' = remq tl1 tl2 in
    /// let tl1', tlu1 = split_univars tl1' and tl2', tlu2 = split_univars tl2' in
    /// (match (tlu1, tlu2) with
    /// | tu1 :: tlu1, _ :: _ ->
    ///   if not !(passive_variants ()) then List.iter (unify env tu1) (tlu1 @ tlu2)
    /// ...
    /// let f1' = Reither (c1 || c2, tl1', m1 || m2, e)
    /// ```
    ///
    /// so each field ends with THREE types, the last two one node (`@4
    /// @4`): the type it had, and the same node again as the type it
    /// gained. The OCaml compiler was run on a source program that reaches
    /// the corner (the pull request of the sixth skeleton turn has it):
    /// its fields hold three types after the join too.
    #[test]
    fn old_checker_gains_a_type_the_holders_made_a_duplicate() {
        use crate::types::type_expr::{RowDesc, RowField};
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN);
        let old = old_context(&program, plan);
        let ctx = &old.ctx;
        let side = || {
            let u = ctx.new_univar(None);
            let x = ctx.new_var(None);
            let holder = ctx.new_tuple(vec![u, x]);
            let field = RowField::Reither {
                constant: false,
                types: vec![holder, x],
                matched: false,
                link: ctx.alloc_row_field(None),
            };
            let row = ctx.new_type(TypeDesc::Tvariant(ctx.new_row_desc(RowDesc {
                row_fields: vec![("A".into(), field)].into(),
                row_more: ctx.new_var(None),
                row_closed: true,
                row_fixed: false,
                row_name: None,
            })));
            (ctx.new_poly(row, vec![u]), row, x)
        };
        let (left, row1, x1) = side();
        let (right, row2, x2) = side();
        let mut state = ctype::UnifyState::new();
        state.set_env(&old.env);
        ctype::unify(ctx, &mut state, left, right).unwrap();
        let form = old_forms(&old, plan, &[left, right, row1, row2, x1, x2], &[]).0;
        assert_eq!(
            form,
            "0 = &0[0]poly(&1[0][closed #A?^0(&2[0](&3[0]!, &4[0]') @4 @4 ) | &5[0]']; @3)\n\
             1 = @0\n2 = @1\n3 = @1\n4 = @4\n5 = @4\n"
        );
    }

    /// What the old checker's walks do with the arguments of a row name
    /// that is no longer the name of the innermost row (section 8.6,
    /// decision 60; observed). `[> #B]` is unified with `[> #A] as p<y>`:
    /// the named row gains `#B` through a new variant node its row
    /// variable is linked to (`set_more`, compiler/ml/ctype.ml:2597-2619)
    /// and the merged row has no name (ctype.ml:2574-2586), so `p<y>` is
    /// the name of a row whose `more` is a variant. `iter_row` visits a
    /// name's arguments only for the row a chain ends in
    /// (compiler/ml/btype.ml:229-241), so `y`, which is in no field, is
    /// reached by no walk: a lowering of the row leaves `y` at its level
    /// (`[1]`), a generalization leaves it there, `deep_occur` does not
    /// find it, a copy of the generalized row makes no copy of it that
    /// the row holds, and a variable bound to the row leaves it.
    #[test]
    fn old_checker_does_not_reach_the_arguments_of_a_stale_row_name() {
        use crate::types::type_expr::{RowDesc, RowField};
        let program = compile(UNIVAR_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, UNIVAR_PLAN);
        let old = old_context(&program, plan);
        let ctx = &old.ctx;
        let mut out = String::new();
        for walk in 0..5 {
            ctx.begin_def();
            let y = ctx.new_var(None);
            let path = crate::types::path::Path::pident(ctx.create_ident("p"));
            let row = |tag: &str, name: Option<(crate::types::path::Path, Vec<TypeExprRef>)>| {
                ctx.new_type(TypeDesc::Tvariant(ctx.new_row_desc(RowDesc {
                    row_fields: vec![(tag.into(), RowField::Rpresent(None))].into(),
                    row_more: ctx.new_var(None),
                    row_closed: false,
                    row_fixed: false,
                    row_name: name,
                })))
            };
            let named = row("A", Some((path, vec![y])));
            let other = row("B", None);
            let mut state = ctype::UnifyState::new();
            state.set_env(&old.env);
            ctype::unify(ctx, &mut state, other, named).unwrap();
            ctx.end_def();
            let mut operands = vec![named, y];
            match walk {
                0 => ctype::update_level(ctx, ctx.current_level(), named),
                1 => ctype::generalize(ctx, named),
                2 => {
                    let found = ctype::deep_occur(ctx, y, named);
                    out.push_str(&format!("deep_occur {found}\n"));
                }
                3 => {
                    ctype::generalize(ctx, named);
                    ctype::generalize(ctx, y);
                    operands.push(ctype::instance(ctx, named));
                    operands.push(ctype::instance(ctx, y));
                }
                _ => {
                    let v = ctx.new_var(None);
                    ctype::unify(ctx, &mut state, v, named).unwrap();
                }
            }
            out.push_str(&old_forms(&old, plan, &operands, &[]).0);
        }
        assert_eq!(
            out,
            "0 = &0[0][#A #B | &1[0]']\n1 = &2[1]'\n\
             0 = &0[G][#A #B | &1[G]']\n1 = &2[1]'\n\
             deep_occur false\n\
             0 = &0[1][#A #B | &1[1]']\n1 = &2[1]'\n\
             0 = &0[G][#A #B | &1[G]']\n1 = &2[G]'\n2 = &3[0][#A #B | &4[0]']\n3 = &5[0]'\n\
             0 = &0[0][#A #B | &1[0]']\n1 = &2[1]'\n"
        );
    }

    /// A program for the fixed cases of pattern mode ([`PATTERN`]): the
    /// two locally abstract types `n0` (the older) and `n1`, an abstract
    /// type with a parameter `k`, a data type `d`, and values whose
    /// parameters are the types a case unifies: `p0` nullary types and a
    /// tuple, `p1` and `p2` constructors of one path, `p3` variables,
    /// `p4` closed rows, `p5` open rows and a row with an upper bound,
    /// `p6` tuples and nested constructors.
    const PATTERN_PROGRAM: &str = "type n0\ntype n1\ntype k<'a>\ntype d<'a> = D('a)\n\
        external p0: (n0, n1, int, (int, int)) => unit = \"p0\"\n\
        external p1: (k<n0>, k<int>, k<n1>, k<'a>) => unit = \"p1\"\n\
        external p2: (d<n0>, d<int>, d<n1>, d<'a>) => unit = \"p2\"\n\
        external p3: ('a, 'b, ('a, int)) => unit = \"p3\"\n\
        external p4: ([#A(n0) | #B], [#A(int) | #B], [#A(int) | #C], [#A | #B]) => unit = \"p4\"\n\
        external p5: ([> #A(n0)], [< #A(int) | #B], [#C(n1)], [> #A(int)], [> #A(int) | #B]) => unit = \"p5\"\n\
        external p6: ((n0, int), (int, (int, int)), k<k<n0>>, k<k<int>>) => unit = \"p6\"\n";

    /// The plan of the fixed cases of pattern mode.
    const PATTERN_PLAN: u16 = OBJECTS | VARIANTS | REFS | BUILD | PATTERN;

    /// One definition, an instance of value `value` (operand 0), its
    /// parameters `left` and `right` (operands 1 and 2), unified in
    /// pattern mode with `flags` ([`Op::Gadt`]).
    fn pattern(value: u16, left: u8, right: u8, flags: u8) -> Vec<Op> {
        vec![
            Op::BeginDef,
            Op::Instance(value),
            Op::Child(0, left),
            Op::Child(0, right),
            Op::Gadt(1, 2, flags),
        ]
    }

    /// One definition, the parameter `structure` of an instance of value
    /// `value` (operand 1) and `n0` (operand 3), unified in pattern mode
    /// as `unify_gadt` does, `n0` on the left.
    fn refine(value: u16, structure: u8) -> Vec<Op> {
        vec![
            Op::BeginDef,
            Op::Instance(value),
            Op::Child(0, structure),
            Op::Instance(0),
            Op::Child(2, 0),
            Op::Gadt(3, 1, 3),
        ]
    }

    /// O(text): the equations a form ends with.
    fn equations(form: &str) -> Vec<&str> {
        form.lines().filter(|line| line.starts_with("= ")).collect()
    }

    /// The old checker on a fixed pattern case: the outcome, and that it
    /// is a judge of every operation ([`old_judges`]).
    fn old_pattern(ops: &[Op]) -> Outcome {
        let program = compile(PATTERN_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN);
        assert_eq!(old_judges(&program, plan, ops), ops.len(), "{ops:?}");
        run_old(&program, plan, ops)
    }

    /// Which pairs get an equation, and in which direction (observed;
    /// section 8.6, decision 62; the old checker is a judge of all of
    /// it). A locally abstract type against a type that is not one gets
    /// the equation whichever side it is on (`Tconstr (path, [], _), _
    /// when is_instantiable ...` and its mirror, compiler/ml/ctype.ml:
    /// 2385-2392), and the two nodes stay two nodes. Two locally abstract
    /// types: the one of the higher newtype level gets it (`if
    /// find_newtype_level !env path > find_newtype_level !env path' then
    /// (path, t2') else (path', t1')`, ctype.ml:2373-2384): `n1`, on
    /// either side. Without `generate_equations` there is none and the
    /// unification succeeds (`reify` and no `mcomp`, ctype.ml:2393-2397).
    /// `int` against a tuple with equations fails: `mcomp`. A second
    /// equation is for the expansion: `n1` against `n0` after `n0 := int`
    /// gives `n1 := int` (`unify2` expands both, ctype.ml:2276-2280).
    #[test]
    fn old_checker_gives_the_equation_to_the_newer_locally_abstract_type() {
        let left = old_pattern(&pattern(0, 0, 2, 3));
        assert_eq!(left.failed, None);
        assert_eq!(
            left.form,
            "0 = &0[1]fn(&1[1]n0, &2[1]n1, &3[1]int, &4[1](&5[1]int, &6[1]int)) => &7[1]unit\n1 = @1\n2 = @3\n= n0 := &0[G]int\n"
        );
        assert_eq!(
            equations(&old_pattern(&pattern(0, 2, 0, 3)).form),
            ["= n0 := &0[G]int"]
        );
        assert_eq!(
            equations(&old_pattern(&pattern(0, 0, 1, 3)).form),
            ["= n1 := &0[G]n0"]
        );
        assert_eq!(
            equations(&old_pattern(&pattern(0, 1, 0, 3)).form),
            ["= n1 := &0[G]n0"]
        );
        assert_eq!(
            equations(&old_pattern(&pattern(0, 0, 3, 3)).form),
            ["= n0 := &0[G](&1[G]int, &2[G]int)"]
        );
        let silent = old_pattern(&pattern(0, 0, 2, 2));
        assert_eq!((silent.failed, equations(&silent.form).len()), (None, 0));
        assert_eq!(old_pattern(&pattern(0, 2, 3, 3)).failed, Some(4));
        let mut chain = pattern(0, 0, 2, 3);
        chain.extend([Op::Child(0, 1), Op::Gadt(3, 1, 3)]);
        assert_eq!(
            equations(&old_pattern(&chain).form),
            ["= n0 := &0[G]int", "= n1 := &1[G]int"]
        );
    }

    /// The arguments of two constructors of one path (observed; decision
    /// 62; the old checker is a judge). As `unify_gadt` runs it
    /// (`assume_injective`) the arguments are unified with equations
    /// (`set_mode_pattern ~generate:true ~injective:false`,
    /// compiler/ml/ctype.ml:2352-2354): `k<n0>` against `k<int>` gives
    /// `n0 := int`. Below that, `k`, abstract and not of the unit, is not
    /// injective: its arguments are unified without equations and what
    /// does not unify is reified (ctype.ml:2359-2371): no equation, a
    /// success, the two `k` nodes two nodes, and a later unification of
    /// the two in expression mode fails, so nothing of the pattern
    /// unification is left to make them equal. `d`, a data type, is
    /// injective (`expands_to_datatype`, ctype.ml:2355-2358): `n0 := int`.
    /// Without `generate_equations` neither has one. A variable argument
    /// is a link to the other argument in every mode.
    #[test]
    fn old_checker_refines_the_arguments_of_a_constructor_by_its_injectivity() {
        assert_eq!(
            equations(&old_pattern(&pattern(1, 0, 1, 3)).form),
            ["= n0 := &0[G]int"]
        );
        for flags in [0, 1] {
            let abstract_type = old_pattern(&pattern(1, 0, 1, flags));
            assert_eq!(
                (abstract_type.failed, equations(&abstract_type.form).len()),
                (None, 0)
            );
            assert!(
                abstract_type.form.contains("\n1 = @1\n2 = @3\n"),
                "{}",
                abstract_type.form
            );
        }
        assert_eq!(
            equations(&old_pattern(&pattern(2, 0, 1, 1)).form),
            ["= n0 := &0[G]int"]
        );
        assert_eq!(equations(&old_pattern(&pattern(2, 0, 1, 0)).form).len(), 0);
        let nested = old_pattern(&pattern(6, 2, 3, 3));
        assert_eq!((nested.failed, equations(&nested.form).len()), (None, 0));
        let mut again = pattern(6, 2, 3, 3);
        again.extend([Op::Child(1, 0), Op::Child(2, 0), Op::Unify(3, 4)]);
        assert_eq!(old_pattern(&again).failed, Some(7));
        let mut direct = pattern(1, 0, 1, 1);
        direct.push(Op::Unify(1, 2));
        assert_eq!(old_pattern(&direct).failed, Some(5));
        let variable = old_pattern(&pattern(1, 0, 3, 1));
        assert!(variable.form.contains("&7[1]k<@2>"), "{}", variable.form);
    }

    /// What `reify` makes of a variable and of a row variable (observed;
    /// decision 62; the old checker is a judge of both, and of the names
    /// of variables without a name). The variable of `('a, int)` at the
    /// newtype level becomes a new abstract type `$0` at the variable's
    /// level, and the equation's body is a generic copy that names it
    /// (compiler/ml/ctype.ml:1815-1840, 2085-2087). The row variable of
    /// `[> #A(int)]` becomes `$0` as well, and the row a fixed row over
    /// it (`{r with row_fields = []; row_fixed = true; row_more = t}`,
    /// ctype.ml:1845-1851). A second one is `$1` (`get_new_abstract_name`,
    /// ctype.ml:908-922). No operation gives the harness a variable with
    /// a name: `$'a` is tested by hand in tc/r3_tests.rs.
    #[test]
    fn old_checker_reifies_a_variable_and_a_row_variable() {
        let variable = old_pattern(&refine(3, 2));
        assert_eq!(variable.failed, None);
        assert_eq!(
            variable.form.lines().next(),
            Some("0 = &0[1]fn(&1[1]$0, &2[1]', &3[1](@1, &4[1]int)) => &5[1]unit")
        );
        assert_eq!(
            equations(&variable.form),
            ["= n0 := &0[G](&1[G]$0, &2[G]int)"]
        );
        let row = old_pattern(&refine(5, 3));
        assert!(
            row.form.contains("&10[1][fixed #A(&11[1]int) | &12[1]$0]"),
            "{}",
            row.form
        );
        assert_eq!(
            equations(&row.form),
            ["= n0 := &0[G][fixed #A(&1[G]int) | &2[G]$0]"]
        );
        let mut twice = refine(3, 2);
        twice.extend([
            Op::Child(2, 1),
            Op::Instance(3),
            Op::Child(5, 2),
            Op::Gadt(4, 6, 3),
        ]);
        assert_eq!(
            equations(&old_pattern(&twice).form),
            [
                "= n0 := &0[G](&1[G]$0, &2[G]int)",
                "= n1 := &3[G](&4[G]$1, &5[G]int)"
            ]
        );
    }

    /// What a pattern unification that fails leaves (observed; decision
    /// 62; the old checker is a judge of the graph, not of the
    /// environment, which the harness drops with the state). `reify`
    /// links before it refuses: a variable below the newtype level is a
    /// link to its new abstract type when the unification fails with the
    /// pair of that type and a new variable (`link_type ty t; if ty.level
    /// < newtype_level then raise (Unify [(t, newvar2 ty.level)])`,
    /// compiler/ml/ctype.ml:1837-1839), and a row that clashes is a fixed
    /// row when `mcomp` refuses the pair after it (ctype.ml:2400-2408).
    /// The handler of unify3 puts back only the description of the left
    /// node (`t1'.desc <- d1`, ctype.ml:2437-2439). The caller that goes
    /// on after a failure restores a snapshot, the levels and the
    /// environment it kept (`set_state`, compiler/ml/typecore.ml:
    /// 1299-1305); `unify_pat_types_gadt` itself reports the failure
    /// (typecore.ml:488-495). A failure below a tuple whose first
    /// elements gave an equation leaves the graph as it was.
    #[test]
    fn old_checker_keeps_what_reify_linked_when_a_pattern_unification_fails() {
        let ops = [
            Op::Instance(3),
            Op::Child(0, 2),
            Op::BeginDef,
            Op::Instance(0),
            Op::Child(2, 0),
            Op::Gadt(3, 1, 3),
        ];
        let below = old_pattern(&ops);
        assert_eq!(below.failed, Some(5));
        assert_eq!(trace_of(&below.form, 5), ["@7 ~ @3", "@1 ~ &14[0]'"]);
        assert_eq!(below.form.lines().last(), Some("3 = @7"), "{}", below.form);
        assert!(
            below
                .form
                .contains("\n0 = &0[0]fn(&1[0]$0, &2[0]', &3[0](@1, &4[0]int)) => &5[0]unit\n"),
            "{}",
            below.form
        );
        let row = old_pattern(&pattern(5, 0, 2, 3));
        assert_eq!(row.failed, Some(4));
        assert!(
            row.form.contains("&1[1][fixed #A(&2[1]n0) | &3[1]$0]"),
            "{}",
            row.form
        );
        let partial = old_pattern(&pattern(6, 0, 1, 3));
        assert_eq!(partial.failed, Some(4));
        assert_eq!(trace_of(&partial.form, 4), ["@1 ~ @4", "@3 ~ @6"]);
        assert_eq!((partial.unchanged, partial.changed), (1, 0));
    }

    /// Rows in pattern mode (observed; decision 62; the old checker is a
    /// judge of all three). Two closed rows of which one lacks a tag of
    /// the other, and a constant tag against one with an argument, clash
    /// and are not compatible: `mcomp` refuses them (`mcomp_row`,
    /// compiler/ml/ctype.ml:1985-2009). A fixed row against an open row
    /// with one more tag clashes (`unify_row` does not extend a fixed
    /// row) and is compatible: the unification succeeds after the
    /// backtrack, the two rows are two nodes, the open one is reified to
    /// a fixed row over `$1` and nothing else of the attempt is left
    /// (ctype.ml:2400-2408).
    #[test]
    fn old_checker_accepts_rows_that_clash_and_are_compatible() {
        assert_eq!(old_pattern(&pattern(4, 0, 2, 3)).failed, Some(4));
        assert_eq!(old_pattern(&pattern(4, 0, 3, 3)).failed, Some(4));
        let mut ops = refine(5, 3);
        ops.extend([Op::Child(0, 4), Op::Gadt(1, 4, 3)]);
        let compatible = old_pattern(&ops);
        assert_eq!(compatible.failed, None);
        assert!(
            compatible.form.contains(
                "&10[1][fixed #A(&11[1]int) | &12[1]$0], &13[1][fixed #A(&14[1]int) #B | &15[1]$1]"
            ),
            "{}",
            compatible.form
        );
        assert!(compatible.form.contains("\n1 = @10\n") && compatible.form.contains("\n4 = @13\n"));
    }

    /// Where the old checker is NOT a judge (observed; decision 62): two
    /// structures that a pattern unification unifies are one node
    /// afterwards. OCaml records the pair as assumed equal and links
    /// neither (`Pattern -> add_type_equality t1' t2'`,
    /// compiler/ml/ctype.ml:2327-2331): a type that is equal only under
    /// the equations of one case must not become the other for good. Two
    /// tuples of two instances are one node; of two closed rows that
    /// differ in `n0` against `int` the left one prints `int` afterwards.
    /// [`old_judges`] ends a case before such an operation.
    #[test]
    fn old_checker_links_the_structures_a_pattern_unification_unifies() {
        let program = compile(PATTERN_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, PATTERN_PLAN);
        let tuples = [
            Op::BeginDef,
            Op::Instance(0),
            Op::Child(0, 3),
            Op::Instance(0),
            Op::Child(2, 3),
            Op::Gadt(1, 3, 3),
        ];
        let linked = run_old(&program, plan, &tuples);
        assert!(linked.form.contains("\n3 = @4\n"), "{}", linked.form);
        assert_eq!(old_judges(&program, plan, &tuples), 5);
        let rows = pattern(4, 0, 1, 3);
        let linked = run_old(&program, plan, &rows);
        assert!(
            linked
                .form
                .starts_with("0 = &0[1]fn(&1[1][closed #A(&2[1]int) #B | &3[1]nil], @1,"),
            "{}",
            linked.form
        );
        assert_eq!(old_judges(&program, plan, &rows), 4);
    }

    /// The self-test of [`PATTERN`]: the two sides agree today on a
    /// pattern program for everything that is not a pattern unification
    /// (the locally abstract types, the abstract type with a parameter
    /// and the data type convert, print and unify in expression mode as
    /// any type), on the fixed program and on 300 generated cases with
    /// the pattern unifications taken out; and the form of a pattern
    /// plan ends with no equation there.
    #[test]
    fn the_two_sides_agree_on_pattern_programs_without_a_pattern_unification() {
        let program = compile(PATTERN_PROGRAM.to_string());
        assert_eq!(program.values.len(), 7);
        let plan = Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN);
        let ops = [
            Op::BeginDef,
            Op::Instance(0),
            Op::Instance(1),
            Op::Child(0, 0),
            Op::Child(1, 3),
            Op::Child(3, 0),
            Op::Unify(2, 4),
            Op::Instance(5),
            Op::Child(0, 1),
            Op::Unify(2, 6),
            Op::EndDef,
            Op::Generalize(1),
            Op::Copy(1),
        ];
        let outcome = compare(0, &program, plan, &ops, Fault::None)
            .unwrap_or_else(|report| panic!("{report}"));
        assert_eq!(outcome.failed, Some(9));
        assert!(outcome.form.contains("k<&"), "{}", outcome.form);
        assert_eq!(equations(&outcome.form).len(), 0);
        let plan = Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN);
        let mut patterns = 0;
        for seed in 1..=3u64 {
            for sequence in 0..100u64 {
                let case_seed = seed * 1_000_003 + sequence;
                let (program, ops) = case(plan, case_seed);
                patterns += ops.iter().filter(|op| matches!(op, Op::Gadt(..))).count();
                let ops: Vec<Op> = ops
                    .into_iter()
                    .filter(|op| !matches!(op, Op::Gadt(..)))
                    .collect();
                if let Err(report) = compare(case_seed, &program, plan, &ops, Fault::None) {
                    panic!("{report}");
                }
            }
        }
        assert!(patterns >= 300, "{patterns}");
    }

    /// The old side of the pattern plan runs today and is not vacuous
    /// (observed, 1,200 cases: 1136 judged to the end, 64 not; 950
    /// pattern unifications that succeed and 493 that fail; 130 cases end
    /// with an equation, 3 with two, 183 with a reified type; the bounds
    /// are a third of that): cases the old checker judges to the end and cases it
    /// leaves at a pattern unification that linked two structures
    /// ([`old_judges`]); among the judged operations, pattern
    /// unifications that succeed and that fail; cases that end with an
    /// equation, with two, and with a reified type.
    #[test]
    fn old_side_of_the_pattern_plan_is_not_vacuous() {
        let plan = Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN);
        let (mut whole, mut cut, mut ok, mut failed) = (0, 0, 0, 0);
        let (mut equation, mut two, mut reified) = (0, 0, 0);
        for seed in 1..=12u64 {
            for sequence in 0..100u64 {
                let (program, ops) = case(plan, seed * 1_000_003 + sequence);
                let judged = old_judges(&program, plan, &ops);
                if judged == ops.len() {
                    whole += 1;
                } else {
                    cut += 1;
                }
                let ops = &ops[..judged];
                let outcome = run_old(&program, plan, ops);
                for (index, op) in ops.iter().enumerate() {
                    if matches!(op, Op::Gadt(..)) {
                        match outcome.form.contains(&format!("! {index} trace\n")) {
                            true => failed += 1,
                            false => ok += 1,
                        }
                    }
                }
                let count = equations(&outcome.form).len();
                equation += usize::from(count >= 1);
                two += usize::from(count >= 2);
                reified += usize::from(outcome.form.contains('$'));
            }
        }
        println!("pattern plan, old side: {whole} {cut} {ok} {failed} {equation} {two} {reified}");
        assert!(
            whole >= 380
                && cut >= 20
                && ok >= 300
                && failed >= 160
                && equation >= 40
                && two >= 1
                && reified >= 60,
            "{whole} {cut} {ok} {failed} {equation} {two} {reified}"
        );
    }

    /// The deliberately wrong new side of [`PATTERN`]
    /// ([`Fault::ExpressionMode`]: a pattern unification runs as an
    /// expression unification, which the kernel has today) is reported by
    /// the generated cases: by a case in which the old checker adds an
    /// equation, and by one in which a pattern unification the old
    /// checker accepts fails in expression mode (observed, 300 cases: 228
    /// with a pattern unification; reported with an equation on the old
    /// side 21, with a failure only the wrong side has 58).
    #[test]
    fn generated_cases_find_a_pattern_unification_in_expression_mode() {
        let plan = Plan::new(Tier::Full, PATTERN_PLAN);
        let (mut cases, mut equation, mut refused) = (0, 0, 0);
        for seed in 1..=3u64 {
            for sequence in 0..100u64 {
                let case_seed = seed * 1_000_003 + sequence;
                let (program, ops) = case(plan, case_seed);
                let ops = &ops[..old_judges(&program, plan, &ops)];
                if !ops.iter().any(|op| matches!(op, Op::Gadt(..))) {
                    continue;
                }
                cases += 1;
                let old = run_old(&program, plan, ops);
                if compare(case_seed, &program, plan, ops, Fault::ExpressionMode).is_err() {
                    let new = run_new(&program, plan, ops, Fault::ExpressionMode);
                    equation += usize::from(!equations(&old.form).is_empty());
                    refused += usize::from(new.failed.is_some() && old.failed != new.failed);
                }
            }
        }
        println!("expression mode fault: {cases} {equation} {refused}");
        assert!(
            cases >= 75 && equation >= 7 && refused >= 19,
            "{cases} {equation} {refused}"
        );
    }

    /// AFTER R3s (run against its prototype; CHECKER_REWRITE 8.6,
    /// decision 110 as corrected in its review): `EXPLAINED_UNTIL_R3S`
    /// is empty, `EXPLAINED_OLD_DIFFERS` stays as it is, and
    /// `EXPLAINED_NEW_DIFFERS` is `[4_000_045, 20_000_132]`. On those
    /// two seeds it is the NEW side that differs from OCaml. After a
    /// unification that failed, OCaml's `unify` expands the types of
    /// the trace with tracing off (`raise (Unify (expand_trace !env
    /// trace))`, compiler/ml/ctype.ml:2732-2737; `expand_trace`,
    /// 1697-1701), so the expansion of `n1` is in the memo all `n1`
    /// nodes share (200-202) and a later instance links to the node.
    /// The old side does the same (`ctype::record_trace_expansions`).
    /// The new side expands no trace yet: once it traces, its expansion
    /// is in the node's own memo only and the instance is a new node.
    /// Owed by the design turn after R3s.
    ///
    /// The seeds of the explained pattern plan (20 programs of 100 cases)
    /// that differ. The first five wait for R3s as [`UNTIL_R3S`] does (a
    /// nullary constructor's memo while instances are traced; in
    /// 20,000,132 it is the old side that links a copy and the new one
    /// that makes a node, after a failed case: which memo holds the
    /// expansion differs the same way). The last two are differences of
    /// the old checker from OCaml, on record in CHECKER_REWRITE 8.6
    /// (decisions 77 and 78), which the build of R3s leaves listed:
    ///
    /// - 11,000,046: the body of an equation keeps the `Tnil` of the
    ///   destination on the old side (`OldSeen::bare_nil`), so an
    ///   instance of the body shares it with the destination;
    /// - 8,000,098: a lowering that clashes on its first pass runs again
    ///   expanding every constructor with arguments in place
    ///   (`| Tconstr (_, _ :: _, _) when expand -> (try link_type ty
    ///   (!forward_try_expand_once env ty)`, compiler/ml/ctype.ml:602-604),
    ///   and in the explaining mode what it wrote stays (decision 14):
    ///   `po<int>` is its expansion afterwards. The old side leaves
    ///   `po<int>`.
    const EXPLAINED_UNTIL_R3S: [u64; 0] = [];
    const EXPLAINED_OLD_DIFFERS: [u64; 2] = [8_000_098, 11_000_046];
    /// The seeds of the explained pattern plan on which the NEW side
    /// differs from OCaml and the old checker is right (see above):
    /// none until R3s is built.
    const EXPLAINED_NEW_DIFFERS: [u64; 2] = [4_000_045, 20_000_132];

    /// The seeds of the pattern plan on which the new side differs from
    /// OCaml (and from the old checker, which is right here) until slice
    /// R3s (all seven agree against the prototype of R3s; its build
    /// makes this list empty). In each, an instance is taken after a pattern case has added
    /// an equation and expanded a locally abstract type inside a later
    /// case: the copy of a nullary constructor of that type links to the
    /// node that was expanded, where OCaml makes a node. While GADT
    /// instances are traced (an equation is in the environment),
    /// `proper_abbrevs` gives a nullary constructor its own memo and not
    /// `simple_abbrevs`:
    ///
    /// ```text
    /// let proper_abbrevs path tl abbrev =
    ///   if tl <> [] || !(trace_gadt_instances ()) || is_object_type path then abbrev
    ///   else simple_abbrevs ()
    /// ```
    ///
    /// (compiler/ml/ctype.ml:200-202), so `find_repr` of a later copy
    /// finds nothing (ctype.ml:720). Tracing is R3s (section 8.11); its
    /// build empties this list and changes nothing else of this test.
    const UNTIL_R3S: [u64; 0] = [];

    /// The acceptance test of pattern mode on generated cases (section
    /// 8.9): 10,000 cases of the pattern plan, each run on the
    /// operations the old checker is a judge of ([`old_judges`]), agree,
    /// in the success mode and, 2,000 of them, in the explaining mode;
    /// and the fixed cases of the observation tests above agree
    /// (equations and their direction, the arguments of one path by the
    /// flags, `reify`, what a failure leaves, rows that clash). The
    /// seven seeds of [`UNTIL_R3S`] differ and are listed, each read
    /// against OCaml; any other seed that differs is read against the
    /// OCaml lines of 8.9 before anything is pinned (the build prompt
    /// says how).
    ///
    /// Reaches: R3m, R3e, R3f, R3n, R3h, R3r.
    #[test]
    fn pattern_plan_agrees_on_generated_cases() {
        let program = compile(PATTERN_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN);
        let mut chain = pattern(0, 0, 2, 3);
        chain.extend([Op::Child(0, 1), Op::Gadt(3, 1, 3)]);
        let mut twice = refine(3, 2);
        twice.extend([
            Op::Child(2, 1),
            Op::Instance(3),
            Op::Child(5, 2),
            Op::Gadt(4, 6, 3),
        ]);
        let mut compatible = refine(5, 3);
        compatible.extend([Op::Child(0, 4), Op::Gadt(1, 4, 3)]);
        let mut again = pattern(6, 2, 3, 3);
        again.extend([Op::Child(1, 0), Op::Child(2, 0), Op::Unify(3, 4)]);
        let below = vec![
            Op::Instance(3),
            Op::Child(0, 2),
            Op::BeginDef,
            Op::Instance(0),
            Op::Child(2, 0),
            Op::Gadt(3, 1, 3),
        ];
        let mut cases: Vec<Vec<Op>> = vec![chain, twice, compatible, again, below, refine(5, 3)];
        for (value, left, right) in [
            (0, 0, 2),
            (0, 2, 0),
            (0, 0, 1),
            (0, 1, 0),
            (0, 0, 3),
            (0, 2, 3),
            (1, 0, 1),
            (1, 0, 3),
            (2, 0, 1),
            (4, 0, 2),
            (4, 0, 3),
            (5, 0, 2),
            (6, 0, 1),
            (6, 2, 3),
        ] {
            for flags in 0..4 {
                cases.push(pattern(value, left, right, flags));
            }
        }
        for (index, ops) in cases.iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None)
                .unwrap_or_else(|e| panic!("{e}"));
        }
        let coverage = run_cases_except(Plan::new(Tier::Full, PATTERN_PLAN), &UNTIL_R3S);
        assert_eq!(coverage.cases + UNTIL_R3S.len(), 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        let (explained, differing) =
            run_plan(Plan::new(Tier::Full, PATTERN_PLAN | EXPLAIN), 1, 20, 100);
        let mut known =
            [&EXPLAINED_UNTIL_R3S[..], &EXPLAINED_OLD_DIFFERS[..], &EXPLAINED_NEW_DIFFERS[..]].concat();
        known.sort_unstable();
        let seeds: Vec<u64> = differing.iter().map(|(seed, _)| *seed).collect();
        let unknown = differing.iter().find(|(seed, _)| !known.contains(seed));
        assert!(seeds == known, "{seeds:?}\n{}", unknown.map_or("", |(_, report)| report.as_str()));
        assert_eq!(explained.cases + known.len(), 2_000);
    }

    /// 10,000 cases of everything on programs with polymorphic fields,
    /// universal variables, rows whose row variable is bound and
    /// hand-made polymorphic types, and 10,000 more with made nodes: the
    /// acceptance test of R3g. A case that differs is read against the
    /// OCaml arm before either side is followed (decision 18); a seed
    /// where the old checker departs from ctype.ml is pinned with
    /// `run_cases_except` and its cause by the reviewer, not by the
    /// builder.
    /// Reaches: R3m, R3e, R3f, R3n, R3g.
    #[test]
    fn univar_plan_agrees_on_generated_cases() {
        let coverage = run_cases(Plan::new(Tier::Full, UNIVAR_PLAN), 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 10 > coverage.cases, "{coverage:?}");
        run_cases(Plan::new(Tier::Full, UNIVAR_PLAN | BUILD), 1, 100, 100);
    }

    /// The plans of the relations: on plain programs, on objects and
    /// variants, and with universal variables.
    const RELATION_PLANS: [u16; 3] = [RELATIONS, RELATIONS | OBJECTS | VARIANTS, RELATIONS | UNIVAR_PLAN];

    /// How often each relation answered `true` and `false` in a form:
    /// `[moregeneral, equal, matches]`, each `[true, false]`.
    fn answers(form: &str, counts: &mut [[usize; 2]; 3]) {
        for line in form.lines() {
            for (at, name) in ["moregeneral", "equal", "matches"].iter().enumerate() {
                if let Some(rest) = line.split(": ").nth(1).and_then(|rest| rest.strip_prefix(name)) {
                    counts[at][usize::from(rest == " = false")] += 1;
                }
            }
        }
    }

    /// The old side of the relation plans runs today and is not vacuous:
    /// each relation answers `true` and `false` on each plan (observed;
    /// the counts are printed, and each is asserted at a quarter of what
    /// was seen or less). Today's checker has all three relations
    /// (types/ctype.rs `moregeneral`, `equal`, `matches`).
    #[test]
    fn old_side_of_the_relation_plans_is_not_vacuous() {
        for with in RELATION_PLANS {
            let plan = Plan::new(Tier::Full, with);
            let mut counts = [[0usize; 2]; 3];
            let mut cases = 0;
            for seed in 1..=12u64 {
                for sequence in 0..100u64 {
                    let (program, ops) = case(plan, seed * 1_000_003 + sequence);
                    let outcome = run_old(&program, plan, &ops);
                    if outcome.failed.is_none() {
                        cases += 1;
                        answers(&outcome.form, &mut counts);
                    }
                }
            }
            println!("relation plan {with:#x}, old side: {cases} cases, {counts:?}");
            assert!(cases >= 600, "{cases}");
            for (at, [yes, no]) in counts.iter().enumerate() {
                assert!(*yes >= 20 && *no >= 20, "relation {at} of plan {with:#x}: {counts:?}");
            }
        }
    }

    /// A relation that answers the opposite is reported: the harness
    /// compares the answers.
    ///
    /// Reaches: R3i.
    #[test]
    fn a_wrong_answer_of_a_relation_is_reported() {
        let program = compile(FIXED.to_string());
        let plan = Plan::new(Tier::Full, RELATIONS);
        let ops = [Op::Instance(0), Op::Instance(0), Op::Equal(0, 1, true), Op::Matches(0, 1)];
        let outcome = compare(0, &program, plan, &ops, Fault::None).unwrap();
        assert!(outcome.form.starts_with("2: equal = true\n3: matches = true\n"), "{}", outcome.form);
        assert!(compare(0, &program, plan, &ops, Fault::WrongAnswer).is_err());
    }

    /// The acceptance test of R3i against today's checker: 10,000 cases
    /// of every operation and the three relations on plain programs,
    /// 10,000 on programs with objects and variants and 5,000 with
    /// universal variables. Each case compares the answer of every
    /// relation and the form of every operand after it: what
    /// `moregeneral` linked, and that `equal` and `matches` left
    /// nothing. Today's checker is the judge of the answers; it is NOT
    /// the judge of what the memos hold after `equal` and `matches`
    /// (it takes no snapshot in `equal`; decision 115), so both sides
    /// forget the memos after those two. A case that differs is read
    /// against the OCaml arm before either side is followed (decision
    /// 18); a seed where today's checker departs from ctype.ml is pinned
    /// with its cause by the reviewer, not by the builder.
    /// Each listed seed is then made again and run on both sides, and
    /// its two outcomes must differ as the class of its list says
    /// (`fits`). A seed that does not fit panics with the plan, the
    /// seed, the list and the reason, after every seed of the plan was
    /// asked.
    ///
    /// Reaches: R3m, R3e, R3f, R3n, R3g, R3i.
    #[test]
    fn relation_plan_agrees_on_generated_cases() {
        for (at, programs) in [(0, 100), (1, 100), (2, 50)] {
            let with = RELATION_PLANS[at];
            let (coverage, differing) = run_plan(Plan::new(Tier::Full, with), 1, programs, 100);
            let seeds: Vec<u64> = differing.iter().map(|(seed, _)| *seed).collect();
            let mut known: Vec<u64> = match at {
                0 => Vec::new(),
                1 => [&ROWS_OLD_EQUAL_DIFFERS[..], &ROWS_OLD_NIL_DIFFERS[..]].concat(),
                _ => [&UNIVARS_OLD_EQUAL_DIFFERS[..], &UNIVARS_OLD_NIL_DIFFERS[..], &UNIVARS_OLD_FREE_UNIVAR_DIFFERS[..]].concat(),
            };
            known.sort_unstable();
            let unknown = differing.iter().find(|(seed, _)| !known.contains(seed));
            assert!(seeds == known, "plan {with:#x}: {seeds:?}\n{}", unknown.map_or("", |(_, report)| report.as_str()));
            assert_eq!(coverage.cases + known.len(), programs as usize * 100);
            let lists: &[(&str, &[u64], SeedClass)] = match at {
                0 => &[],
                1 => &[
                    ("ROWS_OLD_EQUAL_DIFFERS", &ROWS_OLD_EQUAL_DIFFERS, SeedClass::Equal),
                    ("ROWS_OLD_NIL_DIFFERS", &ROWS_OLD_NIL_DIFFERS, SeedClass::Nil),
                ],
                _ => &[
                    ("UNIVARS_OLD_EQUAL_DIFFERS", &UNIVARS_OLD_EQUAL_DIFFERS, SeedClass::Equal),
                    ("UNIVARS_OLD_NIL_DIFFERS", &UNIVARS_OLD_NIL_DIFFERS, SeedClass::Nil),
                    ("UNIVARS_OLD_FREE_UNIVAR_DIFFERS", &UNIVARS_OLD_FREE_UNIVAR_DIFFERS, SeedClass::FreeUnivar),
                ],
            };
            // `compare` runs both sides on these operations: no relation
            // plan has the bit of pattern unification, the only one under
            // which it cuts them (`old_judges`).
            let plan = Plan::new(Tier::Full, with);
            let mut refused = Vec::new();
            for &(list, seeds, class) in lists {
                for &seed in seeds {
                    let (program, ops) = case(plan, seed);
                    let old = run_old(&program, plan, &ops);
                    let new = run_new(&program, plan, &ops, Fault::None);
                    if let Err(reason) = fits(class, &old, &new) {
                        refused.push(format!(
                            "plan {with:#x}, seed {seed}, {list}: {reason}\n--- operations\n{ops:?}\n--- old: failed {:?}\n{}--- new: failed {:?}\n{}",
                            old.failed, old.form, new.failed, new.form
                        ));
                    }
                }
            }
            assert!(refused.is_empty(), "{} listed seeds do not fit their class\n{}", refused.len(), refused.join("\n"));
        }
    }

    /// Seeds of the relation plan with objects and variants on which
    /// TODAY'S CHECKER differs from OCaml in `equal`: it answers `false`
    /// for two rows of which the right one was extended by a
    /// unification (its `row_more` is a variant node). OCaml's
    /// `eqtype_row` expands `row_more row2`, the FUNCTION, which follows
    /// the chain to the row variable (compiler/ml/ctype.ml:3327,
    /// btype.ml `row_more`); types/ctype.rs `equal_rows_without_renaming`
    /// expands the FIELD `right.row_more`, finds the inner row and
    /// compares the left row with that row alone. On each of these seeds
    /// the two sides agree on everything but `equal = false` (old)
    /// against `equal = true` (new), seen in the tenth skeleton turn.
    const ROWS_OLD_EQUAL_DIFFERS: [u64; 52] = [
        1000013, 3000021, 4000062, 9000070, 11000114, 12000122, 14000076, 17000141, 20000083, 20000109,
        21000071, 22000117, 23000165, 30000145, 30000180, 32000124, 32000163, 33000101, 35000150, 40000189,
        40000190, 40000200, 41000213, 42000196, 46000232, 49000208, 49000234, 55000260, 58000191, 58000235,
        58000270, 65000224, 65000236, 68000208, 68000273, 69000302, 72000300, 75000246, 75000308, 76000293,
        78000236, 78000242, 78000305, 81000299, 82000304, 84000339, 86000341, 90000348, 91000338, 92000279,
        95000330, 100000301,
    ];
    /// Seeds on which TODAY'S CHECKER differs from OCaml in the copy of
    /// `moregeneral`: its `subst_identity_copy` keeps a `Tnil` node as
    /// it keeps a variable (types/ctype.rs, the arm `Tvar | Tunivar |
    /// Tnil`), where `Subst.typexp` copies it (compiler/ml/subst.ml:
    /// 135-143 keeps `Tvar` and `Tunivar` only), and a `Tnil` of the
    /// pattern is then one node with a `Tnil` of the subject. The
    /// answers agree; the old form has fewer `nil` nodes of their own.
    const ROWS_OLD_NIL_DIFFERS: [u64; 4] = [32000157, 54000224, 69000217, 84000296];
    /// As [`ROWS_OLD_EQUAL_DIFFERS`], on the plan with universal
    /// variables.
    const UNIVARS_OLD_EQUAL_DIFFERS: [u64; 16] = [
        2000018, 6000024, 8000033, 9000110, 11000112, 12000074, 14000060, 22000109, 23000147, 23000165,
        28000123, 33000167, 37000116, 37000194, 48000215, 49000216,
    ];
    /// As [`ROWS_OLD_NIL_DIFFERS`], on the plan with universal variables.
    const UNIVARS_OLD_NIL_DIFFERS: [u64; 3] = [5000060, 12000099, 14000052];
    /// Seeds on which TODAY'S CHECKER differs from OCaml in
    /// `moregen_occur`: `moregeneral` with `inst_nongen` of a weak
    /// variable against a FREE universal variable. OCaml refuses it
    /// (`occur_univar env ty`, compiler/ml/ctype.ml:2917-2918, called
    /// unconditionally; with no binder entered a `Tunivar` raises,
    /// 1584-1585: `if not (Type_set.mem ty bound) then raise (Unify
    /// [(ty, newgenvar ())])`); types/ctype.rs `moregen_occur` runs
    /// `occur_univar` only `if !univars.pairs.is_empty()`, so with no
    /// scope open it accepts and links the weak variable. Both read in
    /// full in the tenth skeleton turn: old `moregeneral = true`, new
    /// `false`.
    const UNIVARS_OLD_FREE_UNIVAR_DIFFERS: [u64; 2] = [5000086, 13000118];

    /// The way today's checker differs from OCaml on the seeds of one
    /// of the five lists above, each stated as what today's checker does
    /// differently and nothing more.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum SeedClass {
        /// [`ROWS_OLD_EQUAL_DIFFERS`], [`UNIVARS_OLD_EQUAL_DIFFERS`]:
        /// today's `equal` answers `false` for a row that a unification
        /// extended, where OCaml answers `true`.
        Equal,
        /// [`ROWS_OLD_NIL_DIFFERS`], [`UNIVARS_OLD_NIL_DIFFERS`]: today's
        /// copy inside `moregeneral` keeps a `nil` node where OCaml copies
        /// it, so a `nil` of the subject is the node of a `nil` of the
        /// pattern on the old side and a node of its own on the new.
        Nil,
        /// [`UNIVARS_OLD_FREE_UNIVAR_DIFFERS`]: today's `moregeneral`
        /// accepts a weak variable against a free universal variable and
        /// links it, where OCaml refuses.
        FreeUnivar,
    }

    /// O(line): the operation index, the relation and the answer of an
    /// answer line of a form (`3: equal = true`, `Outcome` and
    /// `New::answer`; the old side prints the same line in `run_old`).
    fn answer_line(line: &str) -> Option<(usize, &str, bool)> {
        let (index, rest) = line.split_once(": ")?;
        let index = index.parse().ok()?;
        let (relation, answer) = rest.split_once(" = ")?;
        if !["moregeneral", "equal", "matches"].contains(&relation) {
            return None;
        }
        let answer = match answer {
            "true" => true,
            "false" => false,
            _ => return None,
        };
        Some((index, relation, answer))
    }

    /// O(text): a form with the sharing of `nil` nodes taken out. A node
    /// prints as `&n[level]` and its description at its first visit and
    /// as `@n` at every later one (`old_form`, `New::node_form`). Every
    /// `nil` node, its mark `&n[level]nil` and every reference `@n` to
    /// it, becomes the bare `nil`, with no number and no level, as the
    /// harness prints the `nil` of an equation (`OldSeen::bare_nil`):
    /// the copy of the new side may be made at another level than the
    /// node the old side kept (seed 54,000,224: `@8`, a `nil` at level 0,
    /// against `&20[1]nil`). Every other mark and reference is then
    /// renumbered in the order of first appearance, so that a `nil`
    /// taken out does not shift the numbers of the nodes after it.
    /// Nothing else is changed: a node other than a `nil` that is shared
    /// on one side and not on the other still prints differently.
    fn unshare_nil(form: &str) -> String {
        let bytes = form.as_bytes();
        // The number after a mark or a reference at `at`, and its end.
        let number = |at: usize| -> Option<(usize, usize)> {
            let end = (at + 1..bytes.len()).find(|&i| !bytes[i].is_ascii_digit()).unwrap_or(bytes.len());
            form[at + 1..end].parse().ok().map(|n| (n, end))
        };
        // The end of `[level]nil` at `at`, when that is what is there.
        let nil_at = |at: usize| -> Option<usize> {
            if bytes.get(at) != Some(&b'[') {
                return None;
            }
            let close = at + form[at..].find(']')?;
            let end = close + 1 + "nil".len();
            let word = |i: usize| bytes.get(i).is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_' || *b == b'\'');
            (form[close + 1..].starts_with("nil") && !word(end)).then_some(end)
        };
        let mut nils = std::collections::HashSet::new();
        for (at, &byte) in bytes.iter().enumerate() {
            if byte == b'&'
                && let Some((n, end)) = number(at)
                && nil_at(end).is_some()
            {
                nils.insert(n);
            }
        }
        let mut renumbered: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
        let mut out = String::with_capacity(form.len());
        let (mut at, mut copied) = (0, 0);
        while at < bytes.len() {
            let Some((n, end)) = matches!(bytes[at], b'&' | b'@').then(|| number(at)).flatten() else {
                at += 1;
                continue;
            };
            out.push_str(&form[copied..at]);
            if nils.contains(&n) {
                out.push_str("nil");
                at = match bytes[at] {
                    b'&' => nil_at(end).expect("a nil mark"),
                    _ => end,
                };
            } else {
                let next = renumbered.len();
                let _ = write!(out, "{}{}", bytes[at] as char, renumbered.entry(n).or_insert(next));
                at = end;
            }
            copied = at;
        }
        out.push_str(&form[copied..]);
        out
    }

    /// O(text): `Ok` when the two outcomes of a listed seed differ and
    /// differ as `class` says; otherwise the reason, with the first line
    /// that does not fit, old beside new.
    fn fits(class: SeedClass, old: &Outcome, new: &Outcome) -> Result<(), String> {
        let refuse = |why: &str, old: Option<&str>, new: Option<&str>| {
            Err(format!(
                "{class:?}: {why}\n  old: {}\n  new: {}",
                old.unwrap_or("(no line)"),
                new.unwrap_or("(no line)")
            ))
        };
        let (o, n): (Vec<&str>, Vec<&str>) = (old.form.lines().collect(), new.form.lines().collect());
        let lines = o.len().max(n.len());
        let first = (0..lines).find(|&at| o.get(at) != n.get(at));
        let same_rest = old.failed == new.failed && old.unchanged == new.unchanged && old.changed == new.changed;
        let failed = || {
            refuse(
                "the outcomes differ outside the form",
                Some(&format!("failed {:?}, {} unchanged, {} changed", old.failed, old.unchanged, old.changed)),
                Some(&format!("failed {:?}, {} unchanged, {} changed", new.failed, new.unchanged, new.changed)),
            )
        };
        match class {
            SeedClass::Equal => {
                if !same_rest {
                    return failed();
                }
                let Some(first) = first else {
                    return refuse("no line differs", None, None);
                };
                if o.len() != n.len() {
                    return refuse("the forms have a different number of lines", o.get(first).copied(), n.get(first).copied());
                }
                for at in first..lines {
                    if o[at] == n[at] {
                        continue;
                    }
                    match (answer_line(o[at]), answer_line(n[at])) {
                        (Some((left, "equal", false)), Some((right, "equal", true))) if left == right => {}
                        _ => {
                            return refuse(
                                "a line differs that is not `equal = false` (old) against `equal = true` (new)",
                                Some(o[at]),
                                Some(n[at]),
                            );
                        }
                    }
                }
                Ok(())
            }
            SeedClass::FreeUnivar => {
                let Some(first) = first else {
                    return refuse("no line differs", None, None);
                };
                match (o.get(first).and_then(|l| answer_line(l)), n.get(first).and_then(|l| answer_line(l))) {
                    (Some((left, "moregeneral", true)), Some((right, "moregeneral", false))) if left == right => Ok(()),
                    _ => refuse(
                        "the first line that differs is not `moregeneral = true` (old) against `moregeneral = false` (new)",
                        o.get(first).copied(),
                        n.get(first).copied(),
                    ),
                }
            }
            SeedClass::Nil => {
                if !same_rest {
                    return failed();
                }
                let Some(_) = first else {
                    return refuse("no line differs", None, None);
                };
                for at in 0..lines {
                    let (left, right) = (o.get(at).copied(), n.get(at).copied());
                    let answer = left.and_then(answer_line).is_some() || right.and_then(answer_line).is_some();
                    if answer && left != right {
                        return refuse("an answer line differs", left, right);
                    }
                }
                let (old_unshared, new_unshared) = (unshare_nil(&old.form), unshare_nil(&new.form));
                let (o, n): (Vec<&str>, Vec<&str>) = (old_unshared.lines().collect(), new_unshared.lines().collect());
                match (0..o.len().max(n.len())).find(|&at| o.get(at) != n.get(at)) {
                    None => Ok(()),
                    Some(at) => refuse(
                        "the forms differ with the sharing of `nil` nodes taken out",
                        o.get(at).copied(),
                        n.get(at).copied(),
                    ),
                }
            }
        }
    }

    /// `fits` takes each class's real pair and refuses a fault the
    /// seed list alone does not see. The pairs are cut from the forms
    /// both sides print against the prototype of R3i: `Equal` from seed
    /// 1,000,013 of [`ROWS_OLD_EQUAL_DIFFERS`], `Nil` from seed
    /// 54,000,224 of [`ROWS_OLD_NIL_DIFFERS`], `FreeUnivar` from seed
    /// 5,000,086 of [`UNIVARS_OLD_FREE_UNIVAR_DIFFERS`]; each fault edits
    /// one or two lines of one side.
    #[test]
    fn a_listed_seed_must_fit_its_class() {
        let outcome = |form: &str| Outcome {
            failed: None,
            form: form.to_string(),
            unchanged: 0,
            changed: 0,
        };
        let pair = |class: SeedClass, old: &str, new: &str| fits(class, &outcome(old), &outcome(new));
        // Seed 1,000,013.
        let equal_old = "1: matches = true\n9: moregeneral = false\n10: equal = false\n11: matches = true\n\
            0 = &0[0]pv<&1[0](&2[0][closed #B?c() | &3[0]'], &4[0](&5[0]rv, &6[0]'))>\n\
            1 = &7[G]pv<&8[G](&9[G][closed #B?c() | &10[G]'], &11[G](&12[G]rv, &13[G]'))>\n\
            2 = @0\n";
        let equal_new = equal_old.replace("10: equal = false", "10: equal = true");
        assert_eq!(pair(SeedClass::Equal, equal_old, &equal_new), Ok(()));
        let failing: [(&str, String); 4] = [
            ("no line differs", equal_old.to_string()),
            ("a second, non-answer line differs", equal_new.replace("2 = @0", "2 = @7")),
            ("the answer the other way round", equal_old.replace("10: equal = false", "10: equal = true")),
            ("an answer of `moregeneral` differs", equal_new.replace("9: moregeneral = false", "9: moregeneral = true")),
        ];
        let refused = pair(SeedClass::Equal, equal_old, &failing[0].1).unwrap_err();
        assert!(refused.contains("no line differs"), "{}: {refused}", failing[0].0);
        let refused = pair(SeedClass::Equal, equal_old, &failing[1].1).unwrap_err();
        assert!(refused.contains("old: 2 = @0\n  new: 2 = @7"), "{}: {refused}", failing[1].0);
        let refused = pair(SeedClass::Equal, &failing[2].1, equal_old).unwrap_err();
        assert!(refused.contains("old: 10: equal = true\n  new: 10: equal = false"), "{refused}");
        let refused = pair(SeedClass::Equal, equal_old, &failing[3].1).unwrap_err();
        assert!(refused.contains("old: 9: moregeneral = false\n  new: 9: moregeneral = true"), "{refused}");
        // A failure on one side only.
        let ended = Outcome { failed: Some(9), ..outcome("") };
        assert!(fits(SeedClass::Equal, &outcome(equal_old), &ended).is_err());

        // Seed 54,000,224: the old subject (operand 2) refers to the
        // pattern's `nil` nodes (`@8`, `@12`), the new one has its own.
        let nil_old = "4: equal = true\n6: moregeneral = true\n8: equal = true\n\
            0 = &0[0]obj{&1[0]x: &2[0]poly(&3[0][closed #A?c() | &4[0]'];); &5[0]y: &6[0]poly(&7[0][closed #A #B | &8[0]nil];); &9[0]z: &10[0]poly(&11[0]a2;); &12[0]nil}\n\
            1 = @0\n\
            2 = &13[1]obj{&14[1]x: &15[1]poly(&16[1][closed #A?c() | @4];); &17[1]y: &18[1]poly(&19[1][closed #A #B | @8];); &20[1]z: &21[1]poly(&22[1]a2;); @12}\n";
        let nil_new = "4: equal = true\n6: moregeneral = true\n8: equal = true\n\
            0 = &0[0]obj{&1[0]x: &2[0]poly(&3[0][closed #A?c() | &4[0]'];); &5[0]y: &6[0]poly(&7[0][closed #A #B | &8[0]nil];); &9[0]z: &10[0]poly(&11[0]a2;); &12[0]nil}\n\
            1 = @0\n\
            2 = &13[1]obj{&14[1]x: &15[1]poly(&16[1][closed #A?c() | @4];); &17[1]y: &18[1]poly(&19[1][closed #A #B | &20[1]nil];); &21[1]z: &22[1]poly(&23[1]a2;); &24[1]nil}\n";
        assert_eq!(pair(SeedClass::Nil, nil_old, nil_new), Ok(()));
        assert!(pair(SeedClass::Nil, nil_old, nil_old).is_err(), "Nil took: no line differs");
        let refused = pair(SeedClass::Nil, nil_old, &nil_new.replace("6: moregeneral = true", "6: moregeneral = false")).unwrap_err();
        assert!(refused.contains("an answer line differs"), "{refused}");
        // The row variable `@4`, not a `nil`, printed in place on the new
        // side: shared on the old side only.
        let unshared_variable = nil_new.replace(
            "2 = &13[1]obj{&14[1]x: &15[1]poly(&16[1][closed #A?c() | @4];); &17[1]y: &18[1]poly(&19[1][closed #A #B | &20[1]nil];); &21[1]z: &22[1]poly(&23[1]a2;); &24[1]nil}",
            "2 = &13[1]obj{&14[1]x: &15[1]poly(&16[1][closed #A?c() | &17[0]'];); &18[1]y: &19[1]poly(&20[1][closed #A #B | &21[1]nil];); &22[1]z: &23[1]poly(&24[1]a2;); &25[1]nil}",
        );
        assert_ne!(unshared_variable, nil_new);
        let refused = pair(SeedClass::Nil, nil_old, &unshared_variable).unwrap_err();
        assert!(refused.contains("taken out"), "{refused}");
        // A level that differs on a node that is not a `nil`.
        let refused = pair(SeedClass::Nil, nil_old, &nil_new.replace("&22[1]poly(&23[1]a2;)", "&22[1]poly(&23[0]a2;)")).unwrap_err();
        assert!(refused.contains("taken out"), "{refused}");

        // Seed 5,000,086.
        let univar_old = "1: equal = true\n2: matches = true\n5: moregeneral = true\n0 = &0[0]!\n1 = @0\n2 = @0\n";
        let univar_new = "1: equal = true\n2: matches = true\n5: moregeneral = false\n0 = &0[0]'\n1 = &1[0]!\n2 = @0\n";
        assert_eq!(pair(SeedClass::FreeUnivar, univar_old, univar_new), Ok(()));
        let refused = pair(SeedClass::FreeUnivar, univar_old, &univar_new.replace("moregeneral = false", "moregeneral = true")).unwrap_err();
        assert!(refused.contains("old: 0 = &0[0]!\n  new: 0 = &0[0]'"), "{refused}");
        let refused = pair(SeedClass::FreeUnivar, univar_new, univar_old).unwrap_err();
        assert!(refused.contains("old: 5: moregeneral = false\n  new: 5: moregeneral = true"), "{refused}");
        let refused = pair(SeedClass::FreeUnivar, univar_old, &univar_new.replace("1: equal = true", "1: equal = false")).unwrap_err();
        assert!(refused.contains("old: 1: equal = true\n  new: 1: equal = false"), "{refused}");
        assert!(pair(SeedClass::FreeUnivar, univar_old, univar_old).is_err());

        // The normalisation itself: a `nil` by reference and in place are
        // one text, and the marks after it are renumbered.
        assert_eq!(unshare_nil("0 = &0[0]nil\n1 = &1[1]t<@0, &2[0]'>\n"), "0 = nil\n1 = &0[1]t<nil, &1[0]'>\n");
        assert_eq!(unshare_nil("0 = &0[0]nil\n1 = &1[1]t<&2[G]nil, &3[0]'>\n"), "0 = nil\n1 = &0[1]t<nil, &1[0]'>\n");
        // A constructor whose name starts with `nil` is not a `nil`.
        assert_eq!(unshare_nil("0 = &0[0]nilx\n1 = @0\n"), "0 = &0[0]nilx\n1 = @0\n");
    }

    /// The plan of the cases of GADT instances.
    const INSTANCE_PLAN: u16 = PATTERN_PLAN | INSTANCES;

    /// `n0 := int` at the level of a scope when `scope`, then `n0`
    /// against `int` in expression mode, which expands the node `n0`
    /// under tracing, then `last`. Operand 1 is the node `n0`, operand 2
    /// the node `int`.
    fn instance_case(scope: bool, last: &[Op]) -> Vec<Op> {
        let mut ops = vec![Op::BeginDef, Op::Instance(0), Op::Child(0, 0), Op::Child(0, 2)];
        if scope {
            ops.push(Op::Scope);
        }
        ops.extend([Op::Gadt(1, 2, 3), Op::Unify(1, 2)]);
        ops.extend_from_slice(last);
        ops
    }

    /// What today's checker does with GADT instances when the case has
    /// a scope ([`INSTANCES`]; pull requests 350 and 352), observed: it
    /// is the judge of the generated cases of R3s. `n0 := int` at the
    /// level of a scope, then `n0` used at `int`, which expands the node
    /// under tracing (compiler/ml/ctype.ml:1218-1227): the node and the
    /// node of `int` it was unified with are members of the set, and
    ///
    /// - lowering either below the scope is refused
    ///   (`| Some lv -> if level < lv then raise (Unify [(ty, newvar2
    ///   level)])`, ctype.ml:587-589);
    /// - without [`Op::Scope`] the same lowering succeeds: no set exists
    ///   and nothing joined one (8.11, (v));
    /// - a copy of the generalized member made with the environment is
    ///   a member (`Env.add_gadt_instances env lv [t]`, ctype.ml:
    ///   770-774): lowering the copy is refused.
    #[test]
    fn old_checker_refuses_a_member_below_its_scope() {
        let program = compile(PATTERN_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, INSTANCE_PLAN);
        let failed = |scope: bool, last: &[Op]| run_old(&program, plan, &instance_case(scope, last)).failed;
        assert_eq!(failed(true, &[Op::Lower(1, 0)]), Some(7));
        assert_eq!(failed(true, &[Op::Lower(2, 0)]), Some(7));
        assert_eq!(failed(false, &[Op::Lower(1, 0)]), None);
        let copied = [Op::Generalize(1), Op::EndDef, Op::Copy(1), Op::Lower(3, 0)];
        assert_eq!(failed(true, &copied), Some(10));
        assert_eq!(failed(false, &copied), None);
    }

    /// The seeds of the explained plan of GADT instances (20 programs of
    /// 100 cases) on which the two sides differ, with the side that
    /// differs from OCaml for each class, read against the lines:
    ///
    /// - 8,000,098 and 11,000,046: `EXPLAINED_OLD_DIFFERS` (decisions
    ///   77 and 78);
    /// - 17,000,064 and 20,000,132: the NEW side differs. After a
    ///   unification that failed, OCaml's `unify` expands the types of
    ///   the trace with tracing off (compiler/ml/ctype.ml:2732-2737,
    ///   1697-1701), so the expansion of `n1` is in the memo all `n1`
    ///   nodes share (200-202) and a later instance links to the node,
    ///   as on the old side (`ctype::record_trace_expansions`,
    ///   types/ctype.rs). The new side expands no trace yet; owed by
    ///   the design turn after R3s;
    /// - 4,000,069: `a3` (a nullary abbreviation whose head, through
    ///   `t0 := k<int>`, is a member) against a function type at a lower
    ///   level. unify2 expands `a3` first, and `try_expand_head` adds
    ///   the chain of `a3` to the set of the head (ctype.ml:1271-1276);
    ///   `update_level` then refuses `a3` itself (587-589): the pair is
    ///   `a3` and a variable, and `a3` keeps its level, as on the new
    ///   side. The old side lowers `a3` and reports a node below it.
    const EXPLAINED_INSTANCES_DIFFER: [u64; 5] =
        [4_000_069, 8_000_098, 11_000_046, 17_000_064, 20_000_132];

    /// The acceptance test of R3s on generated cases (section 8.11;
    /// decisions 103 and 110): the fixed cases of
    /// `old_checker_refuses_a_member_below_its_scope` agree, 10,000
    /// cases of the pattern plan with scopes agree in the success mode,
    /// and of 2,000 in the explaining mode all but the listed seeds.
    /// More than a quarter of the cases fail somewhere, a refused
    /// member among them. A seed that differs is read against the OCaml
    /// lines of 8.11 before anything is pinned; the builder pins none.
    ///
    /// Reaches: R3m, R3e, R3f, R3n, R3h, R3r, R3s.
    #[test]
    fn instance_plan_agrees_on_generated_cases() {
        let program = compile(PATTERN_PROGRAM.to_string());
        let plan = Plan::new(Tier::Full, INSTANCE_PLAN);
        let copied = [Op::Generalize(1), Op::EndDef, Op::Copy(1), Op::Lower(3, 0)];
        let cases = [
            instance_case(true, &[Op::Lower(1, 0)]),
            instance_case(true, &[Op::Lower(2, 0)]),
            instance_case(false, &[Op::Lower(1, 0)]),
            instance_case(true, &copied),
            instance_case(false, &copied),
        ];
        for (index, ops) in cases.iter().enumerate() {
            compare(index as u64, &program, plan, ops, Fault::None).unwrap_or_else(|e| panic!("{e}"));
        }
        let coverage = run_cases(plan, 1, 100, 100);
        assert_eq!(coverage.cases, 10_000);
        assert!(coverage.failures * 4 > coverage.cases, "{coverage:?}");
        let (explained, differing) = run_plan(Plan::new(Tier::Full, INSTANCE_PLAN | EXPLAIN), 1, 20, 100);
        let seeds: Vec<u64> = differing.iter().map(|(seed, _)| *seed).collect();
        let unknown = differing.iter().find(|(seed, _)| !EXPLAINED_INSTANCES_DIFFER.contains(seed));
        assert!(
            seeds == EXPLAINED_INSTANCES_DIFFER,
            "{seeds:?}\n{}",
            unknown.map_or("", |(_, report)| report.as_str())
        );
        assert_eq!(explained.cases + seeds.len(), 2_000);
    }
}
