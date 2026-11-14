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
//! A failed unification ends the case: what a failed unification leaves in
//! the graph is not observable (CHECKER_REWRITE "R3 as designed", decision
//! 5), so nothing after it is compared except the index of the failure.
//!
//! Nothing here is on a compile path; the harness allocates freely.

use std::fmt::Write as _;
use std::sync::Arc;

use super::bridge::from_old::{Input, from_old};
use super::expand::{ExpandMode, TypeTable};
use super::graph::{ARROW, CONSTR, GENERIC, NONE, TUPLE, Ty, VAR};
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
}

/// What one side reports for one case.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Outcome {
    /// Index of the operation that failed, when one did.
    pub failed: Option<usize>,
    /// The form of every operand; empty after a failure.
    pub form: String,
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
            type_text(rng, depth - 1, vars, nullary, unary, out);
            out.push('>');
        }
        1 => {
            out.push('(');
            for i in 0..2 + rng.below(2) {
                if i != 0 {
                    out.push_str(", ");
                }
                type_text(rng, depth - 1, vars, nullary, unary, out);
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
                type_text(rng, depth - 1, vars, nullary, unary, out);
            }
            out.push_str(") => ");
            type_text(rng, depth - 1, vars, nullary, unary, out);
            out.push(')');
        }
    }
}

/// O(program size): the source of one program. Declarations: two abstract
/// types, then (when the tier has them) up to five abbreviations, each
/// nullary or unary over the earlier ones, a unary one sometimes phantom.
/// Values: externals with random types over two type variables, and two
/// inferred values whose types share nodes.
pub(crate) fn program_source(rng: &mut Rng, tier: Tier) -> String {
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
    for index in 0..3 + rng.below(4) {
        let mut body = String::new();
        type_text(rng, 3, &["'a", "'b"], &nullary, &unary, &mut body);
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
pub(crate) fn operations(rng: &mut Rng, tier: Tier, values: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    let mut operands = 0usize;
    let mut depth = 0u8;
    for _ in 0..4 + rng.below(13) {
        let operand = |rng: &mut Rng| rng.below(operands) as u16;
        let op = if operands == 0 {
            Op::Instance(rng.below(values) as u16)
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
            Op::BeginDef => depth += 1,
            Op::EndDef => depth -= 1,
            _ => {}
        }
        ops.push(op);
    }
    ops
}

/// O(operations + printed nodes²): the old checker's side of a case.
pub(crate) fn run_old(program: &Program, tier: Tier, ops: &[Op]) -> Outcome {
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
    for item in unit.ps_sig.iter() {
        match item {
            SignatureItem::SigValue(_, value) => values.push(value.val_type),
            SignatureItem::SigType(id, declaration, _) => {
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
    let mut operands: Vec<TypeExprRef> = Vec::new();
    for (index, op) in ops.iter().enumerate() {
        match *op {
            Op::Instance(value) => operands.push(ctype::instance(&ctx, values[value as usize])),
            Op::Copy(operand) => operands.push(ctype::instance(&ctx, operands[operand as usize])),
            Op::BeginDef => ctx.begin_def(),
            Op::EndDef => ctx.end_def(),
            Op::Generalize(operand) => ctype::generalize(&ctx, operands[operand as usize]),
            Op::Lower(operand, level) => {
                ctype::update_level(&ctx, base + i32::from(level), operands[operand as usize])
            }
            Op::Unify(left, right) => {
                let mut state = ctype::UnifyState::new();
                state.set_env(&env);
                let result = ctype::unify(
                    &ctx,
                    &mut state,
                    operands[left as usize],
                    operands[right as usize],
                );
                if result.is_err() {
                    return Outcome {
                        failed: Some(index),
                        form: String::new(),
                    };
                }
            }
            Op::Expand(operand) => {
                operands.push(ctype::expand_head(&ctx, &env, operands[operand as usize]))
            }
            Op::Cleanup => ctx.clear_abbrev_memos(),
        }
    }
    let mut form = String::new();
    let mut seen = Vec::new();
    for (index, &operand) in operands.iter().enumerate() {
        let _ = write!(form, "{index} = ");
        old_form(&ctx, base, tier.names(), operand, &mut seen, &mut form);
        form.push('\n');
    }
    Outcome { failed: None, form }
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
    pub roots: Vec<SchemeRoot>,
    pub operands: Vec<Ty>,
    /// First instance of each value, for [`Fault::ReuseInstance`].
    first: Vec<Option<Ty>>,
}

impl New {
    /// O(the unit): convert the program's publication with `from_old`.
    pub(crate) fn convert(program: &Program, tier: Tier) -> New {
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
        // No generated program has an object, a variant row, a universal
        // variable or a package, so the descriptor pools stay empty; the
        // tiers of R3e to R3j fill them with `Extras::from_segment`.
        if tier.memo_aware() {
            checker.types = TypeTable::from_segment(&segment);
        }
        New {
            first: vec![None; roots.len()],
            segment,
            checker,
            tier,
            roots,
            operands: Vec::new(),
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
                    // The old side lowers without an environment
                    // (`ctype::update_level`): no scope can clash.
                    self.checker.lower(ty, level).expect("no scoped type");
                }
            }
            Op::Unify(left, right) => {
                let (left, right) = (self.operands[left as usize], self.operands[right as usize]);
                return self.checker.unify(left, right).map_err(|_| ());
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
        }
        Ok(())
    }

    /// O(printed nodes): the form of every operand; see the module text.
    pub(crate) fn form(&mut self) -> String {
        let mut form = String::new();
        let mut seen = vec![NONE; self.checker.g.nodes.len()];
        let mut count = 0;
        let operands = self.operands.clone();
        for (index, operand) in operands.into_iter().enumerate() {
            let _ = write!(form, "{index} = ");
            self.node_form(operand, &mut seen, &mut count, &mut form);
            form.push('\n');
        }
        form
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
            _ => out.push_str("?unsupported"),
        }
    }
}

/// O(operations + printed nodes): the new graph's side of a case.
pub(crate) fn run_new(program: &Program, tier: Tier, ops: &[Op], fault: Fault) -> Outcome {
    let mut new = New::convert(program, tier);
    for (index, &op) in ops.iter().enumerate() {
        if new.apply(op, fault).is_err() {
            return Outcome {
                failed: Some(index),
                form: String::new(),
            };
        }
    }
    Outcome {
        failed: None,
        form: new.form(),
    }
}

/// Both sides of one case. `Err` is the report a failing test prints: the
/// seed, the program, the operations and both outcomes.
pub(crate) fn compare(
    seed: u64,
    program: &Program,
    tier: Tier,
    ops: &[Op],
    fault: Fault,
) -> Result<Outcome, String> {
    let old = run_old(program, tier, ops);
    let new = run_new(program, tier, ops, fault);
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
}

/// `programs` programs from consecutive seeds, `per_program` operation
/// sequences each; panics with the report of the first mismatch.
pub(crate) fn run_cases(tier: Tier, first_seed: u64, programs: u64, per_program: u64) -> Coverage {
    let mut coverage = Coverage::default();
    for seed in first_seed..first_seed + programs {
        let mut rng = Rng(seed);
        let program = compile(program_source(&mut rng, tier));
        for sequence in 0..per_program {
            // Each sequence has its own seed, printed on failure.
            let case_seed = seed.wrapping_mul(1_000_003).wrapping_add(sequence);
            let mut rng = Rng(case_seed);
            let ops = operations(&mut rng, tier, program.values.len());
            match compare(case_seed, &program, tier, &ops, Fault::None) {
                Ok(outcome) => {
                    coverage.cases += 1;
                    coverage.failures += usize::from(outcome.failed.is_some());
                    coverage.sharing += usize::from(outcome.form.contains('@'));
                    coverage.mixed_levels += usize::from(
                        outcome.form.contains("[G]") && outcome.form.contains("[0]"),
                    );
                }
                Err(report) => panic!("program seed {seed}, sequence {sequence}\n{report}"),
            }
        }
    }
    coverage
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_is_small() {
        assert_eq!(std::mem::size_of::<Op>(), 6);
        assert_eq!(std::mem::size_of::<Fault>(), 1);
        assert_eq!(std::mem::size_of::<Tier>(), 1);
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
}
