//! Tests of slice R4 (CHECKER_REWRITE "R4 as designed").
//!
//! The first part runs today on the old checker and pins what a lookup
//! answers: the programs of [`PROGRAMS`], each with the lines of the
//! canonical signature that show which item a name resolved to and with the
//! warnings its lookups raise. The old checker is driven as a build drives
//! it for `rescript build --check-only`: `driver::compile_source_in_process`
//! on a source text, dependencies compiled the same way and registered in a
//! module registry. Nothing is
//! started at a level or a stamp a compilation would not start at.
//!
//! The second part is the acceptance tests of the build slices, ignored
//! until their slice is built. Each names the `todo!` slices it reaches.

use std::sync::Arc;

use super::bridge::from_old::{Input, from_old};
use super::name_table::Name;
use super::names::{ModuleShape, PathErrorKind, READ};
use super::scope::{
    Binder, BinderKind, DEPRECATED, Found, IMPORTED, Key, MEMBER_DEPRECATED, NONE, Namespace,
    OPEN_OVERRIDE, OPEN_USED, PATTERN, Resolved, ResolvedKind, Scopes, TableId, USED, UnitSource,
    WarningKind,
};
use super::scope_oracle::{Resolver, replay};
use super::scope_trace::{self, Event, Ns};
use super::segment::{
    ChildTable, ExportItem, ExportKind, Range, Segment, SignaturePools, ValueRow,
};
use super::steps;
use crate::cmi::persistent_env::{InMemoryModuleInfo, ModuleRegistry};
use crate::cmi::portable_types::{PortablePersStruct, internalize_pers_struct};
use crate::context::IdGenerator;
use crate::driver::{CompilerOptions, compile_source_in_process};
use crate::types::context::TypeContext;

/// One program the old checker compiles, with what its lookups must answer.
pub(crate) struct Program {
    /// Units the program reads, compiled first, in order: name and source.
    pub deps: &'static [(&'static str, &'static str)],
    pub source: &'static str,
    /// Lines of the canonical signature of the unit (`Case`).
    pub lines: &'static [&'static str],
    /// The message of every warning the compile reports, in order.
    pub warnings: &'static [&'static str],
}

/// The dependency of the programs that read another unit.
const DEP: (&str, &str) = (
    "Dep",
    "module A = {\n  module B = {\n    let v = \"s\"\n  }\n}\nlet x = 1.5\ntype r = {dx: int}\ntype c = Dc\n",
);

/// A later binding hides an earlier one of the same scope.
pub(crate) const SHADOWING: Program = Program {
    deps: &[],
    source: "let x = 1\nlet x = \"s\"\nlet y = x\n",
    lines: &["value y: &0(string)"],
    warnings: &["unused value x."],
};

/// An opened module hides an older local binding, and the lookup that goes
/// through the open reports the shadowing (warning 44).
pub(crate) const OPEN_SHADOWS_A_LOCAL: Program = Program {
    deps: &[],
    source: "let x = 1\nmodule M = {\n  let x = \"s\"\n}\nopen M\nlet y = x\n",
    lines: &["value y: &0(string)"],
    warnings: &["this open statement shadows the value identifier x (which is later used)"],
};

/// A local binding made after the open hides the opened module's member; the
/// open is then unused (warning 33).
pub(crate) const LOCAL_SHADOWS_AN_OPEN: Program = Program {
    deps: &[],
    source: "module M = {\n  let x = \"s\"\n}\nopen M\nlet x = 1\nlet y = x\n",
    lines: &["value y: &0(int)"],
    warnings: &["unused open M."],
};

/// Of two opens the later wins; a name only the earlier has is still found.
pub(crate) const LATER_OPEN_WINS: Program = Program {
    deps: &[],
    source: "module M1 = {\n  let x = \"s\"\n  let only1 = 1\n}\nmodule M2 = {\n  let x = 1.5\n}\nopen M1\nopen M2\nlet y = x\nlet z = only1\n",
    lines: &["value y: &0(float)", "value z: &0(int)"],
    warnings: &["this open statement shadows the value identifier x (which is later used)"],
};

/// One name in five namespaces: the type `t`, the label `t`, the value `t`;
/// the constructor `T` and the module `T`.
pub(crate) const ONE_NAME_IN_EACH_NAMESPACE: Program = Program {
    deps: &[],
    source: "type t = {t: int}\nlet t = {t: 1}\nlet u: t = t\nlet v = t.t\ntype c = T(int)\nmodule T = {\n  let v = 1.5\n}\nlet a = T(1)\nlet b = T.v\n",
    lines: &[
        "value u: &0(t)",
        "value v: &0(int)",
        "value a: &0(c)",
        "value b: &0(float)",
    ],
    warnings: &[],
};

/// A qualified path through two aliases, inside the unit and across units.
pub(crate) const PATH_THROUGH_TWO_ALIASES: Program = Program {
    deps: &[DEP],
    source: "module A = {\n  module B = {\n    let v = \"s\"\n  }\n}\nmodule N = A\nmodule O = N\nlet y = O.B.v\nmodule P = Dep\nmodule Q = P.A\nlet z = Q.B.v\n",
    lines: &[
        "value y: &0(string)",
        "value z: &0(string)",
        "  alias MtaAbsent P.A",
    ],
    warnings: &[],
};

/// A label and a constructor two types share: with an expected type the
/// member of that type is taken (`f`, `h`); without one, the last defined
/// (`g`, `k`).
pub(crate) const TYPE_DIRECTED: Program = Program {
    deps: &[],
    source: "type a = {x: int}\ntype b = {x: string}\nlet f = (r: a) => r.x\nlet g = r => r.x\ntype p = A | B\ntype q = A | C\nlet h = (v: p) =>\n  switch v {\n  | A => 1\n  | B => 2\n  }\nlet k = A\n",
    lines: &[
        "value f: &0((&1(a)) => &2(int))",
        "value g: &0((&1(b)) => &2(string))",
        "value h: &0((&1(p)) => &2(int))",
        "value k: &0(q)",
    ],
    warnings: &[],
};

/// An opened unit whose member a local binding hides.
pub(crate) const OPENED_UNIT_UNUSED: Program = Program {
    deps: &[DEP],
    source: "open Dep\nlet x = 1\nlet y = x\n",
    lines: &["value y: &0(int)"],
    warnings: &["unused open Dep."],
};

/// A constructor and a label found through an open that hides older ones
/// (warning 45, once per name).
pub(crate) const OPEN_SHADOWS_MEMBERS: Program = Program {
    deps: &[],
    source: "type t = A | B\ntype r = {lbl: int}\nmodule M = {\n  type t2 = A | C\n  type r2 = {lbl: string}\n}\nopen M\nlet k = A\nlet l = r => r.lbl\n",
    lines: &["value k: &0(M.t2)", "value l: &0((&1(M.r2)) => &2(string))"],
    warnings: &[
        "this open statement shadows the constructor A (which is later used)",
        "this open statement shadows the label lbl (which is later used)",
    ],
};

/// Two opens, one used through a type and one through a value.
pub(crate) const TWO_OPENS_BOTH_USED: Program = Program {
    deps: &[],
    source: "module M = {\n  let x = 1\n  type t = int\n}\nmodule N = {\n  let x = 2\n}\nopen M\nopen N\nlet y: t = x\n",
    lines: &["value y: &0(M.t)"],
    warnings: &["this open statement shadows the value identifier x (which is later used)"],
};

/// Opens inside expressions: a local open hides a binding of an enclosing
/// function and ends with its block; a unit opened in a block.
pub(crate) const LOCAL_OPENS: Program = Program {
    deps: &[DEP],
    source: "module M = {\n  let x = \"s\"\n}\nlet f = () => {\n  let x = 1\n  let g = () => {\n    open M\n    x\n  }\n  (x, g())\n}\nlet h = {\n  open Dep\n  x\n}\n",
    lines: &[
        "value f: &0((&1(unit)) => &2(tuple(&3(int), &4(string))))",
        "value h: &0(float)",
    ],
    warnings: &["this open statement shadows the value identifier x (which is later used)"],
};

/// A deprecated type and value, read through a path and through an alias:
/// one warning per use, at the use.
pub(crate) const DEPRECATED_USES: Program = Program {
    deps: &[],
    source: "module M = {\n  @deprecated(\"no\") type t = int\n  @deprecated(\"gone\") let v = 1\n}\nlet a: M.t = M.v\nmodule N = M\nlet b = N.v\n",
    lines: &["value a: &0(M.t)", "value b: &0(int)"],
    warnings: &["deprecated: M.t", "deprecated: M.v", "deprecated: N.v"],
};

/// The unused-declaration warnings: all are reported at the end of the unit,
/// in declaration order.
pub(crate) const UNUSED_DECLARATIONS: Program = Program {
    deps: &[],
    source: "module M: {\n  let v: int\n} = {\n  type t = A | B\n  type u = int\n  type r = {lbl: int}\n  let unused = 1\n  let v = 2\n}\nlet f = a => {\n  let local = 1\n  a\n}\n",
    lines: &["    value v: &0(int)"],
    warnings: &[
        "unused type t.",
        "unused constructor A.",
        "unused constructor B.",
        "unused type u.",
        "unused type r.",
        "unused value unused.",
        "unused variable local.",
    ],
};

pub(crate) const PROGRAMS: &[&Program] = &[
    &SHADOWING,
    &OPEN_SHADOWS_A_LOCAL,
    &LOCAL_SHADOWS_AN_OPEN,
    &LATER_OPEN_WINS,
    &ONE_NAME_IN_EACH_NAMESPACE,
    &PATH_THROUGH_TWO_ALIASES,
    &TYPE_DIRECTED,
    &OPENED_UNIT_UNUSED,
    &OPEN_SHADOWS_MEMBERS,
    &TWO_OPENS_BOTH_USED,
    &LOCAL_OPENS,
    &DEPRECATED_USES,
    &UNUSED_DECLARATIONS,
];

/// What the old checker did with one program.
pub(crate) struct Old {
    /// The canonical signature of the unit.
    pub signature: String,
    /// The warning reports, as the build prints them.
    pub warnings: String,
    /// The environment's events while the unit was compiled (dependencies
    /// are compiled before the capture starts).
    pub events: Vec<Event>,
    /// The published dependencies, by name, for conversion to segments.
    pub deps: Vec<(&'static str, Arc<PortablePersStruct>)>,
}

/// The warnings a project enables by default (rewatch `config.rs`), so that
/// the pinned warnings are those a build prints.
fn options() -> CompilerOptions {
    CompilerOptions {
        // A check-only build: type checking, warnings and publication, no
        // JavaScript (which would need the dependency's output path).
        check_only: true,
        nopervasives: true,
        warning_specs: vec!["+a-4-9-20-40-41-42-50-61-102-70".to_string()],
        ..Default::default()
    }
}

/// O(the program): compile the dependencies, then the unit `Case` under a
/// capture of the environment's events. Panics with the source when the old
/// checker rejects the program.
pub(crate) fn old_checker(program: &Program) -> Old {
    let options = options();
    let mut registry = ModuleRegistry::new();
    let mut deps = Vec::new();
    for &(name, source) in program.deps {
        let file = format!("{name}.res");
        let compiled =
            compile_source_in_process(source, &file, name, &options, &registry, false, None)
                .unwrap_or_else(|error| panic!("dependency {name} does not compile: {error:?}"));
        let unit = compiled.pers_struct.expect("published dependency");
        registry.register_module_arc(
            name,
            unit.clone(),
            InMemoryModuleInfo::new(file.into(), true, Default::default(), false),
        );
        deps.push((name, unit));
    }
    let (compiled, events) = scope_trace::capture(|| {
        compile_source_in_process(
            program.source,
            "Case.res",
            "Case",
            &options,
            &registry,
            false,
            None,
        )
    });
    let compiled = compiled
        .unwrap_or_else(|error| panic!("program does not compile: {error:?}\n{}", program.source));
    let unit = compiled.pers_struct.expect("published signature");
    let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
    let old = internalize_pers_struct(unit.clone(), &ctx);
    let signature =
        crate::types::canonical_sig::canonical_signature(&ctx, "Case", &old.ps_sig, None, None);
    Old {
        signature,
        warnings: compiled.warnings,
        events,
        deps,
    }
}

/// The messages of `Program::warnings` found in `text`, in the order of
/// their first occurrence, and the number of reports in `text`.
fn reported(program: &Program, text: &str) -> (Vec<&'static str>, usize) {
    let mut found: Vec<(usize, &'static str)> = program
        .warnings
        .iter()
        .filter_map(|&message| text.find(message).map(|at| (at, message)))
        .collect();
    found.sort();
    (
        found.into_iter().map(|(_, message)| message).collect(),
        text.matches("Warning number").count(),
    )
}

// ---------------------------------------------------------------------------
// On the old checker, today: the evidence of decisions 1, 2 and 4.
// ---------------------------------------------------------------------------

/// Decision 1. Every program resolves its names as pinned: the lines of the
/// canonical signature name the item each lookup found.
#[test]
fn old_checker_lookups_are_pinned() {
    for program in PROGRAMS {
        let old = old_checker(program);
        for line in program.lines {
            assert!(
                old.signature.lines().any(|found| found == *line),
                "missing line\n{line}\nin\n{}\nof\n{}",
                old.signature,
                program.source
            );
        }
    }
}

/// Decision 2. Every program reports exactly the pinned warnings, in the
/// pinned order: the lookup warnings (3, 44, 45) where the walk reaches the
/// use, the unused warnings (26, 32, 33, 34, 37) at the end of the unit.
#[test]
fn old_checker_lookup_warnings_are_pinned() {
    for program in PROGRAMS {
        let old = old_checker(program);
        let (found, reports) = reported(program, &old.warnings);
        assert_eq!(
            found, program.warnings,
            "warnings of\n{}\nare\n{}",
            program.source, old.warnings
        );
        assert_eq!(
            reports,
            program.warnings.len(),
            "warnings of\n{}\nare\n{}",
            program.source,
            old.warnings
        );
    }
}

/// An open whose constructor and label hide older ones of the same type
/// (`type t2 = t = A | B`): no shadowing is reported, where
/// `OPEN_SHADOWS_MEMBERS`, with two different types, reports both
/// (`check_shadowing`, compiler/ml/env.ml:415-420). Not in `PROGRAMS`: the
/// replay counts are pinned on those thirteen.
const OPEN_SHADOWS_THE_SAME_TYPE: Program = Program {
    deps: &[],
    source: "type t = A | B\ntype r = {lbl: int}\nmodule M = {\n  type t2 = t = A | B\n  type r2 = r = {lbl: int}\n}\nopen M\nlet k = A\nlet l = v => v.lbl\n",
    lines: &[],
    warnings: &[],
};

/// Decision 2, constructors and labels: the shadowing warning of an open
/// depends on the two result types, not only on the names.
#[test]
fn old_checker_open_of_the_same_type_reports_no_shadowing() {
    let old = old_checker(&OPEN_SHADOWS_THE_SAME_TYPE);
    let (_, reports) = reported(&OPEN_SHADOWS_THE_SAME_TYPE, &old.warnings);
    assert_eq!(reports, 0, "warnings are\n{}", old.warnings);
    let differ = old_checker(&OPEN_SHADOWS_MEMBERS);
    let (found, reports) = reported(&OPEN_SHADOWS_MEMBERS, &differ.warnings);
    assert_eq!((found.len(), reports), (2, 2));
}

/// Decision 4. The trace of a program is not empty and names what the
/// program binds: the capture sees the compile of the unit.
#[test]
fn the_old_environment_reports_bindings_opens_and_lookups() {
    let old = old_checker(&OPEN_SHADOWS_A_LOCAL);
    let bound = |ns: Ns, name: &str| {
        old.events
            .iter()
            .filter(|event| matches!(event, Event::Bind { ns: n, name: m, .. } if *n == ns && *m == name))
            .count()
    };
    assert!(bound(Ns::Value, "x") >= 2, "the unit's `x` and `M.x`");
    assert!(bound(Ns::Module, "M") >= 1);
    assert!(bound(Ns::Value, "y") >= 1);
    let layers: Vec<&Vec<scope_trace::Member>> = old
        .events
        .iter()
        .filter_map(|event| match event {
            Event::Open { members, .. } => Some(members),
            _ => None,
        })
        .collect();
    assert!(
        layers
            .iter()
            .any(|members| members.iter().any(|m| (m.0, m.1) == (Ns::Value, "x"))),
        "{layers:?}"
    );
    assert!(
        old.events.iter().any(|event| matches!(
            event,
            Event::Lookup { ns: Ns::Value, name, found, .. } if name == "x" && found.len() == 1
        )),
        "the use of `x` is a lookup that finds one binding"
    );
    // Nothing is recorded outside a capture.
    assert!(!scope_trace::on());
}

// ---------------------------------------------------------------------------
// Acceptance tests of the build slices. Helpers first; they call only what
// the slice named in their doc comment builds.
// ---------------------------------------------------------------------------

/// R4a. Intern `text` and make its key.
fn key(s: &mut Scopes, text: &str, ns: Namespace) -> Key {
    Key::new(s.names.intern(text), ns)
}

/// R4a. The kind the tests give a binder of a namespace.
fn kind_of(ns: Namespace) -> BinderKind {
    match ns {
        Namespace::Value => BinderKind::Let,
        Namespace::Type => BinderKind::Type,
        Namespace::Module => BinderKind::Module,
        Namespace::ModuleType => BinderKind::ModuleType,
        Namespace::Constructor => BinderKind::Constructor,
        Namespace::Label => BinderKind::Label,
    }
}

/// R4a. A binder that is not in scope yet; its payload is `payload`.
fn push(s: &mut Scopes, text: &str, ns: Namespace, payload: u32) -> Binder {
    let key = key(s, text, ns);
    s.binders.push(key, payload, 0, kind_of(ns))
}

/// R4a, R4b. A binder in scope.
fn bind(s: &mut Scopes, text: &str, ns: Namespace, payload: u32) -> Binder {
    let binder = push(s, text, ns, payload);
    s.bind(binder);
    binder
}

/// R4a, R4b. A structure with scope 0 entered, as a unit starts.
fn unit_scopes() -> Scopes {
    let mut s = Scopes::new();
    assert_eq!(s.enter(), 0);
    s
}

/// R4a to R4c. A local module `name` whose members are `members`, bound in
/// the current scope as the walk will bind a structure: a scope for the
/// body, its bindings, the table sealed, the scope left, the module bound
/// with the table as payload.
fn module(s: &mut Scopes, name: &str, members: &[(&str, Namespace, u32)]) -> (Binder, TableId) {
    let from = s.log_mark();
    s.enter();
    for &(member, ns, payload) in members {
        bind(s, member, ns, payload);
    }
    let table = s.seal(from);
    s.leave();
    (bind(s, name, Namespace::Module, table.0), table)
}

/// The binder a lookup found.
fn binder_of(found: Option<Found>) -> Binder {
    match found.expect("found").item.kind() {
        ResolvedKind::Binder(binder) => binder,
        other => panic!("not a binder: {other:?}"),
    }
}

/// O(the unit): a published unit of the old checker as a segment, converted
/// as `bridge::from_old::published_segment` converts a dependency.
fn segment_of(name: &str, unit: &Arc<PortablePersStruct>) -> Arc<Segment> {
    let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
    let segment = unit
        .with_published_graph(&ctx, |published| {
            from_old(Input::new(
                &published.graph,
                &published.signature,
                name,
                None,
                &published.names,
                [0; 32],
            ))
        })
        .expect("published graph");
    Arc::new(segment)
}

/// O(the source): compile one unit with the old checker, as a build does,
/// and convert it.
fn compiled_segment(name: &'static str, source: &'static str) -> Arc<Segment> {
    let file = format!("{name}.res");
    let compiled = compile_source_in_process(
        source,
        &file,
        name,
        &options(),
        &ModuleRegistry::new(),
        false,
        None,
    )
    .unwrap_or_else(|error| panic!("{name} does not compile: {error:?}"));
    segment_of(name, &compiled.pers_struct.expect("published unit"))
}

/// A [`UnitSource`] over a list, counting how often it is asked.
struct Units {
    list: Vec<(&'static str, Arc<Segment>)>,
    asked: u32,
}

impl UnitSource for Units {
    fn segment(&mut self, name: &str) -> Option<Arc<Segment>> {
        self.asked += 1;
        self.list
            .iter()
            .find(|(unit, _)| *unit == name)
            .map(|(_, segment)| segment.clone())
    }
}

/// The text of a segment string.
fn segment_text(segment: &Segment, index: u32) -> &str {
    let range = segment.signature.strings[index as usize];
    std::str::from_utf8(
        &segment.signature.bytes[range.start as usize..(range.start + range.len) as usize],
    )
    .unwrap()
}

/// A segment with `n` exported values `v0`, `v1`, ... and nothing else: the
/// export table, the string pool and one value row per item.
fn wide_segment(n: u32) -> Arc<Segment> {
    let mut bytes = Vec::new();
    let mut strings = Vec::new();
    for i in 0..n {
        let text = format!("v{i}");
        strings.push(Range {
            start: bytes.len() as u32,
            len: text.len() as u32,
        });
        bytes.extend_from_slice(text.as_bytes());
    }
    let value = ValueRow {
        ty: 0,
        primitive: NONE,
        attributes: Range { start: 0, len: 0 },
        loc: 0,
        path: 0,
    };
    Arc::new(Segment {
        items: (0..n)
            .map(|i| ExportItem {
                name: i,
                payload: i,
                kind: ExportKind::Value,
            })
            .collect(),
        children: Box::new([ChildTable { start: 0, len: n }]),
        signature: SignaturePools {
            bytes: bytes.into_boxed_slice(),
            strings: strings.into_boxed_slice(),
            values: vec![value; n as usize].into_boxed_slice(),
            ..SignaturePools::default()
        },
        ..Segment::default()
    })
}

// ----- R4a: names and binders -----

/// Reaches: R4a.
#[test]
fn names_are_interned_once_and_dense() {
    let mut s = Scopes::new();
    let a = s.names.intern("alpha");
    assert_eq!(s.names.intern("alpha"), a);
    let b = s.names.intern("beta");
    assert_ne!(a, b);
    assert_eq!((s.names.text(a), s.names.text(b)), ("alpha", "beta"));
    assert_eq!(s.names.find("alpha"), Some(a));
    assert_eq!(s.names.find("gamma"), None);
    assert_eq!(s.names.len(), 2);
    for i in 0..10_000 {
        let name = s.names.intern(&format!("n{i}"));
        assert_eq!(name, Name(2 + i));
    }
    assert_eq!(s.names.len(), 10_002);
    assert_eq!(s.names.text(Name(10_001)), "n9999");
    assert_eq!(s.names.intern(""), Name(10_002));
}

/// Reaches: R4a. Pushing 10,000 binders is 10,000 steps, and every array
/// has the row.
#[test]
fn ten_thousand_binders_are_one_step_each() {
    let mut s = Scopes::new();
    let key = key(&mut s, "x", Namespace::Value);
    let count = steps::scope(|| {
        for i in 0..10_000 {
            assert_eq!(
                s.binders.push(key, i, i + 1, BinderKind::Variable),
                Binder(i)
            );
        }
    });
    assert_eq!(count, 10_000);
    assert_eq!(s.binders.len(), 10_000);
    let b = 1234usize;
    assert_eq!(
        (
            s.binders.key[b],
            s.binders.payload[b],
            s.binders.loc[b],
            s.binders.previous[b],
            s.binders.kind[b],
            s.binders.used[b]
        ),
        (key.0, 1234, 1235, NONE, BinderKind::Variable, 0)
    );
}

// ----- R4b: scopes and the undo log -----

/// Reaches: R4a, R4b. The task text's bound: 10,000 bindings in one scope
/// and leaving it is at most 3 steps a binding (push, bind, undo).
#[test]
fn ten_thousand_bindings_then_leaving_is_three_steps_a_binding() {
    let mut s = unit_scopes();
    let keys: Vec<Key> = (0..10_000)
        .map(|i| key(&mut s, &format!("n{i}"), Namespace::Value))
        .collect();
    let mut binders = Vec::new();
    let count = steps::scope(|| {
        s.enter();
        for &key in &keys {
            let binder = s.binders.push(key, 0, 0, BinderKind::Let);
            s.bind(binder);
            binders.push(binder);
        }
        s.leave();
    });
    assert!(count <= 3 * 10_000, "{count}");
    assert_eq!(s.current, 0);
    assert!(s.log.is_empty());
    for &key in &keys {
        assert_eq!(s.head(key), NONE);
    }
    // The same name 10,000 times: leaving restores the binding before.
    let x = bind(&mut s, "x", Namespace::Value, 0);
    let count = steps::scope(|| {
        s.enter();
        for _ in 0..10_000 {
            bind(&mut s, "x", Namespace::Value, 0);
        }
        s.leave();
    });
    assert!(count <= 3 * 10_000, "{count}");
    assert_eq!(
        s.head(Key::new(s.names.find("x").unwrap(), Namespace::Value)),
        x.0
    );
}

/// Reaches: R4a, R4b. The task text's bound: a lookup under 10,000 nested
/// scopes is 1 step, whichever scope bound the name.
#[test]
fn a_lookup_under_ten_thousand_nested_scopes_is_one_step() {
    let mut s = unit_scopes();
    let outer = bind(&mut s, "outer", Namespace::Value, 0);
    let mut middle = Binder(NONE);
    for depth in 0..10_000 {
        assert_eq!(s.enter(), depth + 1);
        let binder = bind(&mut s, &format!("n{depth}"), Namespace::Value, 0);
        if depth == 5_000 {
            middle = binder;
        }
    }
    let outer_key = key(&mut s, "outer", Namespace::Value);
    let middle_key = key(&mut s, "n5000", Namespace::Value);
    let missing_key = key(&mut s, "missing", Namespace::Value);
    for (key, expected) in [
        (outer_key, outer.0),
        (middle_key, middle.0),
        (missing_key, NONE),
    ] {
        let mut found = 0;
        assert_eq!(steps::scope(|| found = s.head(key)), 1);
        assert_eq!(found, expected);
    }
    assert_eq!(s.scopes[10_000].parent, 9_999);
    assert_eq!(s.scopes[1].first_binder, 1);
    let count = steps::scope(|| {
        for _ in 0..10_000 {
            s.leave();
        }
    });
    assert_eq!(count, 10_000, "one undo a binding");
    assert_eq!(
        (s.current, s.head(middle_key), s.head(outer_key)),
        (0, NONE, outer.0)
    );
    // Rows of left scopes stay: a remembered index keeps its meaning.
    assert_eq!(s.scopes.len(), 10_001);
}

/// Reaches: R4a, R4b. Shadowing (pinned on the old checker by `SHADOWING`):
/// the later binding is found, the earlier one is its `previous`, leaving
/// restores it; and one name in two namespaces is two keys (pinned by
/// `ONE_NAME_IN_EACH_NAMESPACE`).
#[test]
fn shadowing_and_namespaces() {
    let mut s = unit_scopes();
    let first = bind(&mut s, "x", Namespace::Value, 1);
    let second = bind(&mut s, "x", Namespace::Value, 2);
    let x = key(&mut s, "x", Namespace::Value);
    assert_eq!(s.head(x), second.0);
    assert_eq!(s.binders.previous[second.0 as usize], first.0);
    s.enter();
    let inner = bind(&mut s, "x", Namespace::Value, 3);
    assert_eq!(s.head(x), inner.0);
    s.leave();
    assert_eq!(s.head(x), second.0);

    let ty = bind(&mut s, "t", Namespace::Type, 0);
    let label = bind(&mut s, "t", Namespace::Label, 0);
    let value = bind(&mut s, "t", Namespace::Value, 0);
    let constructor = bind(&mut s, "T", Namespace::Constructor, 0);
    let module = bind(&mut s, "T", Namespace::Module, 0);
    for (text, ns, expected) in [
        ("t", Namespace::Type, ty),
        ("t", Namespace::Label, label),
        ("t", Namespace::Value, value),
        ("T", Namespace::Constructor, constructor),
        ("T", Namespace::Module, module),
    ] {
        let key = key(&mut s, text, ns);
        assert_eq!(s.head(key), expected.0);
        assert_eq!(s.binders.previous[expected.0 as usize], NONE);
    }
    let missing = key(&mut s, "t", Namespace::ModuleType);
    assert_eq!(s.head(missing), NONE);
}

/// Reaches: R4a, R4b. A unit starts from the frozen prefix.
#[test]
fn reset_returns_to_the_frozen_prefix() {
    let mut s = unit_scopes();
    let int = bind(&mut s, "int", Namespace::Type, 0);
    s.freeze();
    let frozen = s.frozen;
    assert_eq!((frozen.binders, frozen.scopes, frozen.log), (1, 1, 1));
    for _ in 0..2 {
        s.enter();
        bind(&mut s, "int", Namespace::Type, 1);
        bind(&mut s, "x", Namespace::Value, 0);
        s.enter();
        s.reset();
        assert_eq!(
            (s.current, s.binders.len(), s.scopes.len(), s.log.len()),
            (0, 1, 1, 1)
        );
        assert_eq!(s.frozen, frozen);
        let int_key = key(&mut s, "int", Namespace::Type);
        let x_key = key(&mut s, "x", Namespace::Value);
        assert_eq!((s.head(int_key), s.head(x_key)), (int.0, NONE));
    }
}

// ----- R4c: member tables, layers, lookup -----

/// Reaches: R4a, R4c. A table of 10,000 members is built in 10,000 steps
/// and searched in at most floor(log2 10,000) + 1 = 14 comparisons.
#[test]
fn a_table_of_ten_thousand_members_is_searched_in_fourteen_steps() {
    let mut s = unit_scopes();
    let mut members = Vec::new();
    // Given in an order that is not the key order.
    for i in (0..10_000u32).rev() {
        let binder = push(&mut s, &format!("m{i}"), Namespace::Value, i);
        members.push((Key(s.binders.key[binder.0 as usize]), binder));
    }
    let mut table = TableId(NONE);
    let count = steps::scope(|| table = s.table_from(&members));
    assert_eq!(count, 10_000);
    assert_eq!(table.0 & IMPORTED, 0);
    assert_eq!(s.tables[table.0 as usize].len, 10_000);
    for &(key, binder) in &members {
        let mut row = None;
        let probes = steps::scope(|| row = s.search(table, key));
        assert!(probes <= 14, "{probes}");
        assert_eq!(s.member(table, row.unwrap()).target, binder.0);
    }
    let missing = key(&mut s, "missing", Namespace::Value);
    assert_eq!(s.search(table, missing), None);
    let wrong_namespace = key(&mut s, "m7", Namespace::Type);
    assert_eq!(s.search(table, wrong_namespace), None);
    let empty = s.table_from(&[]);
    assert_eq!(s.search(empty, missing), None);
}

/// Reaches: R4a, R4b, R4c. The task text's bound: a lookup under 10 opened
/// modules probes at most 10 layers and stops at the first younger hit.
/// Every table here has one member, so a probe is one comparison and the
/// counts are exact: 1 for the head and 1 a layer probed.
#[test]
fn a_lookup_under_ten_opened_modules() {
    let mut s = unit_scopes();
    let old_x = bind(&mut s, "x", Namespace::Value, 0);
    let mut layer_y = [NONE; 10];
    for i in 0..10u32 {
        // Layers 2 and 7 have `y`; the others one name of their own.
        let member = if i == 2 || i == 7 {
            "y".to_string()
        } else {
            format!("m{i}")
        };
        let binder = push(&mut s, &member, Namespace::Value, i);
        layer_y[i as usize] = binder.0;
        let table = s.table_from(&[(Key(s.binders.key[binder.0 as usize]), binder)]);
        assert_eq!(s.open(table, 0, 0, 0), i);
    }
    let find = |s: &Scopes, key: Key| {
        let mut found = None;
        let count = steps::scope(|| found = s.find(key));
        (found, count)
    };
    // In no layer and not bound: every layer is probed.
    let z = key(&mut s, "z", Namespace::Value);
    assert_eq!(find(&s, z), (None, 11));
    // In layers 7 and 2: the walk stops at layer 7, the younger.
    let y = key(&mut s, "y", Namespace::Value);
    let (found, count) = find(&s, y);
    assert_eq!(count, 4, "the head, then layers 9, 8, 7");
    assert_eq!(
        found,
        Some(Found {
            item: Resolved::binder(Binder(layer_y[7])),
            layer: 7
        })
    );
    // Bound before every open and in no layer: all ten are probed.
    let x = key(&mut s, "x", Namespace::Value);
    assert_eq!(
        find(&s, x),
        (
            Some(Found {
                item: Resolved::binder(old_x),
                layer: NONE
            }),
            11
        )
    );
    // The only member of the innermost layer: one probe.
    let m9 = key(&mut s, "m9", Namespace::Value);
    assert_eq!(find(&s, m9).1, 2);
    // A binding younger than every layer: no layer is probed.
    s.enter();
    let young_y = bind(&mut s, "y", Namespace::Value, 0);
    assert_eq!(
        find(&s, y),
        (
            Some(Found {
                item: Resolved::binder(young_y),
                layer: NONE
            }),
            1
        )
    );
    // A layer opened in the inner scope hides it again, and ends with the scope.
    let inner = push(&mut s, "y", Namespace::Value, 0);
    let table = s.table_from(&[(y, inner)]);
    let open = s.open(table, 0, 0, 0);
    assert_eq!(
        find(&s, y),
        (
            Some(Found {
                item: Resolved::binder(inner),
                layer: open
            }),
            2
        )
    );
    s.leave();
    assert_eq!(
        find(&s, y).0,
        Some(Found {
            item: Resolved::binder(Binder(layer_y[7])),
            layer: 7
        })
    );
    // A wide layer costs its search, not its size: 1 + at most 14.
    let mut members = Vec::new();
    for i in 0..10_000u32 {
        let binder = push(&mut s, &format!("w{i}"), Namespace::Value, i);
        members.push((Key(s.binders.key[binder.0 as usize]), binder));
    }
    let wide = s.table_from(&members);
    s.open(wide, 0, 0, 0);
    let w = key(&mut s, "w7777", Namespace::Value);
    let (found, count) = find(&s, w);
    assert!(found.is_some() && count <= 15, "{count}");
}

/// Reaches: R4a, R4b, R4c. `OPEN_SHADOWS_A_LOCAL`, `LOCAL_SHADOWS_AN_OPEN`
/// and `LATER_OPEN_WINS` on the new structure, with the answers the old
/// checker is pinned to.
#[test]
fn an_open_shadows_a_local_and_a_local_shadows_an_open() {
    // let x = 1; module M = { let x = "s" }; open M; let y = x
    let mut s = unit_scopes();
    let local = bind(&mut s, "x", Namespace::Value, 0);
    let (_, m) = module(&mut s, "M", &[("x", Namespace::Value, 0)]);
    let x = key(&mut s, "x", Namespace::Value);
    assert_eq!(
        binder_of(s.find(x)),
        local,
        "M's `x` is not in scope before the open"
    );
    let open = s.open(m, 0, 0, 0);
    let found = s.find(x).unwrap();
    let member = Binder(s.member(m, s.search(m, x).unwrap()).target);
    assert_eq!(
        found,
        Found {
            item: Resolved::binder(member),
            layer: open
        }
    );
    assert_ne!(member, local);
    assert_eq!(
        s.find_below(x, open),
        Some(Found {
            item: Resolved::binder(local),
            layer: NONE
        })
    );

    // module M = { let x = "s" }; open M; let x = 1; let y = x
    let mut s = unit_scopes();
    let (_, m) = module(&mut s, "M", &[("x", Namespace::Value, 0)]);
    let open = s.open(m, 0, 0, 0);
    let local = bind(&mut s, "x", Namespace::Value, 0);
    let x = key(&mut s, "x", Namespace::Value);
    assert_eq!(
        s.find(x),
        Some(Found {
            item: Resolved::binder(local),
            layer: NONE
        })
    );
    assert_eq!(
        s.find_below(x, open),
        None,
        "nothing older than the open has `x`"
    );

    // open M1; open M2: the later wins; a name only M1 has is found there.
    let mut s = unit_scopes();
    let (_, m1) = module(
        &mut s,
        "M1",
        &[("x", Namespace::Value, 0), ("only1", Namespace::Value, 0)],
    );
    let (_, m2) = module(&mut s, "M2", &[("x", Namespace::Value, 0)]);
    let open1 = s.open(m1, 0, 0, 0);
    let open2 = s.open(m2, 0, 0, 0);
    let x = key(&mut s, "x", Namespace::Value);
    let only1 = key(&mut s, "only1", Namespace::Value);
    assert_eq!(s.find(x).unwrap().layer, open2);
    assert_eq!(s.find(only1).unwrap().layer, open1);
    assert_eq!(s.find_below(x, open2).unwrap().layer, open1);
    assert_eq!(s.find_below(x, open1), None);
}

/// Reaches: R4a, R4b, R4c. A sealed structure lists the last binding of a
/// value, type or module name and every constructor and label, the younger
/// first; bindings of scopes already left are not members.
#[test]
fn seal_lists_what_a_structure_exports() {
    let mut s = unit_scopes();
    let from = s.log_mark();
    s.enter();
    bind(&mut s, "x", Namespace::Value, 1);
    // An item of the structure enters a scope for what follows it.
    s.enter();
    let x2 = bind(&mut s, "x", Namespace::Value, 2);
    let a1 = bind(&mut s, "A", Namespace::Constructor, 1);
    let t = bind(&mut s, "t", Namespace::Type, 0);
    // A scope inside an expression: entered and left before the seal.
    s.enter();
    bind(&mut s, "hidden", Namespace::Value, 0);
    s.leave();
    let a2 = bind(&mut s, "A", Namespace::Constructor, 2);
    let mut count = 0;
    let mut table = TableId(NONE);
    count += steps::scope(|| table = s.seal(from));
    assert_eq!(count, 5, "one step a log entry since the mark");
    s.leave();
    s.leave();
    assert_eq!(s.tables[table.0 as usize].len, 4);
    let x = key(&mut s, "x", Namespace::Value);
    let a = key(&mut s, "A", Namespace::Constructor);
    let t_key = key(&mut s, "t", Namespace::Type);
    let hidden = key(&mut s, "hidden", Namespace::Value);
    assert_eq!(s.member(table, s.search(table, x).unwrap()).target, x2.0);
    assert_eq!(s.member(table, s.search(table, t_key).unwrap()).target, t.0);
    assert_eq!(s.search(table, hidden), None);
    let first = s.search(table, a).unwrap();
    assert_eq!(
        (
            s.member(table, first).target,
            s.member(table, first + 1).target
        ),
        (a2.0, a1.0)
    );
    assert_eq!(
        s.head(x),
        NONE,
        "the members are out of scope after the structure"
    );
}

/// Reaches: R4a, R4b, R4c. Candidates of a constructor name, innermost
/// first: a younger binding, the opened module's two (in its order), the
/// older binding (`TycompTbl.find_all`; the old checker's order is checked
/// on real traces by the oracle).
#[test]
fn candidates_are_innermost_first() {
    let mut s = unit_scopes();
    let older = bind(&mut s, "A", Namespace::Constructor, 0);
    let (_, m) = module(
        &mut s,
        "M",
        &[
            ("A", Namespace::Constructor, 1),
            ("A", Namespace::Constructor, 2),
        ],
    );
    let a = key(&mut s, "A", Namespace::Constructor);
    let first = s.search(m, a).unwrap();
    let (m_young, m_old) = (s.member(m, first).target, s.member(m, first + 1).target);
    assert_eq!(
        (
            s.binders.payload[m_young as usize],
            s.binders.payload[m_old as usize]
        ),
        (2, 1)
    );
    let open = s.open(m, 0, 0, 0);
    let younger = bind(&mut s, "A", Namespace::Constructor, 3);
    let mut out = Vec::with_capacity(8);
    let count = steps::scope(|| s.candidates(a, &mut out));
    let expected = [
        Found {
            item: Resolved::binder(younger),
            layer: NONE,
        },
        Found {
            item: Resolved::binder(Binder(m_young)),
            layer: open,
        },
        Found {
            item: Resolved::binder(Binder(m_old)),
            layer: open,
        },
        Found {
            item: Resolved::binder(older),
            layer: NONE,
        },
    ];
    assert_eq!(out, expected);
    assert!(
        count <= 4 + 2,
        "4 candidates and one search of a 2-member table: {count}"
    );
    assert_eq!(s.find(a), Some(expected[0]));
    // 10,000 bindings of one name: one step a candidate.
    let mut s = unit_scopes();
    for _ in 0..10_000 {
        bind(&mut s, "A", Namespace::Constructor, 0);
    }
    let a = key(&mut s, "A", Namespace::Constructor);
    let mut out = Vec::with_capacity(10_000);
    assert_eq!(steps::scope(|| s.candidates(a, &mut out)), 10_000);
    assert_eq!(out.len(), 10_000);
    assert_eq!(out[0].item, Resolved::binder(Binder(9_999)));
}

/// [`Scopes`] as a resolver of the oracle. An item is a binder's payload.
struct OnScopes {
    scopes: Scopes,
    out: Vec<Found>,
}

fn namespace(ns: Ns) -> Namespace {
    match ns {
        Ns::Value => Namespace::Value,
        Ns::Type => Namespace::Type,
        Ns::Module => Namespace::Module,
        Ns::ModuleType => Namespace::ModuleType,
        Ns::Constructor => Namespace::Constructor,
        Ns::Label => Namespace::Label,
    }
}

impl OnScopes {
    fn item(&self, found: Found) -> u32 {
        match found.item.kind() {
            ResolvedKind::Binder(binder) => self.scopes.binders.payload[binder.0 as usize],
            other => panic!("the replay binds nothing imported: {other:?}"),
        }
    }
}

impl Resolver for OnScopes {
    fn enter(&mut self) {
        self.scopes.enter();
    }

    fn leave(&mut self) {
        self.scopes.leave();
    }

    fn bind(&mut self, ns: Ns, name: &str, item: u32) {
        bind(&mut self.scopes, name, namespace(ns), item);
    }

    fn open(&mut self, members: &[(Ns, &str, u32)]) {
        let rows: Vec<(Key, Binder)> = members
            .iter()
            .map(|&(ns, name, item)| {
                let binder = push(&mut self.scopes, name, namespace(ns), item);
                (Key(self.scopes.binders.key[binder.0 as usize]), binder)
            })
            .collect();
        let table = self.scopes.table_from(&rows);
        self.scopes.open(table, 0, 0, 0);
    }

    fn first(&mut self, ns: Ns, name: &str) -> Option<u32> {
        let key = key(&mut self.scopes, name, namespace(ns));
        self.scopes.find(key).map(|found| self.item(found))
    }

    fn all(&mut self, ns: Ns, name: &str, out: &mut Vec<u32>) {
        let key = key(&mut self.scopes, name, namespace(ns));
        self.out.clear();
        self.scopes.candidates(key, &mut self.out);
        out.extend(self.out.iter().map(|&found| self.item(found)));
    }
}

/// Reaches: R4a, R4b, R4c. The oracle of decision 4 on the new structure:
/// every lookup by name the old environment made while it checked the
/// pinned programs, replayed on `Scopes`, finds the same item.
#[test]
fn scopes_answer_what_the_old_environment_answered() {
    for program in PROGRAMS {
        let old = old_checker(program);
        let mut resolver = OnScopes {
            scopes: Scopes::new(),
            out: Vec::new(),
        };
        let done = replay(&old.events, &mut resolver)
            .unwrap_or_else(|mismatch| panic!("{mismatch:?}\n{}", program.source));
        assert!(done.lookups > 0, "{}", program.source);
    }
}

// ----- R4d: dependencies as member tables -----

/// Reaches: R4a, R4c (`search`, `member`), R4d. Importing an export table
/// of 10,000 items is 10,000 steps once and 1 step afterwards; a unit is
/// asked for once per worker.
#[test]
fn an_export_table_is_imported_once() {
    let mut s = unit_scopes();
    let mut source = Units {
        list: vec![("Wide", wide_segment(10_000))],
        asked: 0,
    };
    let wide = s.names.intern("Wide");
    let missing = s.names.intern("Missing");
    let unit = s.unit_by_name(wide, &mut source).unwrap();
    assert_eq!(s.unit_by_name(missing, &mut source), None);
    assert_eq!(source.asked, 2);
    // 1 step in R4d; 2 from R4g on, which logs the read.
    assert!(steps::scope(|| assert_eq!(s.unit_by_name(wide, &mut source), Some(unit))) <= 2);
    assert_eq!(
        steps::scope(|| assert_eq!(s.unit_by_name(missing, &mut source), None)),
        1
    );
    assert_eq!(
        source.asked, 2,
        "a unit and a missing unit are asked for once"
    );
    assert_eq!((s.units.len(), s.units[unit as usize].name), (1, wide));

    let mut table = TableId(NONE);
    assert_eq!(steps::scope(|| table = s.import_table(unit, 0)), 10_000);
    assert_ne!(table.0 & IMPORTED, 0);
    assert_eq!(
        steps::scope(|| assert_eq!(s.import_table(unit, 0), table)),
        1
    );
    assert_eq!(s.imported_members.len(), 10_000);
    for i in [0u32, 1, 4_999, 9_999] {
        let key = key(&mut s, &format!("v{i}"), Namespace::Value);
        let mut row = None;
        assert!(steps::scope(|| row = s.search(table, key)) <= 14);
        let row = row.unwrap();
        let member = s.member(table, row);
        assert_eq!((member.target, member.origin), (i, unit));
        let (segment, item) = s.item(row);
        assert_eq!(
            (segment_text(segment, item.name), item.kind),
            (format!("v{i}").as_str(), ExportKind::Value)
        );
    }
    // Imports are kept for the worker: a reset keeps them.
    s.freeze();
    s.reset();
    assert_eq!(s.import_table(unit, 0), table);
    assert_eq!(source.asked, 2);
}

/// Reaches: R4a, R4c, R4d. The members of an imported table are the members
/// of the layer the old checker opens for the same unit: the same names in
/// the same namespaces. (`OPENED_UNIT_UNUSED` opens `Dep`.)
#[test]
fn an_import_lists_the_members_of_the_old_layer() {
    let old = old_checker(&OPENED_UNIT_UNUSED);
    let mut expected: Vec<(u32, String)> = old
        .events
        .iter()
        .find_map(|event| match event {
            Event::Open { members, .. } => Some(members),
            _ => None,
        })
        .expect("the program opens Dep")
        .iter()
        .map(|&(ns, name, _)| (namespace(ns) as u32, name.to_string()))
        .collect();
    expected.sort();
    assert!(expected.len() >= 6, "A, x, r, dx, c, Dc: {expected:?}");

    let mut s = unit_scopes();
    let name = s.names.intern("Dep");
    let unit = s.add_unit(name, segment_of("Dep", &old.deps[0].1));
    let table = s.import_table(unit, 0);
    let rows = s.imported_tables[(table.0 & !IMPORTED) as usize];
    let mut actual: Vec<(u32, String)> = (rows.first..rows.first + rows.len)
        .map(|row| {
            let key = Key(s.imported_members[row as usize].key);
            (key.namespace(), s.names.text(key.name()).to_string())
        })
        .collect();
    actual.sort();
    assert_eq!(actual, expected);
    // Sorted by key, and each row names the export item of its key.
    for row in rows.first..rows.first + rows.len {
        let member = s.imported_members[row as usize];
        if row > rows.first {
            assert!(s.imported_members[row as usize - 1].key <= member.key);
        }
        let (segment, item) = s.item(row);
        assert_eq!(
            segment_text(segment, item.name),
            s.names.text(Key(member.key).name())
        );
        assert_eq!(
            item.kind as u32,
            Key(member.key).namespace(),
            "ExportKind and Namespace agree for {item:?}"
        );
    }
}

/// Reaches: R4a, R4c, R4d. `@deprecated` on a declaration of a dependency
/// is a bit of its imported member.
#[test]
fn an_import_knows_what_is_deprecated() {
    let segment = compiled_segment(
        "Old",
        "@deprecated(\"gone\") let v = 1\nlet w = 2\n@deprecated(\"no\") type t = int\ntype u = int\n",
    );
    let mut s = unit_scopes();
    let name = s.names.intern("Old");
    let unit = s.add_unit(name, segment);
    let table = s.import_table(unit, 0);
    for (text, ns, deprecated) in [
        ("v", Namespace::Value, true),
        ("w", Namespace::Value, false),
        ("t", Namespace::Type, true),
        ("u", Namespace::Type, false),
    ] {
        let key = key(&mut s, text, ns);
        let member = s.member(table, s.search(table, key).unwrap());
        assert_eq!(member.origin & MEMBER_DEPRECATED != 0, deprecated, "{text}");
        assert_eq!(member.origin & super::scope::UNIT_MASK, unit);
    }
}

// ----- R4e: paths -----

/// A dependency with aliases in its own signature, one of them of another
/// unit, a module type and a functor.
const CHAIN: (&str, &str) = (
    "Chain",
    "module A = {\n  module B = {\n    let v = \"s\"\n  }\n}\nmodule N = A\nmodule O = N\nmodule D = Dep\nmodule type S = {\n  let a: int\n}\nmodule F = (X: S) => {\n  let v = X.a\n}\n",
);

/// A unit that compiles `Dep` and `Chain` first.
const READS_CHAIN: Program = Program {
    deps: &[DEP, CHAIN],
    source: "let v = Chain.O.B.v\n",
    lines: &[],
    warnings: &[],
};

/// The names of a path.
fn path(s: &mut Scopes, components: &[&str]) -> Vec<Name> {
    components.iter().map(|text| s.names.intern(text)).collect()
}

/// Reaches: R4a to R4e. `PATH_THROUGH_TWO_ALIASES` inside the unit:
/// `module N = A; module O = N; O.B.v` is `A.B.v`, and the modules the path
/// went through are reported for their usage.
#[test]
fn a_path_through_two_local_aliases() {
    let mut s = unit_scopes();
    let mut source = Units {
        list: Vec::new(),
        asked: 0,
    };
    // module A = { module B = { let v = "s" } }
    let from_a = s.log_mark();
    s.enter();
    let (b, b_table) = module(&mut s, "B", &[("v", Namespace::Value, 0)]);
    let a_table = s.seal(from_a);
    s.leave();
    let a = bind(&mut s, "A", Namespace::Module, a_table.0);
    let alias = |s: &mut Scopes, name: &str, target: Binder| {
        let key = key(s, name, Namespace::Module);
        let binder = s
            .binders
            .push(key, Resolved::binder(target).0, 0, BinderKind::ModuleAlias);
        s.bind(binder);
        binder
    };
    let n = alias(&mut s, "N", a);
    let o = alias(&mut s, "O", n);
    let v_key = key(&mut s, "v", Namespace::Value);
    let v = Binder(s.member(b_table, s.search(b_table, v_key).unwrap()).target);

    assert_eq!(
        s.module_shape(Resolved::binder(o), &mut source),
        Ok(ModuleShape::Structure(a_table))
    );
    assert_eq!(
        steps::scope(|| {
            let _ = s.module_shape(Resolved::binder(o), &mut source);
        }),
        2,
        "two aliases"
    );
    let names = path(&mut s, &["O", "B", "v"]);
    let mut modules = Vec::with_capacity(4);
    let mut found = None;
    let count = steps::scope(|| {
        found = Some(s.lookup_path(Namespace::Value, &names, &mut modules, &mut source))
    });
    assert_eq!(
        found.unwrap(),
        Ok(Found {
            item: Resolved::binder(v),
            layer: NONE
        })
    );
    assert_eq!(
        modules,
        [
            Found {
                item: Resolved::binder(o),
                layer: NONE
            },
            Found {
                item: Resolved::binder(b),
                layer: NONE
            }
        ]
    );
    // Derived on paper: 3 components, the head of `O`, 2 aliases, and one
    // comparison in each of the two one-member tables.
    assert!(count <= 8, "{count}");
    assert_eq!(source.asked, 0, "`O` is bound: no unit is asked for");

    // One component is a lookup by name; a module name with no binding is a unit.
    let one = path(&mut s, &["A"]);
    assert_eq!(
        s.lookup_path(Namespace::Module, &one, &mut modules, &mut source),
        Ok(Found {
            item: Resolved::binder(a),
            layer: NONE
        })
    );
    assert!(modules.is_empty());
    for (components, ns, kind, component) in [
        (
            &["O", "B", "w"][..],
            Namespace::Value,
            PathErrorKind::Unbound,
            2,
        ),
        (
            &["O", "C", "v"][..],
            Namespace::Value,
            PathErrorKind::UnboundModule,
            1,
        ),
        (
            &["Nowhere", "v"][..],
            Namespace::Value,
            PathErrorKind::UnboundModule,
            0,
        ),
        (&["w"][..], Namespace::Value, PathErrorKind::Unbound, 0),
        (
            &["Nowhere"][..],
            Namespace::Module,
            PathErrorKind::UnboundModule,
            0,
        ),
    ] {
        let names = path(&mut s, components);
        let error = s
            .lookup_path(ns, &names, &mut modules, &mut source)
            .unwrap_err();
        assert_eq!(
            (error.kind, error.component),
            (kind, component),
            "{components:?}"
        );
    }
    // A functor has no members.
    let functor = bind(&mut s, "F", Namespace::Module, NONE);
    assert_eq!(
        s.module_shape(Resolved::binder(functor), &mut source),
        Ok(ModuleShape::Functor)
    );
    let names = path(&mut s, &["F", "v"]);
    let error = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap_err();
    assert_eq!((error.kind, error.component), (PathErrorKind::Functor, 0));
    // A path found through an open reports the layer of its first component.
    let wrapper = s.table_from(&[(Key(s.binders.key[a.0 as usize]), a)]);
    s.enter();
    bind(&mut s, "A", Namespace::Module, NONE);
    let open = s.open(wrapper, 0, 0, 0);
    let names = path(&mut s, &["A", "B", "v"]);
    assert_eq!(
        s.lookup_path(Namespace::Value, &names, &mut modules, &mut source),
        Ok(Found {
            item: Resolved::binder(v),
            layer: open
        })
    );
    assert_eq!(
        modules[0],
        Found {
            item: Resolved::binder(a),
            layer: open
        }
    );
}

/// Reaches: R4a to R4e. `PATH_THROUGH_TWO_ALIASES` across units:
/// `module P = Dep; module Q = P.A; Q.B.v` is the value `v` of `Dep`'s
/// table for `A.B`, and aliases inside a dependency are followed in its
/// segment.
#[test]
fn a_path_through_aliases_of_another_unit() {
    let old = old_checker(&READS_CHAIN);
    let dep = segment_of("Dep", &old.deps[0].1);
    let chain = segment_of("Chain", &old.deps[1].1);
    let mut s = unit_scopes();
    let mut source = Units {
        list: vec![("Dep", dep), ("Chain", chain)],
        asked: 0,
    };
    let mut modules = Vec::with_capacity(4);
    let item_of = |s: &Scopes, found: Found| match found.item.kind() {
        ResolvedKind::Import(row) => {
            let (segment, item) = s.item(row);
            (
                segment_text(segment, item.name).to_string(),
                item.kind,
                s.imported_members[row as usize].origin & super::scope::UNIT_MASK,
            )
        }
        other => panic!("not imported: {other:?}"),
    };

    // Dep.A.B.v, directly.
    let names = path(&mut s, &["Dep", "A", "B", "v"]);
    let direct = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    let dep_unit = s.unit_by_name(names[0], &mut source).unwrap();
    assert_eq!(
        item_of(&s, direct),
        ("v".to_string(), ExportKind::Value, dep_unit)
    );
    assert_eq!(modules.len(), 3);
    assert_eq!(modules[0].item, Resolved::unit(dep_unit));

    // module P = Dep; module Q = P.A; Q.B.v
    let p_key = key(&mut s, "P", Namespace::Module);
    let p = s.binders.push(
        p_key,
        Resolved::unit(dep_unit).0,
        0,
        BinderKind::ModuleAlias,
    );
    s.bind(p);
    let names = path(&mut s, &["P", "A"]);
    let p_a = s
        .lookup_path(Namespace::Module, &names, &mut modules, &mut source)
        .unwrap();
    let q_key = key(&mut s, "Q", Namespace::Module);
    let q = s
        .binders
        .push(q_key, p_a.item.0, 0, BinderKind::ModuleAlias);
    s.bind(q);
    let names = path(&mut s, &["Q", "B", "v"]);
    let through = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    assert_eq!(through.item, direct.item, "the same imported member");
    assert_eq!(modules[0].item, Resolved::binder(q));

    // Aliases published by a dependency: Chain.O.B.v is Chain.A.B.v, and
    // Chain.D.A.B.v reads Dep.
    let names = path(&mut s, &["Chain", "A", "B", "v"]);
    let chain_direct = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    let names = path(&mut s, &["Chain", "O", "B", "v"]);
    let chain_alias = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    assert_eq!(chain_alias.item, chain_direct.item);
    let names = path(&mut s, &["Chain", "D", "A", "B", "v"]);
    let chain_dep = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    assert_eq!(chain_dep.item, direct.item);
    assert_eq!(source.asked, 2, "each unit is asked for once");

    // A functor of a dependency has no members; a module type is found.
    let names = path(&mut s, &["Chain", "F", "v"]);
    let error = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap_err();
    assert_eq!((error.kind, error.component), (PathErrorKind::Functor, 1));
    let names = path(&mut s, &["Chain", "S"]);
    let module_type = s
        .lookup_path(Namespace::ModuleType, &names, &mut modules, &mut source)
        .unwrap();
    assert_eq!(item_of(&s, module_type).1, ExportKind::ModuleType);
    // Qualified candidates: the constructors of one name in a module.
    let names = path(&mut s, &["Dep"]);
    let dep_module = s
        .lookup_path(Namespace::Module, &names, &mut modules, &mut source)
        .unwrap();
    let Ok(ModuleShape::Structure(table)) = s.module_shape(dep_module.item, &mut source) else {
        panic!("Dep is a structure");
    };
    let dc = key(&mut s, "Dc", Namespace::Constructor);
    let mut out = Vec::with_capacity(2);
    s.candidates_in(table, dc, &mut out);
    assert_eq!(out.len(), 1);
    assert_eq!(item_of(&s, out[0]).1, ExportKind::Constructor);
}

/// Reaches: R4a to R4e. A path of 10,000 components and a chain of 10,000
/// aliases are linear and fit a 2 MB stack.
#[test]
fn long_paths_and_alias_chains_are_linear() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut s = unit_scopes();
            let mut source = Units {
                list: Vec::new(),
                asked: 0,
            };
            // M9999 is innermost: build the tables inside out.
            let mut inner = push(&mut s, "v", Namespace::Value, 0);
            let mut names = vec![s.names.intern("v")];
            for i in (0..10_000).rev() {
                let table = s.table_from(&[(Key(s.binders.key[inner.0 as usize]), inner)]);
                inner = push(&mut s, &format!("M{i}"), Namespace::Module, table.0);
                names.push(Key(s.binders.key[inner.0 as usize]).name());
            }
            s.bind(inner);
            names.reverse();
            let mut modules = Vec::with_capacity(10_000);
            let mut found = None;
            let count = steps::scope(|| {
                found = Some(s.lookup_path(Namespace::Value, &names, &mut modules, &mut source))
            });
            assert!(found.unwrap().is_ok());
            assert_eq!(modules.len(), 10_000);
            assert!(count <= 3 * 10_001, "{count}");

            let mut target = inner;
            for i in 0..10_000 {
                let key = key(&mut s, &format!("N{i}"), Namespace::Module);
                target =
                    s.binders
                        .push(key, Resolved::binder(target).0, 0, BinderKind::ModuleAlias);
            }
            let mut shape = None;
            let count = steps::scope(|| {
                shape = Some(s.module_shape(Resolved::binder(target), &mut source))
            });
            assert!(matches!(shape.unwrap(), Ok(ModuleShape::Structure(_))));
            assert_eq!(count, 10_000);
        })
        .unwrap()
        .join()
        .unwrap();
}

// ----- R4f: usage and the warnings of a lookup -----

/// Reaches: R4a, R4b, R4f. The task text's bound: marking 10,000 uses is
/// 10,000 steps.
#[test]
#[ignore = "R4f build"]
fn marking_ten_thousand_uses_is_ten_thousand_steps() {
    let mut s = unit_scopes();
    let binders: Vec<Binder> = (0..100)
        .map(|i| bind(&mut s, &format!("n{i}"), Namespace::Value, 0))
        .collect();
    let count = steps::scope(|| {
        for i in 0..10_000 {
            s.mark(binders[i % 100], USED);
        }
    });
    assert_eq!(count, 10_000);
    assert!(
        binders
            .iter()
            .all(|binder| s.binders.used[binder.0 as usize] == USED)
    );
    assert!(s.warnings.is_empty());
}

/// Reaches: R4a, R4b, R4c, R4f. The warnings of `OPEN_SHADOWS_A_LOCAL`,
/// `LOCAL_SHADOWS_AN_OPEN`, `LATER_OPEN_WINS` and `OPEN_SHADOWS_MEMBERS` as
/// the old checker is pinned to report them: a use through an open that
/// hides something reports the shadowing once per name at the open; an
/// open nothing went through is unused at the end of the unit; a lookup
/// that is not used raises nothing.
#[test]
#[ignore = "R4f build"]
fn an_open_is_used_or_unused_and_reports_shadowing_once() {
    // let x = 1; module M = { let x = "s"; type t = A }; open M; type u = A; let y = x
    let mut s = unit_scopes();
    bind(&mut s, "x", Namespace::Value, 0);
    let (_, m) = module(
        &mut s,
        "M",
        &[("x", Namespace::Value, 0), ("A", Namespace::Constructor, 0)],
    );
    let open = s.open(m, 77, 5, 0);
    s.arm_open(open);
    let local_a = bind(&mut s, "A", Namespace::Constructor, 0);
    let x = key(&mut s, "x", Namespace::Value);
    let a = key(&mut s, "A", Namespace::Constructor);
    let found = s.find(x).unwrap();
    let mut candidates = Vec::new();
    s.candidates(a, &mut candidates);
    assert_eq!(candidates.len(), 2);
    assert_eq!(
        candidates[0],
        Found {
            item: Resolved::binder(local_a),
            layer: NONE
        }
    );
    assert_eq!(candidates[1].layer, open);
    assert!(
        s.warnings.is_empty() && s.opens[open as usize].flags == 0,
        "finding is not using"
    );
    s.use_found(found, x, 100);
    assert_eq!(s.opens[open as usize].flags & OPEN_USED, OPEN_USED);
    assert_eq!(s.warnings.len(), 1);
    let warning = s.warnings[0];
    assert_eq!(
        (warning.kind, warning.loc, warning.a, warning.b),
        (WarningKind::OpenShadows, 77, x.0, open)
    );
    s.use_found(found, x, 101);
    assert_eq!(s.warnings.len(), 1, "once per name and open");
    // The local `A` is younger than the open and was not found through it.
    s.use_found(candidates[0], a, 102);
    assert_eq!(s.warnings.len(), 1);
    // The open's `A` hides nothing: the only other `A` is younger than the open.
    s.use_found(candidates[1], a, 103);
    assert_eq!(s.warnings.len(), 1);
    s.finish();
    assert_eq!(s.warnings.len(), 1, "the open was used");

    // module M = { let x = "s" }; open M; let x = 1; let y = x
    let mut s = unit_scopes();
    let (_, m) = module(&mut s, "M", &[("x", Namespace::Value, 0)]);
    let open = s.open(m, 77, 5, 0);
    s.arm_open(open);
    bind(&mut s, "x", Namespace::Value, 0);
    let x = key(&mut s, "x", Namespace::Value);
    let found = s.find(x).unwrap();
    s.use_found(found, x, 100);
    assert!(s.warnings.is_empty());
    s.finish();
    assert_eq!(s.warnings.len(), 1);
    let warning = s.warnings[0];
    assert_eq!(
        (warning.kind, warning.loc, warning.a),
        (WarningKind::UnusedOpen, 77, open)
    );

    // `open!` reports no shadowing; an open that is not armed no unused open.
    let mut s = unit_scopes();
    bind(&mut s, "x", Namespace::Value, 0);
    let (_, m) = module(&mut s, "M", &[("x", Namespace::Value, 0)]);
    let open = s.open(m, 77, 5, OPEN_OVERRIDE);
    let x = key(&mut s, "x", Namespace::Value);
    let found = s.find(x).unwrap();
    s.use_found(found, x, 100);
    let (_, m2) = module(&mut s, "M2", &[]);
    s.open(m2, 78, 6, 0);
    s.finish();
    assert!(s.warnings.is_empty());
    assert_eq!(s.opens[open as usize].flags, OPEN_USED | OPEN_OVERRIDE);
}

/// Reaches: R4a, R4b, R4c, R4f. A constructor used through an open that
/// hides an older one: `use_found` reports nothing and hands back the
/// hidden item, because whether the open shadows depends on the two result
/// types (`old_checker_open_of_the_same_type_reports_no_shadowing`). The
/// walk's verdict is `shadows`, once per name and open. A value never asks.
#[test]
#[ignore = "R4f build"]
fn the_walk_decides_whether_an_opened_constructor_shadows() {
    // type t = A; let x = 1; module M = { type u = A; let x = 2 }; open M
    let mut s = unit_scopes();
    let older = bind(&mut s, "A", Namespace::Constructor, 0);
    bind(&mut s, "x", Namespace::Value, 0);
    let (_, m) = module(
        &mut s,
        "M",
        &[("A", Namespace::Constructor, 0), ("x", Namespace::Value, 0)],
    );
    let open = s.open(m, 77, 5, 0);
    let a = key(&mut s, "A", Namespace::Constructor);
    let mut candidates = Vec::new();
    s.candidates(a, &mut candidates);
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0].layer, open);
    let hidden = Some(Found {
        item: Resolved::binder(older),
        layer: NONE,
    });
    assert_eq!(s.use_found(candidates[0], a, 100), hidden);
    assert_eq!(s.opens[open as usize].flags & OPEN_USED, OPEN_USED);
    assert!(s.warnings.is_empty(), "the walk has not compared the types");
    // The same result type: nothing is said, and the next use asks again.
    assert_eq!(s.use_found(candidates[0], a, 101), hidden);
    assert!(s.warnings.is_empty());
    // Different result types: reported at the open, once.
    s.shadows(open, a);
    assert_eq!(s.warnings.len(), 1);
    let warning = s.warnings[0];
    assert_eq!(
        (warning.kind, warning.loc, warning.a, warning.b),
        (WarningKind::OpenShadows, 77, a.0, open)
    );
    assert_eq!(s.use_found(candidates[0], a, 102), None);
    assert_eq!(s.warnings.len(), 1);
    // The older constructor was not found through the open.
    assert_eq!(s.use_found(candidates[1], a, 103), None);
    // A value is reported by `use_found` itself and returns nothing.
    let x = key(&mut s, "x", Namespace::Value);
    let found = s.find(x).unwrap();
    assert_eq!(found.layer, open);
    assert_eq!(s.use_found(found, x, 104), None);
    assert_eq!(s.warnings.len(), 2);
    // `open!` never asks.
    let mut s = unit_scopes();
    bind(&mut s, "A", Namespace::Constructor, 0);
    let (_, m) = module(&mut s, "M", &[("A", Namespace::Constructor, 0)]);
    let open = s.open(m, 77, 5, OPEN_OVERRIDE);
    let a = key(&mut s, "A", Namespace::Constructor);
    let mut candidates = Vec::new();
    s.candidates(a, &mut candidates);
    assert_eq!(candidates[0].layer, open);
    assert_eq!(s.use_found(candidates[0], a, 100), None);
    assert!(s.warnings.is_empty());
}

/// Reaches: R4a, R4b, R4f. The unused warnings of `UNUSED_DECLARATIONS`:
/// at the end of the unit, in the order armed, for binders without a use;
/// a constructor counts as used by any of its three usages; what was armed
/// under an undone speculation is forgotten; a unit with an error never
/// calls `finish` and so has only the warnings its lookups raised.
#[test]
#[ignore = "R4f build"]
fn unused_binders_are_reported_in_the_order_armed() {
    let mut s = unit_scopes();
    let t = bind(&mut s, "t", Namespace::Type, 0);
    let a = bind(&mut s, "A", Namespace::Constructor, 0);
    let b = bind(&mut s, "B", Namespace::Constructor, 0);
    let unused = bind(&mut s, "unused", Namespace::Value, 0);
    let v = bind(&mut s, "v", Namespace::Value, 0);
    for binder in [t, a, b, unused, v] {
        s.arm(binder);
    }
    let mark = s.armed_mark();
    let speculative = bind(&mut s, "speculative", Namespace::Value, 0);
    s.arm(speculative);
    s.disarm(mark);
    let late = bind(&mut s, "local", Namespace::Value, 0);
    s.arm(late);
    s.mark(v, USED);
    s.mark(b, PATTERN);
    assert!(s.warnings.is_empty(), "nothing before the end of the unit");
    let count = steps::scope(|| s.finish());
    assert_eq!(count, 6, "one step an armed entry");
    let reported: Vec<(WarningKind, u32)> = s.warnings.iter().map(|w| (w.kind, w.a)).collect();
    assert_eq!(
        reported,
        [
            (WarningKind::Unused, t.0),
            (WarningKind::Unused, a.0),
            (WarningKind::Unused, unused.0),
            (WarningKind::Unused, late.0),
        ]
    );
    // 10,000 armed binders: 10,000 steps.
    let mut s = unit_scopes();
    for i in 0..10_000 {
        let binder = bind(&mut s, &format!("n{i}"), Namespace::Value, i);
        s.binders.loc[binder.0 as usize] = i;
        s.arm(binder);
    }
    assert_eq!(steps::scope(|| s.finish()), 10_000);
    assert_eq!(s.warnings.len(), 10_000);
    assert!(
        s.warnings
            .iter()
            .enumerate()
            .all(|(i, w)| w.loc == i as u32)
    );
}

/// Reaches: R4a to R4f. The deprecations of `DEPRECATED_USES`: one warning
/// per use, at the use, for a local declaration and for an imported one,
/// and for a module a path goes through.
#[test]
#[ignore = "R4f build"]
fn a_deprecated_item_warns_at_each_use() {
    let segment = compiled_segment("Old", "@deprecated(\"gone\") let v = 1\nlet w = 2\n");
    let mut s = unit_scopes();
    let mut source = Units {
        list: vec![("Old", segment)],
        asked: 0,
    };
    let local = bind(&mut s, "v", Namespace::Value, 0);
    s.binders.used[local.0 as usize] |= DEPRECATED;
    let v = key(&mut s, "v", Namespace::Value);
    let found = s.find(v).unwrap();
    s.use_found(found, v, 10);
    s.use_found(found, v, 11);
    let mut modules = Vec::with_capacity(2);
    let names = path(&mut s, &["Old", "v"]);
    let imported = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    s.use_modules(&modules, &names[..1], 12);
    s.use_found(imported, v, 12);
    let names = path(&mut s, &["Old", "w"]);
    let w = key(&mut s, "w", Namespace::Value);
    let fine = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    s.use_found(fine, w, 13);
    let reported: Vec<(WarningKind, u32, u32)> =
        s.warnings.iter().map(|w| (w.kind, w.loc, w.a)).collect();
    assert_eq!(
        reported,
        [
            (WarningKind::Deprecated, 10, found.item.0),
            (WarningKind::Deprecated, 11, found.item.0),
            (WarningKind::Deprecated, 12, imported.item.0),
        ]
    );
    // A deprecated module on the path, and the module's usage.
    let m = bind(&mut s, "M", Namespace::Module, NONE);
    s.binders.used[m.0 as usize] |= DEPRECATED;
    let m_name = [s.names.intern("M")];
    s.use_modules(
        &[Found {
            item: Resolved::binder(m),
            layer: NONE,
        }],
        &m_name,
        20,
    );
    assert_eq!(s.binders.used[m.0 as usize] & USED, USED);
    let last = *s.warnings.last().unwrap();
    assert_eq!(
        (last.kind, last.loc, last.a),
        (WarningKind::Deprecated, 20, Resolved::binder(m).0)
    );
}

// ----- R4g: reads of other units -----

/// Reaches: R4a to R4g. A unit is read when its interface is loaded and an
/// item when it is used; each is logged once, in the order first read; a
/// reset forgets them; 10,000 uses of one item are 10,000 steps and one
/// entry.
#[test]
#[ignore = "R4g build"]
fn reads_are_logged_once_in_the_order_first_read() {
    let mut s = unit_scopes();
    s.freeze();
    let mut source = Units {
        list: vec![
            ("Wide", wide_segment(100)),
            ("Dep", compiled_segment(DEP.0, DEP.1)),
        ],
        asked: 0,
    };
    let mut modules = Vec::with_capacity(4);
    let names = path(&mut s, &["Dep", "A", "B", "v"]);
    let found = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    let dep = s.unit_by_name(names[0], &mut source).unwrap();
    assert_eq!(s.read_units, [dep], "the path loaded Dep's interface");
    assert_eq!(s.unit_read[dep as usize], READ);
    assert!(s.read_items.is_empty(), "nothing was used yet");
    let v = key(&mut s, "v", Namespace::Value);
    let ResolvedKind::Import(row) = found.item.kind() else {
        panic!()
    };
    let count = steps::scope(|| {
        for _ in 0..10_000 {
            s.read_item(row);
        }
    });
    assert_eq!(count, 10_000);
    s.use_found(found, v, 1);
    assert_eq!(s.read_items, [row]);
    let names = path(&mut s, &["Wide", "v7"]);
    let other = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    let wide = s.unit_by_name(names[0], &mut source).unwrap();
    let v7 = key(&mut s, "v7", Namespace::Value);
    s.use_found(other, v7, 2);
    assert_eq!(s.read_units, [dep, wide]);
    assert_eq!(s.read_items.len(), 2);

    // The next unit of this worker starts with no reads but keeps the imports.
    s.reset();
    assert!(s.read_units.is_empty() && s.read_items.is_empty());
    assert_eq!(s.unit_read[dep as usize], 0);
    let names = path(&mut s, &["Wide", "v7"]);
    let again = s
        .lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    assert_eq!(again.item, other.item, "the imported row is the worker's");
    assert_eq!(
        s.read_units,
        [wide],
        "read again by this unit, without asking the source"
    );
    assert_eq!(source.asked, 2);
}

/// Reaches: R4a to R4g. The reads of a unit, as unit names in the order
/// first read, do not depend on what the worker checked before (its unit
/// indices and imported rows differ; the names do not).
#[test]
#[ignore = "R4g build"]
fn reads_do_not_depend_on_what_the_worker_checked_before() {
    let segments = || {
        vec![
            ("Wide", wide_segment(100)),
            ("Dep", compiled_segment(DEP.0, DEP.1)),
        ]
    };
    let check = |s: &mut Scopes, source: &mut Units| -> Vec<String> {
        let mut modules = Vec::with_capacity(4);
        for components in [
            &["Dep", "x"][..],
            &["Wide", "v3"][..],
            &["Dep", "A", "B", "v"][..],
        ] {
            let names = path(s, components);
            let key = Key::new(*names.last().unwrap(), Namespace::Value);
            let found = s
                .lookup_path(Namespace::Value, &names, &mut modules, source)
                .unwrap();
            s.use_found(found, key, 0);
        }
        s.read_units
            .iter()
            .map(|&unit| s.names.text(s.units[unit as usize].name).to_string())
            .collect()
    };
    let mut fresh = unit_scopes();
    fresh.freeze();
    let fresh_reads = check(
        &mut fresh,
        &mut Units {
            list: segments(),
            asked: 0,
        },
    );

    let mut busy = unit_scopes();
    busy.freeze();
    let mut source = Units {
        list: segments(),
        asked: 0,
    };
    let mut modules = Vec::with_capacity(4);
    let names = path(&mut busy, &["Wide", "v9"]);
    busy.lookup_path(Namespace::Value, &names, &mut modules, &mut source)
        .unwrap();
    busy.reset();
    let busy_reads = check(&mut busy, &mut source);
    assert_eq!(fresh_reads, ["Dep", "Wide"]);
    assert_eq!(busy_reads, fresh_reads);
    assert_ne!(
        busy.read_units, fresh.read_units,
        "the indices differ; the names do not"
    );
}
