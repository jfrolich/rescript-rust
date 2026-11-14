//! Tests of slice R4 (CHECKER_REWRITE "R4 as designed").
//!
//! The first part runs today on the old checker and pins what a lookup
//! answers: the programs of [`PROGRAMS`], each with the lines of the
//! canonical signature that show which item a name resolved to and with the
//! warnings its lookups raise. The old checker is driven as a build drives
//! it: `driver::compile_source_in_process` on a source text, dependencies
//! compiled the same way and registered in a module registry. Nothing is
//! started at a level or a stamp a compilation would not start at.
//!
//! The second part is the acceptance tests of the build slices, ignored
//! until their slice is built. Each names the `todo!` slices it reaches.

use std::sync::Arc;

use super::scope_trace::{self, Event, Ns};
use crate::cmi::persistent_env::{InMemoryModuleInfo, ModuleRegistry};
use crate::cmi::portable_types::internalize_pers_struct;
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
}

/// The warnings a project enables by default (rewatch `config.rs`), so that
/// the pinned warnings are those a build prints.
fn options() -> CompilerOptions {
    CompilerOptions {
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
    for &(name, source) in program.deps {
        let file = format!("{name}.res");
        let compiled =
            compile_source_in_process(source, &file, name, &options, &registry, false, None)
                .unwrap_or_else(|error| panic!("dependency {name} does not compile: {error:?}"));
        let unit = compiled.pers_struct.expect("published dependency");
        registry.register_module_arc(
            name,
            unit,
            InMemoryModuleInfo::new(file.into(), true, Default::default(), false),
        );
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
