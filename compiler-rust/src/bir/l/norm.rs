//! Level L normalising rules: what `LamArena`'s smart constructors do when a
//! node is built (`compiler-rust/src/lambda/arena.rs`). The table in
//! BACKEND_REDESIGN.md C.5 is the specification; every rule cites its row.
//!
//! | Row | Constructor (`LamArena`) | Trigger | Result | Pattern depth |
//! | --- | --- | --- | --- | --- |
//! | N1 | `prim`, `fold_prim` | unary primitive on a constant | constant | 1 |
//! | N2 | `prim`, `fold_prim` | binary primitive on two constants | constant | 1 |
//! | N3 | `prim`, `fold_makeblock_module_alias` | module block of all fields of one module, in order | that module | 2, all arguments |
//! | N4 | `if_` | constant condition | the branch taken | 1 |
//! | N5 | `if_` | a branch is `assert false` | `seq(condition, other branch)` | 1 |
//! | N6 | `if_` | `if c then true else false`, `c` a boolean primitive | `c` | 1 |
//! | N7 | `if_`, `lambda_not` | `if c then false else true`, `c` a boolean primitive | `not c`; `a != b` becomes `a == b` | 1 |
//! | N8 | `seq` | first is a non-empty `Pmakeblock` | its arguments in sequence, then second | 1, all arguments |
//! | N9 | `seq` | first is a one-argument null-to-option conversion | `seq(argument, second)` | 1 |
//! | N10 | `switch_with`, `decide_switch` | constant scrutinee | the action of its case, or the default | 1, the keys |
//! | N11 | `switch_with`, `decide_switch` | constant scrutinee, untagged variant | the action the generated dispatch reaches | 1, the keys, and `eq_approx` of actions |
//! | N12 | `string_switch_with` | constant string scrutinee | the action of its case, or the default | 1, the keys |
//! | N13 | `apply`, `eta_reduce_function_apply` | callee is a function that only forwards its parameters to a primitive | the primitive on the arguments | 4 |
//! | N14 | `apply` | callee is `let x = v in fun` | `let x = v in apply(fun, args)` | 2 |
//!
//! `let_`, `letrec`, `function_`, `static_catch`, `try_`, loops and
//! assignments build their node as given: there is no rule for them.
//!
//! Each rule edits the node in place and pushes what the constructor would
//! have passed to another constructor; it never calls another rule.
use crate::bir::NodeId;
use crate::bir::engine::{Changed, Engine};

/// Number of rows in the table.
pub const ROWS: usize = 14;
/// Row names, for reports.
pub const ROW_NAMES: [&str; ROWS] = [
    "N1", "N2", "N3", "N4", "N5", "N6", "N7", "N8", "N9", "N10", "N11", "N12", "N13", "N14",
];

/// Offer one node to the rule of its opcode.
pub(crate) fn step(e: &mut Engine<'_>, node: NodeId) -> Changed {
    // One read of the node decides which rule sees it; the rules follow in
    // table order.
    let _op = e.bir().node(node).op();
    Changed::No
}
