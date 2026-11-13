# Backend lowering: level L to level J (S3.3 to S3.9)

Status: specification. S3.3 to S3.9 are implemented, in check mode only ([STATUS.md](STATUS.md)). It is the table
[BACKEND_REDESIGN.md](BACKEND_REDESIGN.md) H.1 asks for before stage S3.3
("a table mapping each context function of `lam_compile.rs` (A.5) to a
continuation case"), and the slicing of S3.3 to S3.9. Sections A to I of that
document are cited as "A.5", "B.3" and so on; sections of this one are
numbered 1 to 10.

Conventions.

- Code is cited by function and line. Lines are those of commit `7822842842`
  and will drift; the function name is the reference. Files are abbreviated:

  | Key | File under `compiler-rust/src/` |
  | --- | --- |
  | C | `lambda/lam_compile.rs` |
  | V | `lambda/lam_compile_variant.rs` |
  | P | `lambda/lam_compile_primitive.rs` |
  | X | `lambda/lam_compile_external.rs` |
  | A | `lambda/lam_compile_arguments.rs` |
  | K | `lambda/lam_compile_const.rs` |
  | M | `lambda/lam_compile_main.rs` |
  | T | `lambda/lam_compile_context.rs` |
  | O | `lambda/lam_coercion.rs` |
  | E | `lambda/js_exp_make.rs` |
  | S | `lambda/js_stmt_make.rs` |
  | B | `js_ir/build.rs` |
  | U | `lambda/untagged_dispatch.rs` |
  | D | `bir/edit.rs` |

  OCaml is cited as `lam_compile.ml:<line>` and so on, under `compiler/core/`,
  at the same commit.
- "Legacy" is today's Rust lowering (the files above). "OCaml" is the
  reference compiler. The legacy code is the oracle of the `Check` gate; OCaml
  is the oracle of the release gate. Where the two are structured differently,
  this document says which structure the new lowering takes.
- "Tested" means the Rust compiler was run on a small `.res` file while
  writing this document and the output is quoted. "Read" means the claim comes
  from reading the cited code only. "Open" marks what could not be determined;
  section 10 collects those with the experiment that settles each.
- The OCaml compiler was not built for this document. Every statement about
  what OCaml emits is "read".

## 1. The interface of the lowering

### 1.1 What the legacy code is

OCaml has one function, `compile_lambda cxt lam`, and a context record
(`lam_compile_context.ml:46-82`):

```ocaml
type continuation =
  | EffectCall of tail_type
  | NeedValue of tail_type
  | Declare of let_kind * J.ident
  | Assign of J.ident
type tail_type = Not_tail | Maybe_tail_is_return of maybe_tail
type maybe_tail = Tail_in_try | Tail_with_name of tail
type tail = {label: return_label option; in_staticcatch: bool}
type t = {continuation; jmp_table; meta; switch_depth; loop_stack;
          loop_label_counter: int ref}
```

and one result type, `Js_output.t = {block; value: expression option;
output_finished}` (`js_output.ml:28-31`), joined with `append_output`
(`js_output.ml:117-138`).

The legacy Rust code has no context value. It has one family of functions per
continuation, a set of fields of `LambdaCompiler` that play the part of the
rest of the context, and two result types: `Compiled {prelude, expr, finished}`
(a `Js_output.t` whose value is present) and `BlockOutput {block, finished}`
(one whose value is absent). Section 2 lists every function.

Three structural differences between the legacy code and OCaml matter here.

1. **Exits.** OCaml has one jump table, `jmp_table: label -> {exit_id,
   bindings, order_id}`, and one test for the cheap form (`lam_compile.ml:1173`).
   The legacy code has three stacks (`static_handlers`,
   `static_jump_handlers`, `fallthrough_return_handlers`, C:413-415). Until
   S3.5 it chose between them with about twenty predicates that walked the
   body and the handler and approximated what OCaml's `in_staticcatch` bit
   says. S3.5 found two shapes on which they chose the other form than OCaml
   (4.6) and replaced them with OCaml's test, `staticcatch_takes_pseudo_jump`:
   no enclosing `try` body, the three stacks empty, and no exit in the
   handler.
2. **Speculation.** OCaml compiles a branch of a conditional in `NeedValue`
   first and compiles it again in the real continuation when the first result
   needs statements (`lam_compile.ml:1577-1712`). The legacy code does the
   same, in a different order in the return continuation (section 3.6).
3. **Tail loops.** OCaml compiles a recursive function body once, with a
   `return_label` in the continuation, and looks at `ret.triggered` afterwards
   (`lam_compile.ml:507-575`). The legacy code asks
   `function_has_self_tailcall` (C:6772) first, compiles the body with a
   `TailLoopState` threaded through a third family of functions, and compiles
   the function again when the loop was not triggered
   (`compile_recursive_function_expr` (C:3989)).

**Decision.** The new lowering takes OCaml's structure: one function, one
context value, one result type. The legacy functions are the oracle, not the
shape. Every legacy function then maps to a value of the context (section 2),
and the predicates of row K14 become one test on it (section 4.1).

### 1.2 Types

```rust
// bir/lower/mod.rs
pub enum Cont {
    Effect(Tail),            // EffectCall
    Value(Tail),             // NeedValue
    Declare(LetKind, VarId), // Declare (kind, id)
    Assign(VarId),           // Assign id
}
pub enum Tail {
    No,                      // Not_tail
    Return(Ret),             // Maybe_tail_is_return
}
pub enum Ret {
    InTry,                                   // Tail_in_try
    Named { loop_: Option<LoopRef>, in_catch: bool }, // Tail_with_name
}
#[derive(Clone, Copy)]
pub struct Cx {
    cont: Cont,
    jumps: JumpTop,     // top of the jump stack visible here (4.1)
    switch_depth: u32,  // inherited switch scopes; a source loop preserves depth
    loops: LoopTop,     // top of the loop-frame stack visible here
    return_unit: bool,  // the enclosing function's `return_unit` attribute
    probing: bool,      // a conditional reads whether this output is free (1.5)
}
pub struct Out {
    stmts: Span,              // a run in the lowering's statement stack (1.3)
    value: Option<NodeId>,    // a J expression
    finished: Finished,       // True, False, Dummy: js_output.ml:28-31
}
```

`Cx` is `Copy` and is passed by value, as OCaml passes `{cxt with ...}`.
`LoopRef` names the `return_label` of the function being compiled as a loop:
its parameters, the map from a parameter to its `_x` copy and the `triggered`
bit (5.1). They live in the lowering's state, not in `Cx`, because they are
written through.

State of the lowering that is not in `Cx` (one per unit):

| State | Legacy | Notes |
| --- | --- | --- |
| statement stack | `Block` vectors | 1.3 |
| jump stack | `static_handlers`, `static_jump_handlers`, `fallthrough_return_handlers` (C:413-415) | one stack of `{label, exit: VarId, bindings, order}`; `Cx::jumps` is its height where the context was made |
| loop frames | `loop_stack` (C:427) | `{label: Option<LabelRef>}` per frame |
| label schedule | `loop_label_counter` (C:431) | 4.5 |
| tail-loop records | `TailLoopState` (C:250) | 5.1 |
| external module ids | `external_module_ids` (C:408) | per unit, first use creates the identifier |
| dynamic import modules | `dynamic_import_modules` (C:412) | handed to the import list |
| the first diagnostic | `diagnostic` (C:432) | lowering can report an error (`report_diagnostic`, C:978) |

Read-only inputs: the `ASSIGNED` flag of a variable (`assignable`, C:404;
B.4), the set of awaited units (`awaited_units`, C:403, computed by
`awaited_units` (M:401)), the flat `make` paths, the options `jsx_preserve`,
`check_div_by_zero`, `cross_module_inline`, `source_map_enabled`, and the
dependents' summaries through `ModulePathResolver` (section 3.3).

### 1.3 The statement stack

The legacy code returns a `Vec<Stmt>` from every function and concatenates on
the way up, so a statement at depth `d` is copied `d` times. The new lowering
has one `Vec<NodeId>` of J statements for the unit, used as a stack:

- lowering a node pushes its statements and returns the run it pushed
  (`Span {start, len}`); a run is always the top of the stack when it is
  returned;
- `append(x, y)` (`Js_output.append_output`) needs no copy when `y` was
  lowered right after `x`: the runs are adjacent. The cases of
  `append_output` that drop something are truncations: a finished `x` drops
  `y` (truncate to the end of `x`), and a value of `x` that has no effect is
  dropped (nothing was pushed for it);
- a statement that must come before a run that is lowered first (the
  declaration of a result temporary, `let exit = 0`, the handler bindings) gets
  a **reserved slot**: the lowering pushes a hole, lowers the run, and fills
  the hole or leaves it. Holes are skipped when a run becomes a `ListId`;
- a run becomes a J child list (`ListId`) when its parent statement (`SIf`,
  `SWhile`, a `JFun` body, a switch clause) is built: one copy, of the run's
  length, and the stack is truncated to the run's start.

So each statement is written to the stack once and copied to a list once.

A conditional needs one more operation: a rule of `S.if_` that keeps one
branch as the statements following a guard (`if (c) return 1;` followed by
the else branch). The guard goes into a slot reserved before both branches
and the kept branch stays where it was lowered. The other branch becomes the
guard's list; when it lies below the kept branch, its slots become one **dead
range** (the first slot records the range's length, so a scan crosses it in
one step) instead of the kept branch being moved down. Dead ranges and holes
at the top of the stack are popped when a branch is complete, so a run ends in
a statement and "the last statement" and "exactly one statement" are constant
reads. The slots of explicit empty blocks are recorded in a sorted side list,
so that `S.if_` drops the empty blocks of a branch (B:1575) without scanning
the branch.

`SBlock` is a real node while a unit is being lowered. `S.block`
(`block` (B:1225)) wraps more than one statement in a block, and the rules of
`S.if_` look at the literal last statement of a branch without looking into a
block (`block_last_is_return_throw_or_continue`, js_stmt_make.ml:186-193; the
legacy code builds such a wrapper on purpose at C:5298). A branch that is
"one block statement" therefore behaves differently from the same statements
unwrapped. `Js_output.output_as_block` peels a block that is the only
statement of an output (`unnest_block` (B:1565)) and nothing else. Lists are
flattened once per unit, after lowering, by the rule that replaces
`apply_js_flatten_pass` (A.6 pass 1). This corrects C.2 row 10 (section 9).

### 1.4 The value of an output

`Out::value` follows `Js_output`:

- `Value(_)`: `value` is present unless `finished` is `True`;
- `Effect(Tail::No)`: `value` may be present; it is an expression whose effect
  has not been emitted yet. The consumer either makes it a statement
  (`output_as_block`: `compiled_to_effect_block` (C:4752), through
  `push_effect_expression` (O:339)), or joins it with the next output's value by a
  comma (`append_output`: `append_effect_output` (C:4715)). This is the difference
  between the legacy families K2 and K3 of section 2: the same continuation,
  consumed in two ways;
- `Declare`, `Assign`, `Effect(Tail::Return(_))`: `value` is absent.

Converting a value output to another continuation is
`Js_output.output_of_block_and_expression` (`js_output.ml:54-64`): append
`let id = v` (`declare_compiled` (C:6648)), `id = v` (`assign_compiled` (C:6667)),
`return v` and `finished = True` (`return_compiled` (C:6658)), or nothing. A
finished value output is left as it is.

### 1.5 Probing: one lowering where the legacy code compiles twice

The legacy code and OCaml decide the form of a conditional by compiling its
branches as values and looking at whether the results need statements, then
compiling the branches again for the real continuation. Done literally this
is exponential in the nesting depth of conditionals whose branches need
statements, and it is the largest violation of "one pass" in today's code.
Section 3.6 gives the passes the legacy code makes in each continuation.

The new lowering lowers every node once. The entry point for a branch is

```rust
fn probe(&mut self, cx: Cx, node: NodeId) -> Probed;
enum Probed {
    Free(Free),   // needs no statement as a value
    Out(Out),     // lowered for `cx`
}
enum Free {       // a deferred combination of already lowered J expressions
    Leaf(NodeId),
    Cond { test: NodeId, then_: Box<Free>, else_: Box<Free> },
    Seq  { first: NodeId, second: Box<Free> },  // head's value, 3.4
}
```

(`Free` is drawn as a tree for clarity; it is stored in a small pool of the
lowering, since a module has few of them alive at once.)

`probe(cx, n)` answers the question the legacy first pass asks, "does `n`
compile to a value with no statements", and, if the answer is no, has already
lowered `n` for `cx`, which is the continuation of the legacy second pass.

- An **expression construct** (`Var`, `Global`, `Const`, `Fun`, `Apply` that
  is not a self tail call, `Prim` other than the short circuits) is lowered as
  a value. With no statements it is `Free::Leaf`. With statements, the legacy
  second pass would produce the same statements followed by the conversion of
  1.4 (this is the `_ =>` arm of every legacy family: C:2534, C:2688, C:3058,
  C:5478), so the result is `Out` = statements plus conversion.
- A **structural construct** (`If`, `Seq`, the short circuits, `Let`,
  `LetRec`, `Switch`, `StrSwitch`, `Catch`, `Exit`, `Try`, `TryFinally`, the
  loops, `Assign`, `Break`, `Continue`) follows its row in section 3. `If` and
  `Seq` probe their own branches and are `Free` when the branches are. A
  short circuit lowers both operands as values once and is a `Free::Leaf`
  when the right one has no statements; otherwise it builds the form of `cx`
  from the same two outputs (3.7). The record-copy form of `Let` (3.4) is an
  expression. The others always need statements, so they are lowered for
  `cx` at once.

`realize(free, cont)` builds the J nodes of a `Free` for a continuation, by
the rule the legacy code applies in that continuation to operands that are
already expressions (section 3.6 gives it per continuation). It visits each
node of the `Free` once. A `Free` is realized exactly once, by the outermost
construct that knows the continuation.

Why this equals the legacy result: the first pass's output is used only when
every part is free, and then the result is a function of the lowered
expressions; the second pass's output is used otherwise, and for a
non-free part `probe` has produced exactly that. What a discarded pass leaves
behind is identifier numbers and loop labels; 3.8 and 4.5 deal with both.

Invariant P1 (checked by a debug assertion in `Check` mode): for every node
and continuation, the result of `probe` followed by `realize` equals lowering
the node for that continuation directly. The assertion costs a second
lowering, so it runs only on units below a size bound.

The direct lowering converts a leaf to its continuation at once instead of
deferring it. Below a branch of a conditional or the right operand of a short
circuit (`Cx::probing`) a leaf stays deferred in the direct mode as well: the
form of the conditional is a function of whether its branches are free, and
the only direct way to learn that is the legacy second lowering, which the
new lowering does not have. P1 therefore checks deferral outside conditional
branches; inside them the two modes take the same path.

`Seq` is free in every continuation when its head has no statements and its
tail is free: `Free::Seq`. In **V** and **E** it is the comma expression at
once; in **D**, **A** and **R** the head must not be emitted when the
sequence is lowered, because an enclosing conditional may still read the
branch as a value (`If(c, Seq(f(), 1), 2)` is `c ? (f(), 1) : 2` in **V**).

## 2. The contexts

One table for every function of `lam_compile*.rs`. "K" rows are contexts, "H"
rows are helpers that do not depend on the continuation, "N" rows are not part
of the lowering. The function index at the end of this section assigns every
function of C, V, P, X, A, K, T and M to a row; a reviewer checks the files
against it.

| Row | Context | Legacy functions (entry points) | Produces | Continuation in the new lowering |
| --- | --- | --- | --- | --- |
| K0 | The output algebra | `BlockOutput::{make, finished, dummy, append}` (C:89-135), `Compiled` (C:139), `OutputFinished` (C:73); `fresh_ident` (X:1445), `fresh_tmp_ident` (X:1449) | | `Out`, `append`, the statement stack (1.3); `Bir::new_var_id` |
| K1 | Value, not tail | `compile_expr` (C:1529), `compile_switch` (V:468), `compile_string_switch` (V:728), `compile_short_circuit_expr` (C:2794) | `Compiled`: statements, an expression, `finished` | `Cont::Value(Tail::No)` |
| K2 | Effect, not tail, value kept | `compile_effect_output` (C:4603), `append_effect_output` (C:4715), `compiled_from_effect_block` (C:7465) | `Compiled` whose expression is still to be emitted for its effect | `Cont::Effect(Tail::No)`, the caller reads `Out::value` (1.4) |
| K3 | Effect, not tail, as a block | `compile_effect_block_output` (C:2554), `compile_effect_block_inner` (C:2593), `compile_if_effect_block` (C:4761), `compile_switch_effect_block` (C:5800), `compile_effect_if` (V:1123) | `BlockOutput` | `Cont::Effect(Tail::No)` followed by `output_as_block` |
| K4 | Declare | `compile_let_binding_output` (C:2411), `compile_if_binding_block` (C:2699), `compile_switch_binding_block` (C:2750), `compile_string_switch_binding_block` (C:2775), `compile_short_circuit_binding_block` (C:2859) | `BlockOutput` ending in the declaration of `id` | `Cont::Declare(kind, id)` |
| K5 | Assign | `compile_assign_to_target_output` (C:5331), `compile_if_assignment_block` (C:4873), `compile_test_assignment_block` (C:4895), `compile_switch_assignment_block` (C:5485), `compile_switch_value_block` (C:5306) | `BlockOutput` assigning `id` on every path that falls through | `Cont::Assign(id)` |
| K6 | Return | `compile_return_output` (C:3067), `compile_return_output_inner` (C:2924), `compile_if_return_output` (C:5144), `compile_switch_return_block` (C:5652), `compile_test_return_block_with_fallback` (C:5231) | `BlockOutput` in which every path returns, throws or jumps | `Cont::Effect(Tail::Return(Ret::Named { loop_: None, in_catch }))` |
| K7 | Return, in a function compiled as a self tail call loop | `compile_recursive_function_expr` (C:3989), `compile_tail_loop_return_output_inner` (C:4174), `compile_tail_loop_if_return_output` (C:4086), `try_compile_self_tailcall_block` (C:4558), `function_has_self_tailcall` (C:6772) | as K6; a self call becomes assignments and `continue` | `Ret::Named { loop_: Some(r), in_catch }`; no separate function (5.1) |
| K8 | Return, in the body of a `try` | `with_try_body_context` (C:3543) (`try_body_depth`, C:417) | as K6; never a loop jump, never the cheap exit form | `Ret::InTry` |
| K9 | Return of a function that returns unit | `with_return_unit_context` (C:3532) (`return_unit_stack`, C:416), `compile_if_unit_return_tail_block` (C:3579), `lambda_is_trivial_unit_undefined` (C:3550) | as K6, with one extra form for a conditional whose branches are both the unit value | `Cx::return_unit` (3.6, row R4) |
| K10 | Function body | `with_function_scope` (C:1997), `function_expr` (C:562); special cases `compile_eta_wrapped_runtime_alias` (X:443), `try_compile_identity_module_return_expr` (X:468) | a `JFun` | a fresh `Cx`: `Effect(Return(Named { loop_: None or the function's own record, in_catch: false }))`, empty jump stack, `switch_depth = 0`, no loop frames (`lam_compile.ml:2006-2032`) |
| K11 | Switch depth, loops, labels | `with_switch_depth` (C:1988), `push_loop` (C:2044), `pop_loop` (C:2050), `ensure_current_loop_label` (C:2059), `with_fresh_loop_label_counter` (C:2034), `continues_toplevel_spine` (C:1513) | `loop_N` labels and labelled `break`/`continue` | `Cx::switch_depth`, `Cx::loops`, the label schedule (4.5) |
| K12 | Exits, explicit form | `flatten_nested_caches` (C:190), `compile_staticcatch_effect_output` (C:3378) and its three siblings, the four `compile_multi_staticcatch_effect_output` (C:3267) siblings, `emit_multi_staticcatch_prelude` (C:6441), `compile_exit_dispatch` (C:6528), `compile_static_raise_jump_output` (C:3173), `next_static_jump_exit_code` (C:6334) | `let exit = 0`, the handler parameters, the body, a dispatch on `exit` | a jump-stack entry with `order > 0`; one function for all continuations (4.1) |
| K13 | Exits, cheap form (the handler follows the body) | `compile_fallthrough_staticcatch_return_output` (C:3463), `compile_fallthrough_static_raise_return_output` (C:3485), `with_fallthrough_return_handler` (C:3516) | the handler parameters, the body, the handler | a jump-stack entry with `order = -1` (`add_pseudo_jmp`) |
| K14 | Exits, choice of the form | `compile_staticcatch_in_return` (C:3091), `staticcatch_takes_pseudo_jump` and the predicates in the index (before S3.5: `uses_fallthrough_staticcatch_return`, `uses_pseudo_fallthrough_staticcatch_return`, `return_staticcatch_requires_explicit_jump` and eighteen more, deleted there, 4.6) | a boolean | one test: the continuation is `Effect(Return(Named { in_catch: false, .. }))`, the flattened table has one handler, and the handler has no `HAS_EXIT` flag (4.1). No walk |
| K15 | Exits, handler substituted at the raise | `with_static_handler` (C:6075), `resolve_static_raise` (C:6113), `compile_hoisted_static_raise_chain_return_tail` (C:3932) | the handler's code at the raise site | none. Open (Q1): the form is reachable only for a catch whose body has no exit to its label |
| H1 | Calls | `compile_apply_call_inner` (C:1144), `apply_with_arity` (C:1341), `call_info_of_apply_status` (C:320) | `JCall` | 3.3 |
| H2 | Fields and calls of another module | `compile_external_field_apply` (C:1266), `resolve_cmj_module_field_arity` (C:1222), `resolve_cmj_module_field_lambda` (C:1211), `resolve_cmj_module_field_constant` (K:163) | `JQualified`, a constant, or an inlined body | 3.3 |
| H3 | Short circuits | `short_circuit_primitive` (C:301), `ShortCircuitOp` (C:269-292) | | 3.7 |
| H5 | Switch construction | `grouped_switch_cases` (C:442), `stable_group_switch_cases` (V:180), `Sw`, `StrSw` (C:7866-7938), `with_block_source_loc` (C:2578) | case groups, clauses | 3.9 |
| H6 | `let rec` | `compile_recursive_bindings_output` (C:2215), `compile_recursive_binding` (C:2244), `compile_recursive_self_binding_makeblock` (C:2293), `recursive_dummy_object_expr` (C:2345), `sort_recursive_binding_group` (C:6710) | declarations, `updateDummy` calls | 5.2 |
| H7 | Loops | `compile_for_loop` (C:2074), `compile_for_of` (C:2154), `lower_ocaml_for_range_direction` (C:6717); `While`, `Break`, `Continue` arms of `compile_expr` (C:1529) | `SWhile`, `SForRange`, `SForOf`, `SBreak`, `SContinue` | 3.11 |
| H8 | `try` | `try_statement` (C:1391), `compile_try_finally` (C:1400) | `STry` | 5.3 |
| H9 | Record copy with updates | `try_compile_record_spread` (C:1450), `collect_record_spread_overrides` (C:1424) | a `JObject` with a spread | 3.4 |
| H10 | Primitives | `compile_primitive` (P:32), `compile_primitive_js` (P:188), the comparison functions of P, `int32_div_expr` (C:6033), `runtime_call_expr` (C:6019), the option functions of X (`some_expr` (X:709), `null_to_opt_expr` (X:668), ...) | J expressions | 3.5 |
| H11 | Source locations | `source_loc` (C:911), `source_loc_of_lam` (C:915), `primitive_uses_default_compilation` (C:7846) | the location of an expression or of a clause's first statement | `HAS_LOC` and the cold array (B.2); 3.12 |
| H12 | Constants and fields | `compile_constant` (K:60), `compile_field_access` (K:186), `compile_set_field` (K:246), `compile_flat_make_field` (P:117), `static_index` (X:1441), `awaited_units` (M:401) | J literals, `JDot`, `JIndex` | 3.2, 3.5 |
| H13 | Argument sequencing | `compile_arguments` (A:249), `sequence_arguments` (A:191), `evaluate_now` (A:116), `delay_safe` (A:28), `extend_assignable` (A:280) | statements that hold earlier arguments, the argument expressions | 3.3 |
| H14 | Externals | `compile_js_call` (X:1202), `compile_js_object_create` (X:972), `assemble_external_args` (X:959), `hold_external_args` (X:254), `external_module_id` (X:581), `compile_js_object_get` (P:84) | calls, `new`, member reads, object literals | S3.8 (section 8) |
| H15 | JSX | `compile_jsx` (X:1158), `jsx_callee` (X:1143) | `JJsx` | S3.9 |
| H16 | Dynamic import | `compile_import` (X:1369), `wrap_then_path` (X:1341), `import_of_path` (X:1360) | `import(...)`, `.then(...)` | S3.9 |
| H17 | Untagged variant dispatch | `compile_untagged_switch` (V:571), `emit_untagged_tree` (V:336), `emit_untagged_clause` (V:400); the plan is `untagged_dispatch.rs` | `typeof`, `Array.isArray`, `instanceof` tests and switches | 3.9 |
| H18 | Named variant dispatch | `dispatch_named_variant_branches` (V:987), `bind_switch_scrutinee_once` (V:944), `is_int_tag` (V:244), `variant_tag_expr` (V:1010) | `typeof x !== "object"`, tag reads | 3.9 |
| N1 | Construction and driving | `LambdaCompiler::new` (C:481), `compile_deps_program_in_arena` (C:663), the `compile_program*` and `take_*` functions | | `bir::lower::unit`; the driver (A.1) |
| N2 | Exports | `coerce_toplevel_exports_with_name_reservations` (C:987), `drop_toplevel_pure_sequence_heads` (C:7803), `lam_coercion.rs` | the export list, rebound exports, name reservations | not in S3.3 to S3.9: section 8.2 |
| N3 | Summaries | `module_side_effect_reason` (C:7419), `collect_cmj_export_constants_from_simplified_lambda` (C:7142), `cmj_export_arities` (M:483) | A.8 | S6 |
| N4 | Import list | `OcamlModuleSet` (C:6957), `ocaml_sort_modules` (C:7010), `collect_modules_from_js_block` (C:7673), `populate_required_modules` (C:7341) | A.8 | emit step (C.2 row 14) |
| N5 | Lambda passes | `simplify_in_arena` (M:75), `handle_exports` (M:139), `add_flat_make_aliases` (M:237), `LamStats` (T) | | S4 |
| N6 | Tests | | | deleted with the legacy code (G.4) |
| N7 | Decoration comments | `pointer_info_comment_text` (C:7781), `commented_number` (K:55) | `/* [] */0` | carried on J nodes until S3.10, because the gate prints with the legacy printer (8.1); then dropped (E.4.2) |

Two names are shared by functions of different rows, and the index shows each
once, under N1: `new` (C:258 is K7, C:481 is N1, C:6963 is N4) and `default`
(C:436 is N1, C:7934 is H5).

Contexts that exist in OCaml and have no legacy function:

| OCaml | Legacy | New lowering |
| --- | --- | --- |
| `NeedValue (Maybe_tail_is_return _)`: a value in tail position, used for the branches of a conditional in a return continuation (`lam_compile.ml:1636-1644`), where a self tail call still becomes the loop jump (`lam_compile.ml:1745-1749`) | approximated: `compile_tail_loop_if_return_output` (C:4086) asks `function_has_self_tailcall` (C:6772) of each branch before compiling it as a plain value | `Cont::Value(Tail::Return(_))`, used by `probe` in a return continuation |
| `in_staticcatch` on the tail | the three stacks being non-empty, and row K14 | `Ret::Named::in_catch` |
| `exit_id` created for every static catch, also the cheap form (`lam_compile.ml:1172`) | created only for the explicit form (C:3356) | as the legacy code; an unused identifier is not observable |

### Function index

Every function name of the files below, by row.

**C: `lambda/lam_compile.rs`** (277 function names)

| Row | Functions (line) |
| --- | --- |
| K0 | `make` 89, `finished` 99, `dummy` 107, `append` 119 |
| N2 | `reusable_export_value_candidate` 172, `coerce_toplevel_exports_with_name_reservations` 987, `drop_toplevel_pure_sequence_heads` 7803 |
| K12 | `flatten_nested_caches` 190, `compile_static_raise_jump_output` 3173, `compile_multi_staticcatch_tail_loop_return_output` 3215, `compile_multi_staticcatch_assignment_output` 3241, `compile_multi_staticcatch_effect_output` 3267, `compile_multi_staticcatch_return_output` 3292, `compile_staticcatch_tail_loop_return_output` 3317, `compile_staticcatch_return_output` 3348, `compile_staticcatch_effect_output` 3378, `compile_staticcatch_assignment_output` 3408, `with_static_jump_handler` 6092, `next_static_jump_exit_code` 6334, `staticcatch_declarations` 6352, `staticcatch_exit_test` 6376, `compile_staticcatch_assignment_block` 6385, `compile_staticcatch_expr` 6398, `emit_multi_staticcatch_prelude` 6441, `pop_multi_staticcatch_handlers` 6482, `compile_grouped_staticcatch_handlers` 6493, `compile_exit_dispatch` 6528, `compile_multi_staticcatch_assignment_block` 6574, `catch_bindings` 6635 |
| N1 | `new` 258/481/6963, `default` 436/7934, `with_generator_and_options` 492, `with_module_path_resolver` 533, `with_module_path_resolver_and_jsx_preserve` 538, `with_module_path_resolver_and_options` 546, `set_flat_make_paths` 596, `compile_program` 601, `compile_program_owned` 606, `compile_deps_program` 611, `compile_deps_program_owned` 616, `compile_deps_program_with_possible_required_modules` 623, `compile_deps_program_with_possible_required_modules_owned` 637, `compile_deps_program_with_collected_possible_required_modules_owned` 650, `compile_deps_program_in_arena` 663, `take_cmj_export_constants` 958, `take_cmj_export_lambdas` 962, `take_cmj_export_arities` 966, `take_module_path_resolver` 970, `take_diagnostic` 974, `report_diagnostic` 978 |
| H3 | `default_expr` 275, `test_expr` 279, `default_lambda` 286, `short_circuit_primitive` 301 |
| H5 | `direct_switch_int` 294, `grouped_switch_cases` 442, `filtered_switch_case_refs` 461, `empty_switch_case_clause_for` 2568, `with_block_source_loc` 2578, `untagged_plan` 7873, `payload` 7889, `consts` 7893, `blocks` 7902, `fail` 7911, `cases` 7924 |
| H1 | `call_info_of_apply_status` 320, `compile_apply_call` 1129, `compile_apply_call_inner` 1144, `apply_with_arity` 1341, `aux` 1346 |
| N3 | `cmj_export_arity_to_external` 347, `cached_cmj_table` 6680, `export_binding_value` 7131, `collect_cmj_export_constants_from_simplified_lambda` 7142, `collect_cmj_export_lambdas_from_simplified_lambda` 7166, `collect_toplevel_export_bindings` 7208, `cmj_export_constant_from_lambda` 7230, `top_level_effect_group_single_ref` 7362, `push_top_level_effect_nop_ref` 7376, `collect_top_level_effect_group_refs` 7385, `module_side_effect_reason` 7419, `required_module_side_effect_reason` 7448 |
| K10 | `function_expr` 562, `with_function_scope` 1997, `enter_function_scope` 2009, `leave_function_scope` 2020 |
| H10 | `prop_name` 587, `runtime_member_expr` 5993, `builtin_runtime_call_info` 6005, `runtime_call_expr` 6019, `int32_div_expr` 6033, `int32_mod_expr` 6049, `bigint_div_expr` 6059, `bigint_mod_expr` 6067 |
| H11 | `set_source_map_enabled` 885, `set_lam_locs` 890, `lam_locs` 895, `take_lam_locs` 899, `mappable_loc` 905, `source_loc` 911, `source_loc_of_lam` 915, `find` 919, `primitive_uses_default_compilation` 7846 |
| H2 | `resolve_cmj_module_field_lambda_any` 1193, `resolve_cmj_module_field_lambda` 1211, `resolve_cmj_module_field_arity` 1222, `module_field_apply_target` 1243, `compile_external_field_apply` 1266 |
| H8 | `try_statement` 1391, `compile_try_finally` 1400 |
| H9 | `collect_record_spread_overrides` 1424, `try_compile_record_spread` 1450 |
| K11 | `continues_toplevel_spine` 1513, `with_switch_depth` 1988, `with_fresh_loop_label_counter` 2034, `push_loop` 2044, `pop_loop` 2050, `ensure_current_loop_label` 2059 |
| K1 | `compile_expr` 1529, `compile_short_circuit_expr` 2794, `compile_short_circuit_js` 2806 |
| K3 | `compile_block` 1982, `compile_effect_block` 2541, `compile_effect_block_output` 2554, `compile_effect_block_inner` 2593, `compile_if_effect_block` 4761, `compile_switch_effect_block` 5800, `compile_switch_effect_block_inner` 5814, `compile_string_switch_effect_block` 5886, `compile_string_switch_effect_block_inner` 5895 |
| H7 | `compile_for_loop` 2074, `compile_for_of` 2154, `lower_ocaml_for_range_direction` 6717 |
| H6 | `compile_recursive_bindings_output` 2215, `compile_recursive_binding` 2244, `compile_recursive_self_binding_makeblock` 2293, `recursive_dummy_object_expr` 2345, `recursive_self_binding_field_info` 2371, `letrec_bindings` 6625, `recursive_function_binding_value` 6692, `binding_is_ocaml_scc_function` 6696, `recursive_binding_group_is_function_only` 6700, `sort_recursive_binding_group` 6710 |
| K4 | `compile_let_binding` 2400, `compile_let_binding_output` 2411, `compile_if_binding_block` 2699, `compile_switch_binding_block` 2750, `compile_string_switch_binding_block` 2775, `compile_short_circuit_binding_block` 2859, `compile_declared_if_block` 4926, `prepend_declaration_or_fold_final_assignment` 5070, `declare_compiled` 6648 |
| K6 | `compile_return_block` 2917, `compile_return_output_inner` 2924, `compile_return_output` 3067, `compile_short_circuit_return_output` 3075, `reorder_fallthrough_return_clauses` 3835, `grouped_return_string_clauses` 3847, `lambda_contains_statement_value_form` 5016, `try_fold_effect_only_return_tail` 5118, `compile_if_return_output` 5144, `compile_test_return_block` 5216, `compile_test_return_block_with_fallback` 5231, `compile_switch_return_block` 5652, `compile_switch_return_block_inner` 5666, `compile_string_switch_return_block` 5749, `compile_string_switch_return_block_inner` 5758, `return_case_needs_break` 6643, `return_compiled` 6658 |
| K14 | `compile_staticcatch_in_return` 3091, `staticcatch_takes_pseudo_jump`, `any_child` 6614, `handler_has_static_raise_like_ocaml` 7509, `no_static_raise_in_handler_like_ocaml` 7520, `lambda_has_exit` 7524, `lambda_contains_static_raise_to_label` 7542. Deleted by S3.5 (4.6): `handler_returns_unit_undefined`, `staticcatch_handler_is_identity_binding`, `uses_fallthrough_staticcatch_return`, `uses_pseudo_fallthrough_staticcatch_return`, `return_staticcatch_requires_explicit_jump`, `handler_is_pure_outward_static_raise_forwarder`, `active_static_raise_target_exists`, `return_handler_requires_explicit_staticcatch_jump`, `handler_is_inlineable_pure_return_static_raise_dispatch`, `pure_return_static_raise_dispatch_has_terminal_value`, `lambda_requires_explicit_staticcatch_jump`, `lambda_contains_static_raise`, `lambda_contains_staticcatch`, `switch_cases_contain_static_raise_to_label`, `string_switch_cases_contain_static_raise_to_label`, `lambda_is_direct_static_raise_to_label`, `switch_cases_contain_nontrivial_static_raise_to_label`, `string_switch_cases_contain_nontrivial_static_raise_to_label`, `lambda_has_multiple_static_raises_to_label`, `lambda_static_raise_count_to_label`, `lambda_contains_static_raise_to_other_label` |
| K13 | `compile_fallthrough_staticcatch_tail_loop_return_output` 3439, `compile_fallthrough_staticcatch_return_output` 3463, `compile_fallthrough_static_raise_return_output` 3485, `with_fallthrough_return_handler` 3516, `active_fallthrough_return_handler` 3831 |
| K9 | `with_return_unit_context` 3532, `lambda_is_trivial_unit_undefined` 3550, `compile_if_unit_return_tail_block` 3579 |
| K8 | `with_try_body_context` 3543 |
| K15 | `should_hoist_grouped_named_string_return_tail` 3905, `compile_hoisted_named_string_return_tail` 3918, `compile_hoisted_static_raise_chain_return_tail` 3932, `with_static_handler` 6075, `resolve_static_raise` 6113 |
| K7 | `compile_recursive_function_expr` 3989, `compile_tail_loop_return_block` 4073, `compile_tail_loop_if_return_output` 4086, `compile_short_circuit_tail_loop_return_output` 4155, `compile_tail_loop_return_output_inner` 4174, `compile_tail_loop_return_output` 4362, `compile_tail_loop_switch_return_block` 4375, `compile_tail_loop_switch_return_block_inner` 4399, `compile_tail_loop_string_switch_return_block` 4491, `compile_tail_loop_string_switch_return_block_inner` 4503, `try_compile_self_tailcall_block` 4558, `block_last_is_continue` 6735, `block_last_is_non_continue_terminal` 6741, `merge_terminal_guard_fallthrough_else` 6750, `function_has_self_tailcall` 6772, `ext_ident_cmp` 6854 |
| K2 | `compile_effect_output` 4603, `append_effect_output` 4715, `compiled_to_effect_block` 4752, `compiled_from_effect_block` 7465 |
| K5 | `compile_if_assignment_block` 4873, `compile_test_assignment_block` 4895, `assignment_parts` 4978, `take_single_result_assignment` 4991, `result_assignment` 5005, `compile_switch_value_block` 5306, `compile_assign_to_target_block` 5320, `compile_assign_to_target_output` 5331, `compile_switch_assignment_block` 5485, `compile_switch_assignment_block_inner` 5509, `compile_string_switch_assignment_block` 5573, `compile_string_switch_assignment_block_inner` 5585, `normalize_if_assignment_merge_order` 6595, `assign_compiled` 6667 |
| H14 | `compile_external_arg_const` 5975 |
| N6 | `collect_required_modules` 6586 |
| N4 | `module_sort_name` 6826, `module_sort_cmp` 6833, `module_kind_rank` 6845, `ocaml_hashtbl_power_2_above` 6865, `ocaml_hash_mix_uint32` 6872, `ocaml_hash_final_mix` 6882, `ocaml_hashtbl_hash_string` 6891, `ocaml_hashtbl_hash_stamp_and_name` 6920, `ocaml_module_hash` 6929, `ocaml_module_equal` 6936, `insert` 6970, `resize` 6987, `to_vec` 6998, `ocaml_sort_modules` 7010, `maxson` 7011, `trickledown` 7034, `trickle` 7046, `bubbledown` 7051, `bubble` 7059, `trickleup` 7063, `collect_possible_required_modules_in_arena` 7101, `go` 7105, `collect_possible_required_modules_for_lambda` 7120, `collect_modules_from_lambda` 7250, `populate_required_modules` 7341, `runtime_module_id` 7657, `collect_modules_from_js_list` 7665, `collect_modules_from_js_block` 7673, `collect_modules_from_js_statement` 7679, `collect_modules_from_js_expression` 7760 |
| N7 | `pointer_info_comment_text` 7781 |

**V: `lambda/lam_compile_variant.rs`** (62 function names)

| Row | Functions (line) |
| --- | --- |
| H5 | `block_last_is_return_throw_or_continue` 41, `empty_switch_case_clause` 48, `named_payload_switch` 57, `untagged_switch` 75, `is_named` 115, `decode` 128, `stable_group_switch_cases` 180 |
| H18 | `named_variant_keys_need_bound_scrutinee` 143, `is_int_tag` 244, `switch_literal_tags` 600, `uses_named_variant_switch` 860, `literal_tag_value` 868, `switch_tag_value` 882, `named_const_cases` 886, `named_block_cases` 899, `const_switch_default` 912, `const_switch_complete` 920, `block_switch_default` 924, `block_switch_complete` 932, `variant_tag_name` 936, `bind_switch_scrutinee_once` 944, `named_variant_switch_needs_bound_scrutinee` 966, `decoded_switch_needs_bound_scrutinee` 976, `dispatch_named_variant_branches` 987, `variant_tag_expr` 1010, `switch_case_expr` 1021, `switch_case_test` 1042 |
| H17 | `class_constructor` 220, `is_instance_of` 230, `untagged_typeof_expr` 277, `untagged_test_expr` 290, `untagged_if` 319, `emit_untagged_tree` 336, `emit_untagged_clause` 400, `untagged_fallback_block` 500, `untagged_output_block` 524, `compile_untagged_plan` 547, `compile_untagged_switch` 571 |
| K1 | `compile_switch` 468, `compile_switch_inner` 631, `compile_string_switch` 728, `compile_string_switch_inner` 739 |
| K5 | `compile_small_string_switch_assignment` 1046, `compile_named_string_switch_assignment_general` 1204, `compile_named_string_switch_assignment` 1248, `compile_named_variant_switch_assignment_statements` 1660 |
| K6 | `compile_small_string_switch_return` 1088, `compile_named_string_switch_return_with_strategy` 1274, `compile_named_string_switch_return` 1432, `compile_named_variant_switch_return_statements` 1738 |
| K3 | `compile_effect_if` 1123, `normalized_if_block` 1153, `compile_small_string_switch_effect` 1161, `compile_named_string_switch_effect_with_strategy` 1584, `compile_named_string_switch_effect` 1647, `compile_named_variant_switch_effect_statements` 1873 |
| K7 | `compile_small_string_switch_tail_loop_return` 1445, `grouped_tail_loop_return_string_clauses` 1488, `compile_named_string_switch_tail_loop_return` 1543, `compile_named_variant_switch_tail_loop_return_statements` 1804 |

**P: `lambda/lam_compile_primitive.rs`** (14 function names)

| Row | Functions (line) |
| --- | --- |
| H10 | `compile_primitive` 32, `compile_debugger` 68, `compile_primitive_js` 188, `compile_object_comparison` 865, `compile_bool_comparison` 881, `compile_int_comparison` 934, `compile_string_comparison` 990, `compile_bigint_comparison` 1003, `compile_typed_min_max` 1016, `first_arg` 1036, `take_arg` 1040 |
| H14 | `compile_js_object_get` 84 |
| H12 | `compile_flat_make_field` 117, `extract_field_path` 127 |

**X: `lambda/lam_compile_external.rs`** (58 function names)

| Row | Functions (line) |
| --- | --- |
| H14 | `literal_polyvar_block` 30/370, `polyvar_dispatch_in_place` 50, `polyvar_event_in_place` 59, `duplicable` 60, `external_module_import_attributes` 79, `external_module_ident_name` 86, `capitalize_ascii_first` 93, `good_hint_name` 106, `collect_start` 115, `collect_next` 133, `js_id_name_of_hint_name` 149, `presence_unknown` 173, `external_optional_to_undefined_expr` 181, `external_option_unwrap_expr` 197, `hold_external_arg` 213, `hold_external_args` 254, `hold_external_obj_args` 278, `external_polyvar_string_expr` 344, `external_polyvar_event_exprs` 374, `external_polyvar_int_expr` 400, `external_polyvar_unwrap_expr` 421, `external_module_id` 581, `external_module_binding` 609, `translate_scoped_module_value` 621, `external_arg_effect` 741, `fuse_external_effects` 749, `add_external_effect` 755, `lower_object_external_arg_value_and_effect` 762, `lower_external_arg_values_and_effect` 782, `assemble_external_args_no_splice` 834, `keep_non_undefined_external_args` 872, `assemble_external_args_with_splice` 894, `assemble_external_args` 959, `compile_js_object_create` 972, `compile_js_call` 1202, `translate_scoped_global_value` 1417, `apply_scoped_access` 1434 |
| H10 | `pure_runtime_call_expr` 431, `optional_block` 657, `can_inline_null_to_opt` 661, `null_to_opt_expr` 668, `null_undefined_to_opt_expr` 679, `is_null_expr` 692, `is_undefined_expr` 696, `is_null_or_undefined_expr` 705, `some_expr` 709, `val_from_option_expr` 723, `is_not_none_expr` 730 |
| K10 | `compile_eta_wrapped_runtime_alias` 443, `try_compile_identity_module_return_expr` 468 |
| H15 | `jsx_callee` 1143, `compile_jsx` 1158 |
| H16 | `wrap_then_path` 1341, `import_of_path` 1360, `compile_import` 1369 |
| H12 | `static_index` 1441 |
| K0 | `fresh_ident` 1445, `fresh_tmp_ident` 1449 |

**A: `lambda/lam_compile_arguments.rs`** (28 function names)

| Row | Functions (line) |
| --- | --- |
| H13 | `delay_safe` 28, `is_okay_to_duplicate` 69, `runs_no_code` 90, `defines_pure_values` 96, `define_strict_variable` 104, `evaluate_now` 116, `evaluate_all_now` 178, `sequence_arguments` 191, `compile_arguments` 249, `compile_each_argument` 263, `extend_assignable` 280, `restore_assignable` 290 |
| N6 | `call` 303, `is_array` 308, `exp_statement` 314, `later_statement` 321, `evaluate_now_drops_pure_array_is_array_in_sequence` 327, `evaluate_now_keeps_array_is_array_with_effectful_argument` 341, `evaluate_now_splits_nested_sequences_left_to_right` 355, `sequence_arguments_holds_method_object_not_property_read` 378, `sequence_arguments_allocates_temporaries_right_to_left` 408, `unit_assign` 434, `function_body` 438, `assignable_names` 448, `assigned_variables_collects_targets_by_identity` 458, `extended_assignable_changes_hold_decision_until_restored` 481, `nested_assignable_extensions_restore_exactly` 515, `sequence_arguments_handles_long_argument_lists` 577 |

**K: `lambda/lam_compile_const.rs`** (10 function names)

| Row | Functions (line) |
| --- | --- |
| H12 | `some_none_depth` 22, `nested_some_none` 26, `compile_some_constant` 34, `compile_runtime_int` 48, `commented_number` 55, `compile_constant` 60, `compile_field_access` 186, `compile_set_field` 246 |
| H2 | `cmj_export_constant_expr` 155, `resolve_cmj_module_field_constant` 163 |

**T: `lambda/lam_compile_context.rs`** (6 function names)

| Row | Functions (line) |
| --- | --- |
| N5 | `new` 129, `is_export` 141, `get_kind` 146, `set_kind` 151 |
| N6 | `test_lam_stats_creation` 161, `test_id_kind` 172 |

**M: `lambda/lam_compile_main.rs`** (22 function names)

| Row | Functions (line) |
| --- | --- |
| N5 | `module_export` 43, `simplify_for_js_backend` 63, `simplify_in_arena` 75, `handle_exports` 139, `add_flat_make_aliases` 237, `is_followed_binding` 261, `flat_make_alias` 275, `is_path` 284, `resolve` 299, `collect_groups` 415, `append_aliases` 437 |
| H12 | `is_awaited_unit` 384, `awaited_units` 401, `collect` 402 |
| N3 | `cmj_export_arities` 483 |
| N6 | `id` 552, `step` 555, `export_node` 561, `run` 569, `export_values` 574, `flat_alias_of_another_unit_reads_its_flat_export_path` 592, `flat_aliases_follow_the_paths_and_are_exported_in_path_order` 626 |


## 3. The constructs

### 3.1 How to read this section

One subsection per group of level L operations (B.3). For each: what is
produced in each continuation, the order in which sub-terms are lowered and
identifiers are created, the facts read, and the legacy function replaced.

Abbreviations for continuations: **V** `Value(No)`, **E** `Effect(No)`,
**D** `Declare(kind, id)`, **A** `Assign(id)`, **R** `Effect(Return(_))`,
**VR** `Value(Return(_))`. "conv" is the conversion of a value output to the
continuation (1.4). `X(n)` is "lower `n` in continuation X".

Two rules hold for every construct and are not repeated.

- **Order.** Sub-terms are lowered in the order given. Where a construct
  probes (1.5), the order is that of the single lowering.
- **Append.** `append(x, y)` is `Js_output.append_output`: both are lowered
  first, then a finished `x` drops `y`.

"Incidental" marks behaviour that follows from how today's compiler happens
to run and not from the construct. Each says where the rule lives in the new
design: in the lowering, or as a J normalising rule (section 6).

### 3.2 `Var`, `Global`, `Const`

| Op | J nodes | Facts | Legacy |
| --- | --- | --- | --- |
| `Var(v)` | `Var(v)` | none | `compile_expr` (C:1529) |
| `Global(m)` | `JQualified(m, no member)`, module kind `Ml` | none; the module is entered in `imports` when the node is built | `compile_expr` (C:1529) |
| `Const(c)` | a literal: `JNumber`, `JStr`, `JBool`, `JNull`, `JUndefined` (with `is_unit`), `JBlockLit` for constant blocks, `JOptional` for `Some` of a constant | none | `compile_constant` (K:60), `compile_some_constant` (K:34), `nested_some_none` (K:26) |

In every continuation: conv of the node. In **E** the output has a value and
no statement; the consumer drops a value without effects.

A field of another module, `Prim(Pfield(Module name), [Global m])`, is not a
`Global` lowering: see 3.3.

### 3.3 `Apply`

**Order** (`compile_apply_call_inner` (C:1144)):

1. If the application has status `Na` and its callee is an application with
   status `Na`, the two are merged into one application of the inner callee
   to both argument lists (C:1151-1166, `LamArena::apply` is called, so rows
   N13 and N14 of C.5 can fire) and the merged node is lowered instead. This
   is a level L rewrite done during lowering. In the new design it is a rule
   of round 7 (C.3), which is the last point where `Na` applications are
   final; the lowering then never sees the shape. Until S4 ports round 7, the
   lowering applies it itself.
2. If the callee is `Pfield(Module name)` of a `Global`: cross-module call,
   below.
3. Otherwise the callee and the arguments are lowered left to right in **V**
   (`compile_each_argument` (A:263)), then sequenced (`sequence_arguments` (A:191)).

**Sequencing** (also used by every primitive and literal). Each argument has
statements and a value. When no argument after the first has statements, the
statements are concatenated and the values used as they are. Otherwise the
arguments are visited **right to left**: an argument with statements after it
is held in a temporary (`let tmp = value`, kind `Strict`) unless it is
`delay_safe` or it runs no code and the statements after it only define
values that run none (`evaluate_now` (A:116), `delay_safe` (A:28),
`runs_no_code` (A:90), `defines_pure_values` (A:96)). A sequence value has its
leading effects made statements; a literal (array, block, object) is kept and
its elements are held instead. With `method_callee` (the callee is a
`PjsObjectGet`), the receiver is held and the property read stays in the
call. Temporaries are therefore created right to left, after every argument
was lowered. Tested by `sequence_arguments_allocates_temporaries_right_to_left`
(A:408).

Facts read: `ASSIGNED` of a variable (`delay_safe`; a variable some `Assign`
writes may change before the call), `JS_GLOBAL`, and the J purity bits of the
argument values (section 7). The legacy code walks each value for these; the
new code reads flags.

**The call.** `JCall(callee, args)` with call information from the
application's status (`call_info_of_apply_status` (C:320)): `InferFull` gives
`MlCall`/`Full`, `Na` gives `MlCall`/`Na`, `Uncurry` gives `Na`/`Full`. The
status was set by round 4 (`alpha_conversion`); the lowering reads no arity
here. The call information is not printed, but the printer's eta reduction
(`eta_reduce_function_body`, A.7) and J1 read it, so it is part of the J node
and of the gate (8.1).

**Reachable J rules.** The call, the function built for a partial application,
and strict temporary declarations are plain constructors. Assignment conversion
does not match J-E4 folding triggers. Calls make retained sequence heads effectful:
J-M1 joins statement-free sequence values and J-M14 emits or splits discarded
effects. J-M14 removes pure numeric/undefined leaves, so its emitted call leaves
cannot trigger J-S1. These are the section-6 rows needed by the application slice.

**Cross-module call** (`compile_external_field_apply` (C:1266)):

- with cross-module inlining on, a callee that is a closed function of
  another module with as many parameters as arguments, whose attributes allow
  inlining, is imported, beta-reduced
  (`lam_beta_reduce::propagate_beta_reduce_with_map`) and the result lowered
  in the same continuation. This is a level L rewrite inside the lowering. In
  the new design it is the rule `inline_external` of rounds 2, 3 and 5 (C.4);
  what today's lowering adds is one more attempt after round 7. S3.8 keeps the
  attempt in the lowering and returns `Unsupported("cross-module inline")`
  until then. Open (Q6): whether the attempt in the lowering ever fires after
  the three rounds had their chance;
- otherwise the arguments are lowered and sequenced (no callee among them),
  the callee is `JQualified(m, name)`, and the call form comes from the
  status: `InferFull` and `Uncurry` as above; `Na` reads the **arity of the
  export** from the other module's summary
  (`resolve_cmj_module_field_arity` (C:1222)) and builds
  `apply_with_arity` (C:1341): one full call per saturated arity group; a partial
  application whose arguments all have no side effects becomes a function
  with fresh parameters named `param`, created left to right; anything else
  is one call with unknown arity.

**Continuations.** **V**, **E**, **D**, **A**: conv of the call. **R**:
`return call`, finished. **R** with `loop_: Some(r)` and callee `Var` of
`r`'s function: the loop jump (5.1); the same in **VR**.

Legacy: `compile_apply_call` (C:1129), arms `Apply` of `compile_expr` (C:1529),
`compile_return_output_inner` (C:2924) (C:2959),
`compile_assign_to_target_output` (C:5331) (C:5359), `compile_effect_output` (C:4603)
(C:4633).

### 3.4 `Fun`, `Let`, `Seq`

**`Fun`.** Two special cases are tried first, in this order, on the function
node: `compile_eta_wrapped_runtime_alias` (X:443) (a function that only forwards
its parameters to a primitive that has a runtime function becomes that
runtime member) and `try_compile_identity_module_return_expr` (X:468) for the
body. Otherwise the body is lowered in a fresh context (row K10) in **R**, and
the node is `JFun` with the header's attributes (`return_unit`, `async`,
directive) and no parameters when the function has `one_unit_arg`. The
function's free variables are not computed (naming does, E.3). A `Fun` bound
by `LetRec` goes through 5.1 instead.

**`Let(kind, id, value, body)`** in continuation k:

1. except in **D**, the record-copy form is tried: `value` is `Pduprecord(init)` and `body` is
   a sequence of `Psetfield`s of `id` that ends in `id`
   (`try_compile_record_spread` (C:1450)). Then `init` and each written value are
   lowered in **V**, left to right, statements concatenated (not sequenced),
   and the result is `JObject` with a record spread of `init` and the written
   fields **in reverse source order**; conv to k. Incidental: the reversal
   comes from a fold that prepends (C:1487); it stays in the lowering;
2. otherwise `D(kind, id)(value)`, then `k(body)`, appended.

S3.9 oracle correction: `compile_let_binding_output` does not try the
record-copy collapse in its `Let` arm. For `let copy = Pduprecord(source) in
copy`, **D** emits `let copy = {...source}; let result = copy;`, unlike the
other continuations. The lowering preserves that declaration boundary.

Finished-binding detail (`compile_expr`'s `Let` arm, versus
`compile_effect_output`): in **V**, a finished binding discards the body's
statements but retains its value and keeps `finished = True`. In **E** the
value becomes `undefined`; in **D**, **A**, **R** it is absent. The retained
export-block value is needed by the shared export coercion to declare the
exports of a unit that throws. Truncated J statements must be released, not
merely removed from the statement stack. The S3.3c oracle and shared-tail
tests cover both cases.

`D(kind, id)` of a value that is itself a `Let` or `Seq` continues through
it: the inner binding or the head first, then `D(kind, id)` of the rest
(the `Let` and `Sequence` arms, C:2419 and C:2487). A sequence that ends in the unit value thus
declares `let id;` (rule J-S1 of section 6 drops the `undefined`).

**`Seq(a, b)`** in k: `E(a)`, then `k(b)`, appended. In **V** and in **E**
with the value kept, `a`'s value stays an expression: when both outputs have
no statements the result is `a, b` built by `js_seq` (E:399); when `a` has no
effect it is dropped (`append_effect_output` (C:4715)). In the other continuations
`a`'s value becomes a statement (`push_effect_expression` (O:339), which splits a
comma expression into statements and drops parts without effect).

The head is in **E** in every legacy pass, so it is lowered once and never
probed. Reading its value back is `compiled_from_effect_block` (C:7465): a
structural head (a conditional, a switch, a catch, a `try`) is lowered to
statements first, and if the result is exactly one expression statement, that
expression is the value again. A `Seq` is free (1.5) when the head, read back
this way, has no statements and the second part is free.

**Top-level groups.** The legacy code lowers the whole unit as one expression
and recognises the top-level spine while doing so: a `Let`, `LetRec` or `Seq`
whose rest is another `Let`, `LetRec`, `Seq` or the export block, outside any
loop (`continues_toplevel_spine` (C:1513)), lowers its binding or head with a fresh
label counter. OCaml lowers a list of groups (`lam_compile_main.ml`). The new
lowering walks the spine in a loop of its own (no recursion on the spine,
which is as long as the module) and lowers each group; the label schedule is
per group (4.5). Heads of the top-level spine that are a variable, constant
or function are dropped before lowering
(`drop_toplevel_pure_sequence_heads` (C:7803)); in the new design `handle_exports`
of round 7 does not build them.

Legacy irregularity (read): `LetRec` has an arm in K1, K3 and K6 only. In K2,
K4, K5 and K7 it falls to the default arm, so its body is lowered in **V** and
converted. OCaml lowers the body in the continuation of the `LetRec`
(`lam_compile.ml:2046-2056`). The new lowering follows OCaml. Open (Q4):
whether the difference is reachable (a `LetRec` in **D** is removed by
`deep_flatten`; in **A** it needs a `let rec` at the end of a branch whose
value is assigned).

### 3.5 `Prim`

Order (`compile_primitive` (P:32)): the flat `make` read
(`compile_flat_make_field` (P:117)), `Pdebugger` and `PjsObjectGet` are tried
first; otherwise the arguments are lowered in **V** left to right, externals
hold their arguments (`hold_external_args` (X:254), `hold_external_obj_args` (X:278)),
the arguments are sequenced (3.3), and the primitive builds its J expression
from the argument values (`compile_primitive_js` (P:188)). In every continuation:
conv of the result. The short circuits are 3.7.

Statements a primitive adds itself: `Praise` adds `throw v` and is
**finished** (the only primitive that is); `Pdebugger` lowers its argument in
**E** and adds `debugger`; `PjsObjectGet` holds a receiver that has statements
and cannot be duplicated in a fresh `tmp` (`compile_js_object_get` (P:84));
externals add what S3.8 specifies.

| Group | Primitives | J nodes | Rewriting constructors used (section 6) |
| --- | --- | --- | --- |
| Lengths | `Pstringlength`, `Parraylength`, `PfnArity` | `JLength` | J-E2 |
| Templates | `Ptemplate`, `PtaggedTemplate` | `JTemplate`, `JTagged` | J-M12 |
| Indexing | `Pstringrefs/u`, `Parrayrefu`, `Parrayrefs`, `Parraysetu` | `JIndex`, runtime calls for the checked forms | |
| Int arithmetic | `Paddint`, `Psubint`, `Pmulint`, `Pdivint`, `Pmodint`, `Ppowint`, `Pnegint`, `Pnotint`, `Pandint`, `Porint`, `Pxorint`, `Plslint`, `Plsrint`, `Pasrint`, `Pintoffloat` | `JBin`, `\| 0`, runtime `Primitive_int.div`/`mod_` | J-M3 to J-M10, `int32_div_expr` (C:6033), `int32_mod_expr` (C:6049) |
| Float and bigint arithmetic | `P*float`, `P*bigint` | `JBin`; runtime `Primitive_bigint.div`/`mod_` when division checks are on | J-E4 |
| Comparisons | `Pintcomp`, `Pfloatcomp`, `Pboolcomp`, `Pstringcomp`, `Pbigintcomp`, `Pobjcomp`, `Pjscomp`, the `*order`, `*min`, `*max` | `JBin`, a folded `JBool`, or a runtime call | J-E4, J-M2 and the literal folds of `compile_bool_comparison` (P:881), `compile_int_comparison` (P:934), `compile_string_comparison` (P:990), `compile_bigint_comparison` (P:1003) |
| Booleans | `Pnot` | | J-E8 |
| Options and null | `Psome`, `PsomeNotNest`, `PvalFromOption`, `PvalFromOptionNotNest`, `PisNotNone`, `PnullToOpt`, `PnullUndefinedToOpt`, `PisNull`, `PisUndefined`, `PisNullUndefined` | `JOptional`, runtime `Primitive_option` calls, `JIsNullish`, `===` tests | J-E3, the functions of X listed under H10 |
| Blocks and fields | `Pmakeblock`, `Pmakelist`, `Pmakearray`, `Pfield`, `Psetfield`, `Pduprecord`, `PrecordRest`, `Pobjtag`, `Pobjsize`, `PisPolyVarBlock` | `JBlockLit`, `JArray`, `JDot`, `JIndex`, assignment | J-M11 (`compile_field_access` (K:186)) |
| Dicts and spreads | `Pmakedict`, `PdictHas`, `PdictSpread`, `ParraySpread`, `PlistSpread` | `JObject`, `JIn`, runtime calls | |
| Strings | `Pstringadd` | `JStrAppend` | J-E1 |
| Hash | `Phash`, `PhashMixint`, `PhashMixstring`, `PhashFinalmix` | runtime calls | |
| Identity | `Pidentity`, `Pfloatofint`, `Pignore`, `Ptypeof`, `PrawJsCode`, `PcreateExtension`, `PinitMod`, `PupdateMod` | the argument; `JSeq(v, unit)`; `JTypeof`; `JRaw`; runtime calls (the exception one is marked pure) | J-M9 |
| Control | `Praise`, `Pdebugger` | `SThrow`, `SDebugger` | |
| Async | `Pawait` | `JAwait` | |
| Externals | `PjsCall`, `PjsApply`, `PjsObjectCreate`, `PjsObjectGet`, `PjsObjectSet`, `PjsFnMethod` | S3.8 | |
| JSX, import | `Pjsx`, `Pimport` | S3.9 | |

The row of every primitive is the arm of `compile_primitive_js` (P:188) with its
name; the port is arm by arm.

Details verified by the S3.3c primitive oracle tests:

- Both `Pstringrefs` and `Pstringrefu` call `Primitive_string.getChar`;
  only `Parrayrefu` is a direct index. "Checked forms" does not distinguish
  the two string primitives.
- `Pdebugger` uses `compile_debugger`, not the nominal arm in
  `compile_primitive_js`: its result is unit `undefined` (`is_unit = true`),
  after lowering its arguments in **E**. `Praise`'s placeholder is non-unit
  `undefined` in a value continuation; it never emits a binding or return.
- `Pmakedict` recognizes exactly one array argument and extracts only
  two-field block entries whose key is a string literal. Other entries are
  skipped; a non-array argument produces `undefined`. `PdictSpread` flattens
  objects only when every property is a literal key or a symbol.
- `PisNotNone` folds an optional block to `true` without a purity guard,
  including an effectful payload. `Psome` marks the optional block as an
  identity for null, objects, numbers, blocks, arrays, strings and plain
  template literals, not for booleans or interpolated templates.
- Null-to-option conversion is inlined only for a variable, null or
  undefined; qualified reads and all other expressions call the runtime.

These are lowering policies, not new J constructor rules. Facts read by primitives: the option
`check_div_by_zero`; for `Pfield(Module)` of a `Global`, the other module's
constant exports (`resolve_cmj_module_field_constant` (K:163): `true`, `false`,
`null`, `undefined` are inlined, anything else is `JQualified(m, name)`); for
the flat `make` read, the set of awaited units.

Incidental: `fold_prim` at level L (C.5 N1, N2) and the J folds of section 6
overlap (integer arithmetic on two literals is folded by both). The lowering
does not depend on which one fires; both stay.

### 3.5.1 Externals

This table specifies S3.8 against X (`lam_compile_external.rs`), P
(`lam_compile_primitive.rs`) and C (`lam_compile.rs`). Line numbers here are
those at revision `73a1901ea0`; C's earlier index predates intervening ports.
These are lowering policies, not additional J normalisation rules.

**Continuations and order.** Let `b; e` be the prelude and expression in the
following table. Every row produces **V** `b; e`, **D** `b; let id = e`,
**A** `b; id = e`, **E** `b` with `e` retained for the effect consumer, and
**R** `b; return e` (finished), through the conversions of 1.4. The normal
unit-return and pure-effect rules still apply. Primitive arguments are lowered
left to right in **V**, then held as specified below, then sequenced by 3.3.
Only object creation and the special object-get path add their own statements.

| Row | Primitive | Expression and prelude | Legacy |
| --- | --- | --- | --- |
| X1 | `PjsCall` | The declaration-kind table below, with removed argument effects sequenced before the expression | `compile_js_call` (X:1202), `add_external_effect` (X:755) |
| X2 | `PjsApply` | Plain default-info call of the first value with the rest; no values gives non-unit undefined. No FFI argument conversion or variadic assembly | P:229; unlike `compile_js_call` (X:1202) |
| X3 | `PjsObjectCreate` | Object literal, possibly a variable object followed by conditional optional-field assignments; result is the object variable | `compile_js_object_create` (X:972) |
| X4 | `PjsObjectGet(name)` | Static member read. With exactly one receiver, lower it first; if its prelude is nonempty and it cannot be duplicated (with record fields allowed), append a strict `tmp` binding and read its member. Otherwise read directly | P:84; `static_index` (X:1441) |
| X5 | `PjsObjectSet(name)` | Exactly receiver and value: plain sequence `(receiver.name = value, unit undefined)`. Other arities give non-unit undefined | P:827; member construction `static_index` (X:1441) |
| X6 | `PjsFnMethod` | First value, marking an actual function `is_method = true` without changing its location; non-function unchanged, missing value non-unit undefined | P:813; ordinary function aliases are separate (`compile_eta_wrapped_runtime_alias`, X:443) |

**Holding precedes sequencing.** A hold goes after that argument's own
statements, before the generic right-to-left sequencing pass. Thus an argument
needing a statement also forces earlier unsafe argument values to be evaluated
before it. Do not first flatten all argument preludes and then add FFI holds.

| Row | Decision | Result | Legacy |
| --- | --- | --- | --- |
| X7 | Call argument/spec pairing | Constants consume no runtime argument; hold other arguments in source order, retaining unmatched remaining arguments | `hold_external_args` (X:254) |
| X8 | Event variant can be read in place | A literal polyvariant block, or a duplicable value, needs no hold. Duplicable means undefined, bool, number, string, template, qualified read, non-global variable, positioned field of a duplicable value, index of two duplicable values, or conditional of three duplicable values | `literal_polyvar_block` (X:30), `polyvar_event_in_place` (X:59), nested `duplicable` (X:60) |
| X9 | String/int dispatch can run in place | Strictly side-effect-free value needs no hold; otherwise bind `tmp` before the dispatch function, including awaited values | `polyvar_dispatch_in_place` (X:50), `hold_external_arg` (X:213) |
| X10 | Optional known `Some` needs a variant hold | Hold only its payload, reconstruct the optional wrapper preserving identity and cold metadata; other argument kinds never request a variant hold | `hold_external_arg` (X:213) |
| X11 | Object argument holding | Skip constants on labelled/empty fields; empty fields do not variant-hold. Labelled and optional fields use X8–X10. An unknown optional value additionally holds if not delay-safe and a later literal-evaluated argument is neither delay-safe nor mutually strictly pure with it | `presence_unknown` (X:173), `hold_external_obj_args` (X:278) |

X11's legacy suffix search is quadratic. Preserve its predicate with a reverse
summary of later literal-evaluated values: whether any is not delay-safe, and
whether any such value is not strictly pure. Test the first bit for an impure
current value and the second for a pure current value. Compute argument facts
on construction, not by repeated subtree walks. This is a specified algorithm
change, not a change in which values are held.

**Argument values and effects.** Optional conversion precedes the attribute
case, except constant specs never consume a runtime argument. The result of
one argument is zero, one or two values plus an optional effect; use an inline
bounded result, not a heap vector per argument.

| Row | Kind | Values and effects | Legacy |
| --- | --- | --- | --- |
| X12 | Optional label | Undefined becomes non-unit undefined; known optional block becomes payload. Duplicable unknown becomes `isNotNone(arg) ? valFromOption(arg) : undefined`; otherwise one runtime `valFromOption(arg)` call | `external_optional_to_undefined_expr` (X:181), `is_not_none_expr` (X:730), `val_from_option_expr` (X:723) |
| X13 | `Nothing` | One converted value, no extra effect | `lower_external_arg_values_and_effect` (X:782) |
| X14 | `ExternUnit` | Preserve effect if not pure; no value for an empty label, unit undefined for a labelled/optional argument | `lower_external_arg_values_and_effect` (X:782), `external_arg_effect` (X:741) |
| X15 | `Ignore` | No values; preserve effect if not pure | `lower_external_arg_values_and_effect` (X:782), `external_arg_effect` (X:741) |
| X16 | `ArgCst` | No runtime argument; int literal cast to i32, string literal, or raw JSON literal | `assemble_external_args_no_splice` (X:834); `compile_external_arg_const` (C:6120) |
| X17 | `PolyVarString` | Undefined stays undefined; literal string dispatches to its mapped string; otherwise a string-switch IIFE | `external_polyvar_string_expr` (X:344) |
| X18 | `PolyVar` (event) | Two values: tag and payload. A literal two-field polyvariant block supplies both directly; otherwise project NAME and VAL. Map the tag through string dispatch when supplied | `external_polyvar_event_exprs` (X:374), `literal_polyvar_block` (X:370) |
| X19 | `Int` | Undefined stays undefined; literal tag dispatches to mapped i32; otherwise a string-switch IIFE returning i32 values | `external_polyvar_int_expr` (X:400) |
| X20 | `Unwrap`, nonoptional | Two-field block with numeric first field yields its second field; otherwise project VAL | `external_polyvar_unwrap_expr` (X:421) |
| X21 | `Unwrap`, optional | Uses the original raw argument, not the optional-converted value: undefined, unwrap known payload, or runtime `unwrapPolyVar` | `external_option_unwrap_expr` (X:197), `lower_external_arg_values_and_effect` (X:782) |
| X22 | No splice | Walk specs once; constants insert values; missing runtime arguments become non-unit undefined; concatenate converted values, collect effects in argument order. Remove the trailing optional-undefined suffix, then prefix fused effects | `assemble_external_args_no_splice` (X:834), `keep_non_undefined_external_args` (X:872), `fuse_external_effects` (X:749), `add_external_effect` (X:755) |
| X23 | Splice/variadic | Last **runtime** argument that is an array expands its elements without attribute conversion. Otherwise convert it and mark that spread is needed. After all specs, wrap the final assembled value in spread. Constants can follow the last runtime argument. No trailing-undefined trimming | `assemble_external_args_with_splice` (X:894), `assemble_external_args` (X:959) |

X22's suffix trimming zips reversed specs with reversed **assembled values**;
keep this exact rule even where an attribute expands or removes an argument.
`external_arg_effect` uses ordinary purity, not strict purity. Effects are
folded with J-M1 and prefixed with J-M1, not inserted at their original argument
positions; the holding/sequencing phase preserves the necessary evaluations.

**Calls and access.** All calls use default call information. Scoped access
uses ordinary static members, not record-field positions.

| Row | Declaration/access | J form | Legacy |
| --- | --- | --- | --- |
| X24 | Named module value/function | With no scopes, qualify the named member; with scopes, qualify the first scope, then member-access the remaining scopes and name. First scope `default` (or unscoped name `default`) selects default import | `translate_scoped_module_value` (X:621) |
| X25 | Global value/function | Global variable is first scope, or name when unscoped; append remaining scopes and name | `translate_scoped_global_value` (X:1417) |
| X26 | Module itself | Bundle is primitive name with no hint/attributes. Zero-arity value returns binding; positive-arity value calls binding with assembled args. Constructor uses **no-splice** assembly, even for variadic declaration | `external_module_binding` (X:609), `compile_js_call` (X:1202) |
| X27 | Named/global `DeclVal` | Zero effective arity returns target if args empty, otherwise calls target with raw sequenced args. Positive arity uses X22/X23 | `compile_js_call` (X:1202) |
| X28 | Named/global `DeclNew` | `new target(assembled args)` with X22/X23 | `compile_js_call` (X:1202) |
| X29 | `DeclSend` | Consume receiver first; assemble remaining args against specs after the first. Apply scopes to receiver, then call its named member (retain receiver binding) | `compile_js_call` (X:1202), `apply_scoped_access` (X:1434) |
| X30 | `DeclGet`, `DeclSet` | No-splice assembly, exactly one/two values. Scoped receiver's member read or assignment. `DeclSet` does **not** append unit undefined, unlike X5 | `compile_js_call` (X:1202), `static_index` (X:1441) |
| X31 | `DeclGetIndex`, `DeclSetIndex` | No-splice assembly, exactly two/three values. Scoped receiver indexed by second value, optionally assigned third | `compile_js_call` (X:1202), `apply_scoped_access` (X:1434) |
| X32 | Tagged templates | Not handled by X: the separate `PtaggedTemplate` primitive retains the existing template lowering | `compile_js_call` (X:1202) is exhaustive over declaration kinds; P's template arm |

**Object fields.** In X3, empty fields consume a runtime argument unless
constant and preserve its effect only. Labelled constants insert their value;
other labelled fields require exactly one converted value (X:762). Optional
undefined fields are omitted; known `Some` payloads are converted as labelled
values directly into the literal. Unknown optional fields are queued in source
order. Fuse discarded effects before the literal. If the queue is nonempty,
bind the object with kind `Variable`; for each queued field, bind a strict
`tmp` if its value cannot be duplicated, test `value !== undefined`, and assign
the converted value. Skip `valFromOption` when `for_sure_no_nested_option` is
set. Convert that field with an empty label; prefix any field effect to its
assignment value. Result is the object variable (`compile_js_object_create`,
X:972; `lower_object_external_arg_value_and_effect`, X:762).

**External identifiers.** Identity is `(bundle, default)`, not hint, import
attributes or dynamic/static use. First encounter creates the binding and its
name; later encounters reuse it (`external_module_id`, X:581). Each reference
still carries its own import attributes and dynamic-import bit (X:79, X:581).
Reuse `import.rs`'s per-unit module inventory and naming implementation rather
than inventing a second identity scheme. Its current string scan per lookup
must be replaced by indexed bindings before repeated-call cost is claimed.
No source handle currently identifies the bundle/default pair: intern it once
and retain an indexed lookup for subsequent source-primitive uses.

An explicit hint capitalizes its first ASCII character. Without a hint, take
the final slash-separated component; an ASCII-letter start followed by ASCII
letters/digits/underscores is capitalized directly. Otherwise collect letters,
digits and underscores, starting at a letter and capitalizing the next letter
after dot/hyphen. If collection is empty, use the original bundle (capitalized
when a slash existed). Sources: `external_module_ident_name` (X:86),
`capitalize_ascii_first` (X:93), `good_hint_name` (X:106), `collect_start`
(X:115), `collect_next` (X:133), `js_id_name_of_hint_name` (X:149).

**Cross-module inline attempt (3.3).** Before lowering call arguments, recognize
a module field of a global. With cross-module inlining enabled, obtain the
exported Lambda function; require equal parameter/argument counts and
`attr_can_be_inlined`. Import its body, compute the closed parameter map,
beta-reduce with `propagate_beta_reduce_with_map`, extend assignable facts for
the reduced tree, and lower that result. Legacy
`compile_external_field_apply` (C:1377) returns a value output which callers
convert to their continuation: do not silently substitute a different
return-specific lowering. Restore temporary assignable state afterwards.
No eligible export means the existing arity-aware call, not an unsupported
result. An eligible body containing an unsupported construct returns that
construct's reason. This function is in C, not X; X's similarly named
`external_module_id` (X:581) handles JavaScript imports, not `.cmj` inlining.

**Cost obligations.** One source visit per argument, one linear spec assembly,
one reverse summary for X11 and one generic sequencing pass. Count holds and
argument steps at 10,000 call arguments and 10,000 labelled object fields.
String dispatch construction additionally costs its case count and spelling
bytes; scoped access costs its segments and spelling bytes. Unknown optional
fields use one pending list per object, not one allocation per field. This
specification is not a claim that these costs have already been measured.

**S3.8 implementation evidence.** The event duplicability predicate is a dense
boolean node table maintained by arena construction/repair; the holder reads
it in O(1). Object suffix facts are two booleans per argument. Module binding
identity uses a dense table indexed by the interned bundle and default bit;
repeated call primitives reuse a `PrimId`-indexed reference. Import attributes
remain on the reference, not the binding. Persistent global names also reuse
one variable identity: distinct identities for repeated `console.log` calls
prevented the conditional normalizer from recognizing equal branches.

The cross-module attempt uses the existing BIR `closed_with_stats` and `reduce`
implementations of the closure-statistics/beta rules rather than exporting back
to the legacy Lambda compiler. Imported binders and their assignment facts are
fresh; they cannot modify enclosing assignment facts. Its reduced body is
scheduled in V, followed by conversion to the original continuation.

The corpus gate exposed `PisPolyVarBlock("a")` bypassing J-M9/J-E4, producing
`typeof "a" === "object"` instead of `false`. P:642 calls E:832/E:653, which
normalizes `typeof` first; the BIR primitive now calls those existing J rules.
No new J rule was needed. These global-identity and primitive corrections do
not change the X tables above.

Measured 10,000-element lowering tests (constant operands):

| Shape | Source visits | Primitive steps | Sequencing steps | Holds |
| --- | ---: | ---: | ---: | ---: |
| External call | 10,001 | 30,001 | 10,000 | 0 |
| Labelled object | 10,001 | 40,001 | 10,000 | 0 |

Separate 10,000-element holder tests exercise 10,000 event holds in 10,000
argument steps and 5,000 optional-object holds in 20,000 argument steps.
These counts describe the opt-in backend, not a default-path speedup.

### 3.6 `If`

`If(c, t, e)`. Always first: `V(c)`. Its statements come first in the output
and its value is the test.

What the legacy code does today, per continuation. "Free" is "lowered as a
value, it has no statements".

| Row | Continuation | Legacy passes over `t` and `e` | Result |
| --- | --- | --- | --- |
| R1 | **V** (C:1812) | `V(t)`, `V(e)`. If not both free: a fresh `tmp`, then `A(tmp)(t)`, `A(tmp)(e)` | both free: value `cond(c, t, e)` (J-E7). Else: `let tmp` (kind `Strict`), `if_(c, T, E)` (J-S3), value `tmp` |
| R2 | **D** (`compile_if_binding_block` (C:2699)) | `V(t)`, `V(e)`. If not both free: `A(id)(t)`, `A(id)(e)` | both free: `let id = cond(c, t, e)`. Else `compile_declared_if_block` (C:4926): after the swap of row R3, if each branch is the single statement `id = x`: `let id = cond(c, x_t, x_e)`; else `let id;` and `if_(c, T, E)` |
| R3 | **A** (`compile_if_assignment_block` (C:4873)) | `A(id)(t)`, `A(id)(e)`, once | `compile_test_assignment_block` (C:4895): if `c` is `!c'` and `E` is not empty, the branches are swapped and `c'` is the test (`normalize_if_assignment_merge_order` (C:6595)); if each branch is the single statement `id = x`: `id = cond(c, x_t, x_e)`; else `if_(c, T, E)` |
| R4 | **E** (`compile_if_effect_block` (C:4761)) | `V(t)`, `V(e)`. Then, depending on the result, `E(e)`, or `E(t)`, or both | below |
| R5 | **R** (`compile_if_return_output` (C:5144)) | `R(t)`, `R(e)`; then, unless the fold of the first stage applies, `V(t)`, `V(e)` | below |
| R6 | **R** in a tail loop (`compile_tail_loop_if_return_output` (C:4086)) | if neither branch contains a self tail call: `V(t)`, `V(e)`. Then `R(t)`, `R(e)` | below |

Row R4, in order (`remove_pure_subexpression` (E:96) is J-M0):

1. both free: let `t'`, `e'` be the values with their pure parts removed.
   Neither left: the test alone, kept only if it has effects
   (`push_s_if_empty` (O:359)). Both left: the expression `cond(c, t', e')` for
   its effect. Only `t'`: `if_(c, [t'], [])`. Only `e'`: `if_(!c, [e'], [])`;
2. `t` free and without effects: `if_(!c, E(e), [])`;
3. `e` free and without effects: `if_(c, E(t), [])`;
4. otherwise `T = E(t)`, `E = E(e)`: if `E` is exactly one `return`,
   `if_(!c, E, [])` followed by `T`; else if `T` ends in `return`, `throw`,
   `break` or `continue`, `if_(c, T, [])` followed by `E`; else
   `if_(c, T, E)`.

Row R5, in order:

0. in a function that returns unit, if both branches are trivially the unit
   value (`lambda_is_trivial_unit_undefined` (C:3550)): the test alone, kept only if
   it has effects; finished (`compile_if_unit_return_tail_block` (C:3579));
1. if neither branch contains a form that needs statements
   (`lambda_contains_statement_value_form` (C:5016)) and both `R(t)` and `R(e)` are
   expression statements followed by one `return`
   (`try_fold_effect_only_return_tail` (C:5118)): `return cond(c, seq_t, seq_e)`,
   finished, where `seq` joins the statements and the returned value with
   `js_seq` (J-M1);
2. else if both are free: `return cond(c, t, e)`, finished;
3. else `compile_test_return_block_with_fallback` (C:5231) on `R(t)`, `R(e)`: both
   exactly one `return`: `if_` (which folds them, J-S3 rule 4); `R(e)` exactly
   one `return`: **one block statement** holding `if (!c) R(e)` followed by
   `R(t)`; else `if_(c, R(t), R(e))`. Not finished.

Row R6: both free (when tried): `return cond(c, t, e)`, finished. Else
`T = R(t)`, `E = R(e)`: if the test is a conjunction, `T` ends in `continue`
and `E` ends in `return`, `throw` or `break`: a plain `if (!c) E'` followed by
`T`, where `E'` is `E` with a leading guard merged
(`merge_terminal_guard_fallthrough_else` (C:6750)); else `if_(c, T, E)`.

**The new lowering.** OCaml has one rule for rows R5 and R6
(`lam_compile.ml:1636-1712`): the branches are lowered in **VR**; both free
gives `return cond(c, t, e)`; otherwise the branches lowered in **R** are
given to `S.if_`. In **VR** a short circuit is a conditional
(`lam_compile.ml:1258-1259`), which is what stage 1 of row R5 reconstructs
from statements, and a self tail call is the loop jump, which is what the
test in row R6 approximates. The new lowering therefore implements:

| Continuation | `probe` target for `t`, `e` | Both free | Otherwise |
| --- | --- | --- | --- |
| **V**, **VR** | `A(tmp)`, `tmp` allocated before the branches (3.8) | `Free::Cond` | fill the reserved slot with `let tmp`; `if_(c, T, E)`; value `tmp` |
| **D** | `A(id)` | `Free::Cond`, realized as `let id = cond(...)` | row R2 |
| **A** | `A(id)` | `Free::Cond`; realized by row R3 on the two branches realized in **A** | row R3 |
| **E** | `E` | row R4 step 1 on the two `Free`s | row R4 steps 2 to 4, where a `Free` branch that is needed as statements is realized in **E** |
| **R** | `R` | `return cond(c, t, e)`, finished | `S.if_` on the two outputs, with the block wrapper of row R5 step 3 |

Rows R5 step 0, R5 step 3's wrapper and R6's guard merge are legacy forms
that OCaml reaches through `S.if_` and block wrappers. They are ported as
written and are the first place to look when `Check` reports a difference in
a conditional. Resolved Q3: the rows differ on `(if c unit unit)` when the
function returns unit. R5 step 0 emits nothing for a pure `c`; R6 emits
`return;`. Inside `while (true)` the return is essential: falling through
would repeat the loop. The context difference is meaningful, not evidence
that one row must disagree with OCaml. Keep both rows (see section 10).

S3.6 also found a separate legacy discrepancy: R6's value probe changed a
short circuit under a conditional to `&&`/`||`, unlike OCaml's
`NeedValue should_return`. The legacy path now folds return blocks for
expression-only branches, preserving conditional returns, and reuses the
blocks when folding fails. `tests/tests/src/lowering_tail_short_circuit.res`
is the reference-compiler fixture. R6 retains the block produced by `S.if_`
when it follows statements of the test; the explicit conjunction/continue
guard remains unwrapped.

`realize(Free::Cond { test, then_, else_ }, k)`:

| k | Result |
| --- | --- |
| **V**, **VR** | `cond(test, realize(then_, V), realize(else_, V))` |
| **D** | `let id = ` the **V** result |
| **A** | row R3 on `realize(then_, A)` and `realize(else_, A)`. The legacy row lowers the branches for `A(id)` only, so a free `Seq` branch is `f(); id = 1`, two statements, and the conditional stays a statement; a leaf branch is `id = x` and both merge to `id = cond(...)` |
| **E** | row R4 step 1 |
| **R** | `return ` the **V** result, finished |

`realize(Free::Seq { first, second }, k)`: in **V**, `js_seq(first,
realize(second, V))`, or the second part alone when `first` has no effect;
in the other continuations `first` as a statement
(`push_effect_expression` (O:339)) followed by `realize(second, k)`.
`realize(Free::Leaf(v), k)`: conv.

Incidental, all three stay in the lowering:

- which branch is negated or swapped depends on the order in which the rules
  of `if_` and of rows R2 to R4 are tried; the rule lists are normative;
- row R5 step 3 constructs one block, but `compile_return_output`
  (`compiler-rust/src/lambda/lam_compile.rs:3179`) then calls `unnest_block`
  on the whole output. When the test has no statements the block is the only
  statement and is removed; after statements of the test it stays one of
  several statements. The distinction shows in the text printed before the
  passes. The new lowering never builds the block in the first case: the
  guard is in the head slot and the kept branch follows it in place;
- the result temporary is `Strict` in **V** and the declaration precedes the
  `if` but follows the statements of the test.

How the rows are carried out (`bir/lower/cond.rs`):

- the output is `[statements of the test][declaration slot][head slot]
  [then run][else run]`. The declaration slot exists in **V** and **D**
  only. A free branch has no run until a rule needs it as statements; it is
  then realized at the top of the stack, above the other branch, which is why
  no rule depends on the order of the two runs;
- `if_(c, T, E)` as one statement is `raw if` when no rule of J-S3 applies to
  the operands (a constant number of reads of the test and of the first and
  last statement of each run), and `norm::js3_simplify_if` otherwise;
- in **R**, `if_` is applied in place (rules 0 to 6 of J-S3 on runs): rule 5
  and rule 6 leave the kept branch where it is. The result is wrapped in one
  block only after statements of the test;
- row R5 step 0 is decided when the conditional is entered, from the `PURE`
  flags along the `Let`/`Seq` spine of each branch, and then only the test is
  lowered. Nothing is lowered and discarded;
- row R5 step 1 reads the statements the branches produced in **R**. Its
  legacy gate, `lambda_contains_statement_value_form` (C:5139), is the L flag
  `HAS_STATEMENT` of the two branches (7.1), read when the conditional is
  entered. S3.5 added it: the gate decides for a branch that is a string
  switch of one complete case, or a static catch in the cheap form, whose
  statements are effects followed by one return;
- in **E** a branch that needs statements has the effect of its value pushed
  when the branch is complete (`compiled_to_effect_block` (C:4875)); the
  output of the row is then read by `compiled_from_effect_block` (C:7612): a
  lone expression statement becomes the value.

Every rule above has a test against the legacy lowering in the five
continuations. Two inputs are not reachable from L yet and are tested on
hand-built J statements against J-S3 instead: a test that is a boolean
literal (rule 0 of J-S3) and a branch ending in `break` or `continue` (row
R4 step 4, rule 6 of J-S3). The same differential test runs every rule of
J-S3 on runs, in place and as one statement, for each pair of sixteen branch
shapes and five tests. The merge of rows R2 and R3 on two single assignments
is reached only through `realize`: a branch that is one assignment is a free
branch.

### 3.7 The short circuits: `Prim(Psequand)`, `Prim(Psequor)`

`l && r`, `l || r`. `default` is `false` for `&&`, `true` for `||`; `test` is
`l` for `&&`, `!l` for `||`.

| Continuation | Order | Result | Legacy |
| --- | --- | --- | --- |
| **V** | `V(l)`, `V(r)`, then `tmp` if needed | `r` free: `bin(op, l, r)` (J-E5, J-E6). Else: `let tmp = default` (kind `Strict`), `if_(test, [r's statements; tmp = r], [])`, value `tmp` | `compile_short_circuit_expr` (C:2794), `compile_short_circuit_js` (C:2806) |
| **D** | `V(l)`, `V(r)` | `r` free: `let id = bin(op, l, r)`. Else: `let id = default` with kind **`Variable`** whatever `kind` is, then the same `if_` | `compile_short_circuit_binding_block` (C:2859) |
| **A** | `V(l)`, `V(r)` | `r` free: `id = bin(op, l, r)`. Else: `if_(test, [r's statements; id = r], [id = default])` | C:5415-5444 |
| **E** | as **V**, then the value for its effect | | default arm of `compile_effect_block_inner` (C:2593) |
| **R**, **VR** | as `If(l, r, false)` or `If(l, true, r)` in the same continuation | | `compile_short_circuit_return_output` (C:3075), `compile_short_circuit_tail_loop_return_output` (C:4155) |

`r` is lowered once in every row, as a value in **V**, **D**, **A** and **E**
and for **R** in **R**; whether it is free selects the form. A short circuit
uses the traversal frame of a conditional, so nested short circuits do not
nest calls of the lowering. In **R** the rewritten conditional is not built
as an L node (the legacy code builds the constant with `default_lambda`,
C:286); the `If` rule is called with a constant free branch.

### 3.8 Identifiers the lowering creates

| Name | Created by | When, relative to the sub-terms |
| --- | --- | --- |
| `tmp` (result) | `If`, `Switch`, `StrSwitch`, `Catch`, `Try`, `TryFinally`, a short circuit, in **V** | legacy: `If` and short circuits after the first lowering of the branches; `Switch` **before** the scrutinee (V:642); `Catch` before the body (C:6408, C:1757); `Try` before the body (C:1781) |
| `tmp` (held argument) | sequencing (3.3) | after all arguments, right to left |
| `tmp` (scrutinee) | a named-variant or untagged switch whose scrutinee is not a variable (`bind_switch_scrutinee_once` (V:944)) | after the scrutinee, before the cases |
| `tmp` (receiver) | `compile_js_object_get` (P:84) | after the receiver |
| `exit` | a static catch in the explicit form | before the body (4.1) |
| `_x` | a self tail call that changes parameter `x` (5.1) | at the first call that changes `x`, in parameter order within the call |
| `param` | a partial cross-module application (3.3) | after the arguments, left to right |
| `_for_of`, `_for_await_of` | a `for ... of` whose variable is unused (3.11) | after the iterable, before the body |
| external module names | the first use of an external module in the unit (S3.8) | at that use |
| rebound exports | export coercion (8.2) | after the unit |

Naming reads the creation order of two identifiers only when both have the
same base name and are free in one function when it is entered (E.3 step 5).
Every identifier above except a module name is local to the function it is
created in and is not captured by an inner function (the `_x` copies are
never read by a closure: the closure reads `x`, section 5.1). So the relative
order of these identifiers is not expected to reach the output. The lowering
still creates them in the order of the legacy pass whose output is kept
(C.2 row 11): with `probe`, the result `tmp` of an `If` is allocated before
the branches are lowered and dropped if the conditional is free, so that it
precedes the identifiers of the branches as it does today. Identifiers of
discarded legacy passes have no counterpart.

Incidental: the numbers that discarded passes consume. Not reproduced. A
variable's `order` (B.4) is a creation sequence number and gaps are harmless.

### 3.9 `Switch` and `StrSwitch`

**Continuations** (`lam_compile.ml:936-952`): **V**: a fresh `tmp`, `let tmp`
(kind `Strict` in the legacy code), the switch in `A(tmp)`, value `tmp`.
**D**: `let id;` with the binding's kind, the switch in `A(id)`
(`compile_switch_binding_block` (C:2750)); for a string switch the last statement
`id = x` is folded into the declaration when it is last
(`prepend_declaration_or_fold_final_assignment` (C:5070)). **A**, **E**, **R**:
the switch in that continuation. A switch never probes.

**Order.** Integer, string and named dispatch lower the scrutinee in **V**,
then each grouped body once, then the default. Integer/named/untagged **V**
allocate the result temporary before the scrutinee; string **V** allocates it
afterward. Untagged emission follows the existing planner: actual switches
lower the default before their clauses, while a single-typeof conditional
lowers its clause before the default. A reused action is lowered once per
in-switch state and its J output is copied for additional emitted occurrences.

Direct integer and string wrappers enter switch context for the scrutinee and
bodies, including small string forms. Named dispatch enters it only for the
bodies of a general side switch; untagged dispatch only for actual switches
in its plan. The explicit traversal carries these contexts without recursion.

**Forms.** The header selects the representation. Small string/named forms
also depend on completeness: direct string **E** treats cases as incomplete,
even without a default, unlike its other continuations:

| Form | When | Function |
| --- | --- | --- |
| untagged dispatch | the header has a plan (`untagged_plan` (C:7873); the plan is computed by `untagged_dispatch.rs`, which the new lowering calls unchanged) | `compile_untagged_switch` (V:571), `emit_untagged_tree` (V:336), `emit_untagged_clause` (V:400): `typeof`, `Array.isArray`, `instanceof` tests, then switches on values. The switch context is entered only for the bodies of its `switch` statements |
| named variant | constructor keys (`uses_named_variant_switch` (V:860)) | the scrutinee is bound to a `tmp` unless it is a variable when both constants and blocks are tested (`named_variant_switch_needs_bound_scrutinee` (V:966)); `if (typeof x !== "object")` separates constants from blocks (`is_int_tag` (V:244)); then one string or literal switch per side (`dispatch_named_variant_branches` (V:987)); the block side switches on the tag read (`variant_tag_expr` (V:1010)) |
| integer | integer keys | below |
| string | `StrSwitch` | below |

The general case of the last two (`compile_general_cases`,
`lam_compile.ml:693-836`):

1. cases whose body equals the default's are dropped
   (`filtered_switch_case_refs` (C:461));
2. cases are grouped: walking from the last case to the first, a case joins
   the first group whose head has an equal body, else starts a group; groups
   keep the order of their last member (`stable_group_switch_cases` (V:180)). All
   members of a group but the last get an empty clause that falls through;
3. direct integer dispatch always retains `switch` syntax, including zero,
   one and two cases. String/named dispatch selects small forms **before**
   filtering/grouping: zero cases is the default's block; one complete case
   without a default is its body; one incomplete case or two complete cases
   use `if_(scrutinee === key, case, other)`. Other forms use a switch;
4. `break`: in **E** and **A** a clause breaks unless its output is finished
   (`to_break_block`, `js_output.ml:88-100`; `compile_switch_value_block` (C:5306)).
   In **R** a clause breaks only if its body contains an exit **and** its
   output is not finished (`return_case_needs_break` (C:6643));
5. in **E**, a direct integer/string switch whose clauses and default are
   all empty is the scrutinee alone (C:5866-5875). Named general switches retain
   their switch even when empty. The legacy-output oracle wins these form
   distinctions over the earlier generalization of this section.

"Equal" in steps 1 and 2 is `eq_approx` (`lambda/arena.rs`), structural
equality on ten node kinds that is false for the others. Section 7 bounds its
cost.

The small string forms of step 3 are separate legacy functions per
continuation (`compile_small_string_switch_assignment` (V:1046),
`compile_small_string_switch_return` (V:1088),
`compile_small_string_switch_effect` (V:1161),
`compile_small_string_switch_tail_loop_return` (V:1445)), and so are the named
string switches (`compile_named_string_switch_assignment` (V:1248),
`compile_named_string_switch_return_with_strategy` (V:1274),
`compile_named_string_switch_effect_with_strategy` (V:1584)). In the new lowering
each is one function taking `Cx`.

Incidental, stays in the lowering: labels use `switch_depth > 0`. Direct
integer/string wrappers include small forms, but named and untagged dispatch
only enter the scopes described above. Loop/exit lowering remains the later
slices' responsibility; this slice tests the dispatcher and nested unsupported
reasons rather than claiming support for those bodies.

Incidental, legacy only: `compile_hoisted_named_string_return_tail` (C:3918) and
`should_hoist_grouped_named_string_return_tail` (C:3905) act only when a
substituted handler is active (row K15, Q1).

### 3.10 `Catch` and `Exit`

Section 4.

### 3.11 Loops, `Break`, `Continue`, `Assign`

All produce statements and the unit value. In **V** the value is `undefined`;
in **E** nothing more; in **D**, **A**, **R** conv of `undefined` (the default
arms).

| Op | Order | J nodes | Notes |
| --- | --- | --- | --- |
| `While(c, body)` | `V(c)` with `switch_depth + 1`; push a loop frame; `E(body)`; pop | `SWhile(label, c, body)`. If `c` has statements: `while (true) { c's statements; if (!c) break; body }` | the condition's statements run inside the loop, hence the switch depth (C:1869-1910) |
| `For(v, start, end, dir, body)` | the end is lowered **before** the start; frame; `E(body)` | `SForRange`. An upward loop to `e - 1` becomes `< e` (`lower_ocaml_for_range_direction` (C:6717)). If the end has statements and the start is not `delay_safe`, `v` is declared with the start before the end's statements | `compile_for_loop` (C:2074); reads `ASSIGNED` |
| `ForOf`, `ForAwaitOf(v, iter, body)` | `V(iter)`; frame; `E(body)` | `SForOf`, `SForAwaitOf`. If `v` is unused in the body, a fresh `_for_of` or `_for_await_of` replaces it | `compile_for_of` (C:2154) walks the body for free variables; the new lowering reads `uses[v] == 0` |
| `Break`, `Continue` | | `SBreak`, `SContinue`, labelled with the innermost frame's label when `switch_depth > 0`; **finished** | arms of `compile_expr` (C:1529); 4.5 for the label |
| `Assign(v, x)` | `V(x)` | `SExp(v = x)` | arm of `compile_expr` (C:1529) |

A loop frame is pushed for the body only, preserving the enclosing switch
depth (`compiler/core/lam_compile_context.ml:88`). Thus a loop inside a
switch may label even a direct body jump; resetting depth at loop entry would
change reference output. A function body starts with no frames and
`switch_depth = 0` (row K10). The dense one-byte loop fact records both a
body switch-crossing jump and a direct body jump. Entry reads that byte once
with the inherited context; no body scan decides whether a label is needed.

### 3.12 `Try`, `TryFinally`, `LetRec`; source locations

`Try` and `TryFinally` are 5.5; `LetRec` is 5.3.

Source locations (only with source maps on; `source_map_enabled`):

- an expression gets the location of its `Apply`, of its `Fun`, or of its
  `Prim` when the primitive is lowered by the default path
  (`primitive_uses_default_compilation` (C:7846)), if the location maps to source
  (`mappable_loc` (C:905)) and the expression has none yet;
- the first statement of a switch clause gets the location found by
  descending from the case body to the first located node
  (`source_loc_of_lam` (C:915), `with_block_source_loc` (C:2578)); an empty
  fall-through clause carries it on the clause;
- `throw` and `debugger` get the primitive's location.

The descent of `source_loc_of_lam` follows first children and is bounded by
the depth of the case body. Smart constructors drop or keep locations as the
legacy ones do (for example J-E8 keeps the comment and drops the location of
a negated literal); the J rules of section 6 are ported with their location
handling, and the gate with source maps on (8.1) is the judge.

S3.7b validation and measurements: [LOWERING_LOOPS_RECURSIVE_RESULTS.md](LOWERING_LOOPS_RECURSIVE_RESULTS.md).

## 4. Exits: `Catch` and `Exit`, and loop labels

### 4.1 Design

The jump table holds one entry `{exit: VarId, order: i32}` per catch header,
indexed by the header (`CatchId`); the bindings are the header's parameters.
A label is bound by one catch (4.2 invariant 1), so an entry is written when
its catch is entered and read only by the exits of that catch's body: no
stack is pushed or popped. `Cx::jumps` is the number of entries visible to a
node, which is all the table needs for `first` below. An `Exit` names its
handler by label, and labels are sparse (they are `i32` in Lambda, and one
unit of `tests/tests` has the label -1), so it finds the header through the
arena's label index, one hash lookup per exit. A function body starts with
no visible entry (row K10). This is OCaml's `jmp_table`
(`lam_compile_context.ml:67`).

`lower_catch(cx, node)` (`compile_staticcatch`, `lam_compile.ml:1169-1255`):

1. **Flatten** (`flatten_nested_caches` (C:190)). Starting at `node`, collect its
   handler, then walk into the body while it is a `Catch` whose handler
   contains no `Exit` to a label already collected (issue 1698). The table is
   ordered **innermost first**. "Contains no exit" is the node flag `HAS_EXIT`
   (section 7): when it is clear the answer is immediate; when it is set the
   handler is walked for the labels, pruned by the flag. A collected catch is
   marked in its table entry, so the test of a label is one read.
2. **Cheap form.** If `cx.cont` is `Effect(Return(Named { in_catch: false,
   .. }))`, the table has one handler, and the handler has no `HAS_EXIT`:
   - push `{label, bindings, order: -1}`;
   - reserve the declarations `let b;` (kind `Variable`) of the bindings;
   - lower the body in `Effect(Return(Named { in_catch: true, .. }))` with
     the entry visible;
   - pop; lower the handler **in `cx`**, after the body;
   - the output is `append(declarations, append(body, handler))`.
3. **Explicit form**, otherwise:
   - in **V** create the result `tmp` first (C:6408), then create `exit` (a
     fresh identifier named `exit`), before anything is lowered;
   - `first = height of the visible jump stack + 1`
     (`next_static_jump_exit_code` (C:6334); `add_jmps`,
     `lam_compile_context.ml:114-123`). The i-th handler of the table gets
     `order = first + i`. Push all entries;
   - declarations, in this order: in **V** `let tmp;` for a fresh `tmp`
     (kind `Strict`, C:6408), in **D** `let id;` with the binding's kind; then
     `let exit = 0;` (kind `Variable`); then `let b;` (kind `Variable`) for
     the bindings of every handler in table order;
   - the body's continuation `k'`: **V** gives `A(tmp)`, **D** gives `A(id)`,
     **A** stays, `Effect(t)` gives `Effect(t')` where `t'` sets `in_catch`
     when `t` is `Return(Named ..)`;
   - lower the body in `k'`; then every handler in `k'`, in table order, with
     the entries still visible; pop;
   - the dispatch (`compile_exit_dispatch` (C:6528)): handlers with equal bodies
     are grouped as switch cases are (3.9 step 2,
     `compile_grouped_staticcatch_handlers` (C:6493)), with the fingerprints
     of the switch lowering, and only the last of a group is lowered. One
     handler: `S.if_(exit === order, handler, [])`, and nothing if the
     handler's block is empty. Several: `switch (exit) { case order: ... }`
     with no default; a clause breaks when it is the last of its group, its
     output is not finished and either the continuation is not a return or
     the handler contains an exit (C:6552). The break is clause metadata in
     every continuation, also in **A**, where a switch on a value emits a
     `break` statement instead (3.9 step 4);
   - the output is `append(declarations, append(body, dispatch))`: a finished
     body drops the dispatch, and the output is finished only then. In **V**
     its value is `tmp` and it is never finished (C:6408); in **E** its value
     is `undefined`.

`lower_exit(cx, label, args)` (`compile_staticraise`,
`lam_compile.ml:1122-1139`). Find the entry. The arguments are lowered
**last first**, each in `A(binding)`; an argument that is a variable is the
plain assignment `b = v`; with `order = -1` an argument that is the binding
itself is skipped (C:3506). The output is the argument outputs in source
order followed by `exit = order` when `order >= 0`, joined with `append`, so
a finished argument (one that throws) drops what follows it. With more than
one argument each argument's run is moved to a slot reserved for it, so that
lowering last first still writes source order. The output is **not**
finished unless an argument is: control falls through to the end of the
enclosing statements and reaches the dispatch or the handler.

The continuation is ignored by OCaml. The legacy families read a value where
they need one, and the lowering gives the same: `undefined` in **V** and
**E**, and `let id = undefined` in **D** (the default arms of `compile_expr`
and `compile_let_binding_output`); nothing in **A** and **R**. In an effect
or return continuation an output that is one block (one argument, a
conditional that needs statements) is unnested, as `compile_return_output`
and `compile_effect_block_output` do for every construct.

A catch whose body holds no exit to its label is lowered by the same rule;
the legacy code substitutes its handler at the (absent) raise instead (row
K15). The two differ when the body's output is not finished, and the shape
does not reach the lowering (Q1).

That is the whole mechanism. The legacy code reaches the same outputs with
four copies of the explicit form (one per continuation family:
`compile_staticcatch_effect_output` (C:3378),
`compile_staticcatch_assignment_output` (C:3408),
`compile_staticcatch_return_output` (C:3348),
`compile_staticcatch_tail_loop_return_output` (C:3317)), four of the flattened
form, two of the cheap form, and the choice in
`compile_staticcatch_in_return` (C:3091) (also inline in
`compile_tail_loop_return_output_inner` (C:4174), C:4240-4312). Since S3.5
the choice there is OCaml's test as well (`staticcatch_takes_pseudo_jump`,
4.6); step 2 above is the same test on the `in_catch` bit and one flag.

### 4.2 Invariants

1. A label is bound by exactly one `Catch` of a unit (the bridge rejects a
   reused label, "reused static catch label"), and every `Exit` lies in the
   body of the `Catch` that binds its label, in the same function (the bridge
   rejects "unbound static exit label").
2. `order > 0` for every explicit entry; `0` is the initial value of `exit`
   and means "no exit taken".
3. Orders are unique among the entries visible at one point: a new table
   starts at height + 1.
4. All entries of one flattened table share one `exit` variable.
5. An exit's output is never finished; a `break` in a switch clause that
   contains an exit is kept in a return continuation for that reason (3.9
   step 4).
6. The cheap form is used only in tail position of a function, with
   `in_catch` clear. Then the handler is the last thing the function does on
   every path that exits, so "fall through to the handler" is correct: every
   other path of the body returns, throws or jumps.
7. `in_catch` is set for the body of every catch in a return continuation,
   cheap or explicit, and for the dispatched handlers of the explicit form
   (they are lowered in `k'`). It is clear for the handler of the cheap form
   (lowered in `cx`) and for a function body. It is never cleared otherwise.
8. `Ret::InTry` has no `in_catch` bit and never takes the cheap form: a catch
   in the body of a `try` in tail position is explicit.

### 4.3 Worked example: three handlers in one dispatch, return position

Source:

```rescript
type t = A | B(int) | C(int, int) | D
@val external log: int => unit = "console.log"
@val external big: (int, int, int) => int = "big"

let f = (x: t, y: t) =>
  switch (x, y) {
  | (B(n), A) | (C(n, _), D) =>
    log(n)
    big(n, n + 1, n + 2)
  | (A, B(m)) | (D, C(_, m)) =>
    log(m)
    big(m, m * 2, m * 3)
  | (A, _) => 0
  | _ => big(1, 2, 3) + big(4, 5, 6) + big(7, 8, 9)
  }
```

Lambda (tested, `-drawlambda`, before the passes; abridged):

```
(function x y
  (let (match1 = x  match2 = y)
    (catch
      (catch
        (catch
          (switch* match1
           case "A": (catch (switch match2
                               case "B": (let (m =a (field 0 match2)) (exit 2 m))
                               default: (exit 4))
                       with (4) 0)
           case "D": (switch match2
                       case "C": (let (m =a (field 1 match2)) (exit 2 m))
                       default: (exit 3))
           case "B": (switch match2
                       case "A": (let (n =a (field 0 match1)) (exit 1 n))
                       default: (exit 3))
           case "C": (switch match2
                       case "D": (let (n =a (field 0 match1)) (exit 1 n))
                       default: (exit 3)))
         with (3) (+ (+ (big 1 2 3) (big 4 5 6)) (big 7 8 9)))
       with (1 n) (seq (log n) (big n (+ n 1) (+ n 2))))
     with (2 m) (seq (log m) (big m (* m 2) (* m 3))))))
```

The passes substitute handler 4 (a constant) at its exit and remove the
aliases. Labels 3, 1 and 2 remain: 3 is raised three times and is not small,
1 and 2 have parameters.

Lowering. The function body is in **R** with `in_catch` clear and an empty
jump stack. The outer `Catch` flattens: handler 2, then handler 1 (it has no
exit), then handler 3 (no exit). The table, innermost first, is
`[3, 1, 2]`; three handlers, so the explicit form; `first = 1`:

| Label | Order | Bindings |
| ---: | ---: | --- |
| 3 | 1 | |
| 1 | 2 | `n` |
| 2 | 3 | `m` |

J nodes (statement list of the function; `x`, `y` are the parameters after
alias removal):

```
SDecl(exit, 0)                                    -- Variable
SDecl(n)  SDecl(m)                                -- table order
SIf(typeof x !== "object")
  [ SIf(x === "A")
      [ SIf(typeof y !== "object") [SReturn(0)] []
        SIf(y.TAG !== "B") [SReturn(0)] []
        SExp(m = y._0)  SExp(exit = 3) ]
      [ SIf(typeof y !== "object" || y.TAG !== "C")
          [ SExp(exit = 1) ]
          [ SExp(m = y._1)  SExp(exit = 3) ] ] ]
  [ SIf(x.TAG === "B")
      [ SIf(typeof y !== "object" && y === "A")
          [ SExp(n = x._0)  SExp(exit = 2) ] [ SExp(exit = 1) ] ]
      [ SIf(typeof y !== "object" && y === "D")
          [ SExp(n = x._0)  SExp(exit = 2) ] [ SExp(exit = 1) ] ] ]
SSwitch(exit)
  case 1: [ SReturn((big(1,2,3) + big(4,5,6) | 0) + big(7,8,9) | 0) ]
  case 2: [ SExp(log(n))  SReturn(big(n, n + 1 | 0, n + 2 | 0)) ]
  case 3: [ SExp(log(m))  SReturn(big(m, m << 1, m * 3 | 0)) ]
```

Points to check against the rules: `(exit 2 m)` with `m` bound by
`let m =a field` lowers the `Let` first (`m = y._0` is the assignment of the
argument to the binding, after alias removal the argument is the field read),
then `exit = 3`; the clauses do not break (return continuation, finished
outputs); `return 0` appears twice because the handler of label 4 was
substituted at level L, and the two-case inner switch became two `if`s whose
`then` branches end in `return` (J-S3 rule 6).

JavaScript (tested):

```js
function f(x, y) {
  let exit = 0;
  let n;
  let m;
  if (typeof x !== "object") {
    if (x === "A") {
      if (typeof y !== "object") {
        return 0;
      }
      if (y.TAG !== "B") {
        return 0;
      }
      m = y._0;
      exit = 3;
    } else if (typeof y !== "object" || y.TAG !== "C") {
      exit = 1;
    } else {
      m = y._1;
      exit = 3;
    }
  } else if (x.TAG === "B") {
    if (typeof y !== "object" && y === "A") {
      n = x._0;
      exit = 2;
    } else {
      exit = 1;
    }
  } else if (typeof y !== "object" && y === "D") {
    n = x._0;
    exit = 2;
  } else {
    exit = 1;
  }
  switch (exit) {
    case 1 :
      return (big(1, 2, 3) + big(4, 5, 6) | 0) + big(7, 8, 9) | 0;
    case 2 :
      console.log(n);
      return big(n, n + 1 | 0, n + 2 | 0);
    case 3 :
      console.log(m);
      return big(m, (m << 1), m * 3 | 0);
  }
}
```

### 4.4 Worked example: an exit from a nested switch, inside a loop, with `break`

Source:

```rescript
type t = A | B(int) | C(int, int) | D
@val external log: int => unit = "console.log"

let f = (xs: array<t>, k: int) => {
  let total = ref(0)
  for i in 0 to Array.length(xs) - 1 {
    switch (Array.getUnsafe(xs, i), k) {
    | (B(n), 1) | (C(n, _), 2) =>
      total := total.contents + n
      log(n)
    | (D, _) => break
    | (A, _) => log(0)
    | _ => log(k)
    }
  }
  total.contents
}
```

Lambda (tested, `-drawlambda`, abridged):

```
(function xs k
  (let (total = (makemutable 0))
    (seq
      (for i 0 to (- (array.length xs) 1)
        (let (match = xs[i]  match1 = match  match2 = k)
          (catch
            (catch
              (switch* match1
               case "A": (seq (log 0) unit)
               case "D": break
               case "B": (if (!= match2 1) (exit 2)
                           (let (n =a (field 0 match1)) (exit 1 n)))
               case "C": (if (!= match2 2) (exit 2)
                           (let (n =a (field 0 match1)) (exit 1 n))))
             with (2) (seq (log k) unit))
           with (1 n) (seq (setfield 0 total (+ (field 0 total) n)) (log n) unit))))
      (field 0 total))))
```

The passes substitute handler 2 (small, no parameters) at its two exits, make
`total` a mutable variable and remove the aliases. One catch remains, label 1
with the parameter `n`.

Lowering. The `for` body is in **E** with one loop frame and
`switch_depth = 0`. The catch is not in a return continuation, so the
explicit form: `exit` is created, `order = 1`. The body is the switch, in
**E**, with `switch_depth = 1`. Its case `"D"` is `Break` with
`switch_depth > 0`: the frame's label is requested (`loop_0`, 4.5) and the
break is labelled, although the switch is printed as `if` statements
(3.9, incidental). The dispatch has one handler: `if (exit === 1) {...}`.

J nodes of the loop:

```
SForRange(i, 0, JLength(xs), Up, label loop_0)
  SDecl(match, JIndex(xs, i))
  SDecl(exit, 0)
  SDecl(n)
  SIf(typeof match !== "object")
    [ SIf(match === "A") [ SExp(log(0)) ] [ SBreak(loop_0) ] ]
    [ SIf(match.TAG === "B")
        [ SIf(k !== 1) [ SExp(log(k)) ] [ SExp(n = match._0)  SExp(exit = 1) ] ]
        [ SIf(k !== 2) [ SExp(log(k)) ] [ SExp(n = match._0)  SExp(exit = 1) ] ] ]
  SIf(exit === 1) [ SExp(total = total + n | 0)  SExp(log(n)) ]
```

JavaScript (tested):

```js
function f(xs, k) {
  let total = 0;
  loop_0: for (let i = 0, i_finish = xs.length; i < i_finish; ++i) {
    let match = xs[i];
    let exit = 0;
    let n;
    if (typeof match !== "object") {
      if (match === "A") {
        console.log(0);
      } else {
        break loop_0;
      }
    } else if (match.TAG === "B") {
      if (k !== 1) {
        console.log(k);
      } else {
        n = match._0;
        exit = 1;
      }
    } else if (k !== 2) {
      console.log(k);
    } else {
      n = match._0;
      exit = 1;
    }
    if (exit === 1) {
      total = total + n | 0;
      console.log(n);
    }
  }
  return total;
}
```

### 4.5 Loop labels

Rule (`ensure_current_loop_label` (C:2059), `lam_compile_context.ml:92-102`): a
loop frame has no label until a `Break` or `Continue` with
`switch_depth > 0` asks for it; then it gets `loop_N`, where `N` is a counter
that starts at 0 for each top-level group (3.4) and is shared by the
functions inside the group.

Resolved Q2: the following named-variant dispatch becomes conditionals,
not a JavaScript switch:

```rescript
let h = (c, xs: array<t>) => {
  g(
    if c {
      for i in 0 to Array.length(xs) - 1 {
        switch Array.getUnsafe(xs, i) {
        | A => break
        | B(n) => log(n)
        | C(n, m) => log(n + m)
        | D => log(4)
        }
      }
      1
    } else {
      2
    },
  )
}
```

The OCaml reference emits **no loop label** for this dispatch, including
when the conditional is directly in return position. The small arms of
`compile_general_cases` preserve the incoming context
(`compiler/core/lam_compile.ml:740-762`); only its general JavaScript-switch
arm calls `enter_switch` (`compiler/core/lam_compile.ml:793`). `Lbreak` and
`Lcontinue` request the innermost loop's label only when `switch_depth > 0`
(`compiler/core/lam_compile.ml:2086-2118`). The legacy Rust port previously
entered switch context around the entire named-variant dispatch, producing
an unnecessary `loop_0` for the return-position example. It now enters that
context in the general switch arm instead, in all lowering continuations.

The counter also advances in lowerings whose output is discarded. The
`stringReturn` variant in `tests/tests/src/lowering_conditional_loop.res`
retains a real JavaScript switch: the OCaml reference prints `loop_1: for
(...)` and `break loop_1;`. `EffectCall should_return` first probes both
branches with `NeedValue should_return`
(`compiler/core/lam_compile.ml:1636-1644`); the discarded probe allocates
`loop_0`, and the retained return lowering allocates `loop_1`. The legacy
Rust return lowering previously retained the first pass and printed
`loop_0`. It now saves the existing label counter before lowering return
branches. If that lowering allocated labels, it resets the counter to the
saved value, performs the value probe, and lowers the retained return
branches with the resulting counter. The decision uses the counter already
maintained by label allocation, not another traversal of the Lambda body.
Ordinary foldable conditionals require no additional value probe. Labels
are allocated lazily, not on entering a loop
(`compiler/core/lam_compile_context.ml:92-102`).

The fixture and its OCaml-generated `.mjs` cover the original return shape,
a non-return conditional, nested loops, and string dispatch. The minimal
before-change outputs are recorded in
[LOWERING_REFERENCE_EXPERIMENTS.md](LOWERING_REFERENCE_EXPERIMENTS.md).

The rule lives in `bir/lower/label.rs`. Only retained lowering builds J:

- Each requested loop gets a unique, non-interned symbolic `StrId`. Loop
  statements and jumps, including copied untagged arms, share that handle.
  Group finalization aliases its string-pool entry to the numbered spelling;
  no J traversal or per-user patch list is needed.
- During the same source traversal, a pooled event program summarizes six
  continuation classes: **V**, **D**, **A**, **E**, **R**, and named tail-loop
  **R**. **D** cannot alias **A** (it probes conditional branches), nor **V**
  (only **V** resets counters along a top-level binding spine).
- Each summary is a pair: internal allocations and the offset of the first
  enclosing-frame request. Composition counts that external request once
  across discarded passes. Loop boundaries consume the body's request;
  conditions and bounds keep the outer frame.
- A single explicit-stack replay follows retained events. A discarded pass
  consumes its cached summary in O(1), assigning an external frame on its
  first request. Top-level groups reset and restore counters explicitly.
  No source body is re-lowered, and nested conditionals do not cause repeated
  subtree walks or range remapping.
- Event edges and source frames are 12 bytes; scheduling tasks are 16 bytes.
  All lists are pooled. Six fixed-size summaries per event and one replay
  make scheduling O(source edges + retained events), independent of the
  exponential work the discarded legacy probes would perform.

Q2 is checked by 512 deterministic generated loop/switch/conditional shapes,
using the actual legacy lowering as the discarded-pass reference and comparing
printed text in every tested continuation and both parenthesis modes. Separate
oracles cover top-level counter restoration and recursive self-tail calls.
The latter exposed a legacy discrepancy: a self-call prevented the initial
probe's labels from being consumed. The isolated fix is covered against OCaml
by `tests/js_output_parity/fixtures/self_tail_loop_labels.res` in eight modes.
A second reference fixture, `inherited_loop_labels.res`, found case-first
label allocation in legacy general string switches. Both lowerers now visit
the default first, as `compiler/core/lam_compile.ml:794-799` does, while
emitting grouped cases before the default. The temporary conditional-label
Unsupported arm has been removed.

### 4.6 What S3.5 found in the legacy choice

The rule tests of S3.5 lower one catch in return position in 952 shapes
(body, handler, parameters, what encloses the catch, `return_unit`) with the
legacy code and with 4.1. They disagreed on 51, in two families, and the
OCaml compiler was run on source for each:

1. **The handler holds a catch under a function, and no exit of its own.**
   `lambda_contains_staticcatch` looked into function bodies, so the legacy
   code took the explicit form. OCaml's `no_static_raise_in_handler` stops at
   a function (`lam_exit_code.ml:28`) and takes the cheap form.
2. **A catch without parameters whose body is a catch that exits to it,
   lowered under an enclosing catch.** An arm of
   `compile_staticcatch_in_return` took the cheap form without asking
   whether a catch enclosed it. OCaml has `in_staticcatch = true` there and
   takes the explicit form. With an exit to the enclosing catch in the body
   the legacy output also ran the wrong handler.

Both are fixed in the legacy code by the same change: the choice is
`staticcatch_takes_pseudo_jump`, and the 23 functions that made it before
are deleted. `tests/tests/src/lowering_static_catch.res` holds one function
per family with the JavaScript the OCaml compiler prints. After the change
the 952 shapes agree.

Three more places where the code needed what this document did not say:

- row R5 step 1 needs the fact `HAS_STATEMENT` (3.6, 7.1);
- a variable the lowering assigns is not `ASSIGNED` for sequencing (7.1);
- the jump table is indexed by catch header, not by label (4.1).

## 5. Tail calls as loops, `let rec`, `try`

### 5.1 Self tail calls

Design (`compile_recursive_let`, `lam_compile.ml:507-575`; `compile_apply`,
`lam_compile.ml:1745-1793`).

- Only a function that is the value of a `LetRec` member can become a loop,
  and only calls of that member's own variable count
  (`compile_recursive_binding` (C:2244) passes `&[*id]`). A function bound by
  `Let` cannot call itself.
- The lowering makes a record `r = {var, params, copies: param -> VarId,
  triggered}` (`params` is empty when the function has `one_unit_arg`), and
  lowers the body **once**, in a fresh function context (row K10) with
  `Effect(Return(Named { loop_: Some(r), in_catch: false }))`.
- `loop_` travels with the return continuation. From the rules of section 3
  it reaches: the body of a `Let` and of a `LetRec`, the second part of a
  `Seq`, both branches of an `If`, the right operand of `&&` and `||` (3.7),
  every case and the default of a `Switch` or `StrSwitch`, the body and the
  handlers of a `Catch`, and the handler of a `Try`. It does not reach the
  body of a `Try` or anything under a `TryFinally` (`Ret::InTry`), a loop
  body, an argument, or a nested function (which has its own context).
- A **self call**: `Apply(Var(r.var), args)` lowered in `Effect(Return(Named
  { loop_: Some(r), .. }))` or `Value(Return(Named { loop_: Some(r), .. }))`.
  The callee and the arguments are lowered and sequenced like any call (3.3)
  and the callee's value is dropped. `r.triggered` is set. For each parameter
  and argument, in parameter order (none when `params` is empty): if the
  argument is the parameter itself, nothing; otherwise the copy of the
  parameter is looked up, or created now as a fresh identifier named `_` +
  the parameter's name, and `copy = argument` is recorded. The statements
  are: the sequencing statements, the recorded assignments in **reverse**
  parameter order (C:4598), `continue` without a label. The output is
  finished.
- After the body: if `r.triggered` is clear, the function is built from the
  body as any function. If it is set, each parameter that has a copy is
  replaced by the copy in the parameter list, and the body becomes
  `while (true) { let x = _x; ...; body }` with one declaration (kind
  `Alias`) per copied parameter, in **descending** order of the parameter's
  identifier (`ext_ident_cmp` (C:6854): stamp, then name length, then name bytes;
  C:4043). In `Bir` the key is `(order, name length, name bytes)` of the
  parameter's `VarId`. This is a second place where the relative order of
  identifiers reaches the output (section 9).

The L arena records whether a recursive function has a self tail call during
construction/import, not lowering. Tail candidates are concatenated in the
same `control_facts` immediate-child fold as `HAS_EXIT`, `HAS_STATEMENT` and
`TRIVIAL_UNIT`. Tail-position children concatenate bounded
segments of pooled callee candidates; a `LetRec` matches the candidates of
each function against its binding. Candidate cells survive node relocation,
and the independent validator rebuilds the answer. The lowering reads this
fact to select the function's continuation. No pre-pass is needed and the
body is never lowered twice. The legacy code
asks `function_has_self_tailcall` (C:6772) before, threads `TailLoopState` through
its own family (row K7), and lowers the function again without the loop when
nothing was triggered.

Invariants:

1. `continue` never needs a label: a self call in tail position is not inside
   a loop of the function body (loop bodies are not in tail position), and a
   JS `switch` does not capture `continue`.
2. Every parameter some self call changes is copied at the top of the loop,
   so a closure created in one iteration captures that iteration's value: the
   declaration `let x = _x` is a fresh binding per iteration. A parameter no
   call changes has no copy and is read directly.
3. The assignments of one call are all evaluated from the current iteration's
   bindings: the arguments read `x`, the assignments write `_x`. Their order
   therefore does not change the values; it is byte-visible only.
4. When `triggered` is clear, the output is the same as without `loop_`: the
   record is read only by self calls.

Resolved Q5: compiling `g` in `tests/tests/src/lowering_nested_rec.res`
with the OCaml reference produces an outer `while (true)` and a self-call
jump (`_x = x - 1 | 0; continue;`), not `return g(x - 1 | 0);`.
`compile_recursive_let` creates a `return_label` containing the function's
`id`, `params`, `new_params`, `immutable_mask` and `triggered` flag, then
installs it as `Tail_with_name {label = Some ret; ...}` in the return
continuation (`compiler/core/lam_compile.ml:525-547`). `Lletrec` compiles
its bindings first and then its body with the original `lambda_cxt`
(`compiler/core/lam_compile.ml:2046-2057`): the nested function's own label
does not replace the enclosing function's return label. `compile_apply`
compares the callee with `ret.id` and sets `ret.triggered`
(`compiler/core/lam_compile.ml:1745-1752`); the enclosing function is then
wrapped in a loop (`compiler/core/lam_compile.ml:550-568`).

The legacy Rust port lost this in two places: `function_has_self_tailcall`
rejected `LetRec`, and `compile_tail_loop_return_output_inner` had no
`LetRec` arm. Both now follow the body, preserving the outer `TailLoopState`
after compiling the nested bindings. The fixture includes a captured outer
parameter and a further nested recursive binding; all match the reference.

Legacy differences from this design, all "read" unless marked:

| Difference | Where | Consequence |
| --- | --- | --- |
| A conditional in a function compiled as a loop is lowered by row R6, otherwise by row R5 | 3.6 | Q3 resolved: unit returns must exit the loop |
| The function is lowered twice when the pre-check says yes and nothing triggers | C:4027 | cost only, and the label counter (4.5) |

The J1 rule (C.3) inlines a function at a final `return f(...)` after
lowering. It can create a self call in tail position that is never made a
loop; that order is kept (C.2 row 10).

### 5.2 Worked example: a tail-recursive function whose closure captures a loop variable

Source:

```rescript
@val external later: (unit => int) => unit = "setTimeout"

let rec loop = (i, acc, fs) =>
  if i == 0 {
    acc
  } else {
    later(() => i + acc)
    loop(i - 1, acc + i, fs)
  }
```

Lambda (tested, `-drawlambda`):

```
(letrec
  (loop
     (function i acc fs
       (if (== i 0) acc
         (seq
           (seq (js_call[setTimeout] (function param (+ i acc))) unit)
           (apply loop (- i 1) (+ acc i) fs)))))
  (makeblock module/exports loop))
```

Lowering. `loop` is a `LetRec` member, so `r = {var: loop, params: [i, acc,
fs]}`. The body is an `If` in **R**: both branches are probed in **R**.
`acc` is free. The second branch is a `Seq`: its head in **E** is the
external call (a statement), its second part is the self call:

- arguments lowered left to right: `i - 1 | 0`, `acc + i | 0`, `fs`;
- `i`: not the parameter itself, copy `_i` created; `acc`: copy `_acc`
  created; `fs`: the parameter itself, nothing;
- statements: `_acc = acc + i | 0`, `_i = i - 1 | 0` (reverse parameter
  order), `continue`; finished.

The branch is not free, so the conditional is `if_(i === 0, [return acc],
[...])`; the `then` branch ends in `return`, so the `else` branch follows the
`if` (J-S3 rule 6). `triggered` is set: the parameters become `_i`, `_acc`,
`fs`, and the copies are declared in descending identifier order, `acc`
before `i`.

J nodes:

```
SDecl(loop, JFun(params [_i, _acc, fs])
  SWhile(true)
    SDecl(acc, _acc)                        -- Alias
    SDecl(i, _i)                            -- Alias
    SIf(i === 0) [ SReturn(acc) ] []
    SExp(setTimeout(JFun([]) [ SReturn(i + acc | 0) ]))
    SExp(_acc = acc + i | 0)
    SExp(_i = i - 1 | 0)
    SContinue)
```

JavaScript (tested). The closure reads `i` and `acc`, the per-iteration
bindings:

```js
function loop(_i, _acc, fs) {
  while (true) {
    let acc = _acc;
    let i = _i;
    if (i === 0) {
      return acc;
    }
    setTimeout(() => i + acc | 0);
    _acc = acc + i | 0;
    _i = i - 1 | 0;
    continue;
  };
}
```

Two more cases, tested, that fix the reach of `loop_`:

```rescript
let rec f = x => x > 0 && f(x - 1)       // the right operand of && is a tail call

let rec h = x =>
  try {
    if ext(x) { h(x - 1) } else { x }    // in the try body: a plain call
  } catch {
  | _ => h(x - 2)                        // in the handler: the loop jump
  }
```

```js
function f(_x) {
  while (true) {
    let x = _x;
    if (x <= 0) {
      return false;
    }
    _x = x - 1 | 0;
    continue;
  };
}

function h(_x) {
  while (true) {
    let x = _x;
    try {
      if (ext(x)) {
        return h(x - 1 | 0);
      } else {
        return x;
      }
    } catch (exn) {
      _x = x - 2 | 0;
      continue;
    }
  };
}
```

A static catch in tail position of such a function, in the cheap form, with
the self call in the handler (tested; the Lambda is `(catch (if (!= n 0)
(exit 1) acc) with (1) (apply count (- n 1) (+ acc 1)))`):

```js
function count(_n, _acc) {
  while (true) {
    let acc = _acc;
    let n = _n;
    if (n === 0) {
      return acc;
    }
    _acc = acc + 1 | 0;
    _n = n - 1 | 0;
    continue;
  };
}
```

The exit has `order = -1`, so it lowers to nothing; the handler follows the
body and is lowered in the function's own continuation, where the call is a
self call.

### 5.3 `LetRec`

Design (`compile_recursive_lets`, `lam_compile.ml:507-692`;
`compile_recursive_bindings_output` (C:2215)). The groups arrive already split
into recursive clusters (`raw_lambda/lambda_scc.rs`, A.2).

1. **Order of the group.** If every member is a function the group keeps its
   order. Otherwise functions come first, stably
   (`sort_recursive_binding_group` (C:6710)).
2. **Lowering order.** The members are lowered **last first**, and each
   output is put in front of the outputs after it, so the statements are in
   group order while identifiers are created in reverse.
3. **Per member**, by the form of its value (`compile_recursive_binding` (C:2244)):

   | Value | Output | Placeholder |
   | --- | --- | --- |
   | a function | `let id = <function>` (kind `Alias`), through 5.1 | none |
   | a `Pmakeblock` whose arguments are all functions or constants, or anything that is not a `Pmakeblock` | `D(Alias, id)(value)`: an ordinary declaration | none |
   | a `Pmakeblock` of a record, an inline record with one non-constant constructor, or a constructor with one non-constant constructor, whose arguments are each a constant or a variable that is the member itself or not another member of the group (`compile_recursive_self_binding_makeblock` (C:2293)) | `let id = <dummy>` (kind `Variable`), then one field assignment per argument, in order (`compile_set_field` (K:246)) | none |
   | any other `Pmakeblock` | the statements of `V(value)`, then `Primitive_object.updateDummy(id, value)` | `let id = <dummy>` (kind `Variable`) |

   The dummy is `[]` for an array record, a tuple and a `ModuleExport` block;
   it is `{}` for `Module` and the other object-shaped tags
   (`recursive_dummy_object_expr` (C:2345)).
4. The placeholders of all members are put in front of the group's
   statements, in group order.
5. Then the body, in the continuation of the `LetRec` (3.4 for the legacy
   irregularity).

Facts read: none beyond the nodes. Whether a member is "another member of
the group" compares variables.

### 5.4 Worked example: mutually recursive `let rec` with non-function members

Source:

```rescript
type rec node = {value: int, next: unit => node, peer: node}

let rec a = {value: 1, next: () => b, peer: b}
and b = {value: 2, next: () => a, peer: a}
and f = x => g(x) + a.value
and g = x => if x > 100 { x } else { f(x + 1) }
```

Lambda (tested, `-drawlambda`). The converter has split the four bindings
into two clusters:

```
(letrec
  (a (makeblock [value;next;peer] 1 (function param b) b)
   b (makeblock [value;next;peer] 2 (function param a) a))
  (letrec
    (f (function x (+ (apply g x) (field:value/0 a)))
     g (function x (if (> x 100) x (apply f (+ x 1)))))
    (makeblock module/exports a b f g)))
```

Lowering the first group. No member is a function, so the order is `a`, `b`.
Lowered last first: `b`, then `a`. Both are `Pmakeblock`s with an argument
that is neither a constant nor a variable (the function), and with a variable
that is another member, so both take the last row: placeholder `let b = {}`,
statement `updateDummy(b, {...})`; then the same for `a`. Placeholders in
group order in front.

The second group is two functions; `f`'s read of `a.value` was folded to `1`
at level L (the block is known), and neither function calls itself in tail
position, so no loop. `g`'s body `f(x + 1)` is later inlined by rule J1 (a
function used once, at a final `return`).

J nodes after lowering:

```
SDecl(a, JObject{})                               -- Variable
SDecl(b, JObject{})                               -- Variable
SExp(Primitive_object.updateDummy(a, JBlockLit(record value,next,peer)
        [1, JFun([]) [SReturn(b)], b]))
SExp(Primitive_object.updateDummy(b, JBlockLit(record value,next,peer)
        [2, JFun([]) [SReturn(a)], a]))
SDecl(f, JFun([x]) [ SReturn(g(x) + 1 | 0) ])     -- Alias
SDecl(g, JFun([x]) [ SIf(x > 100) [SReturn(x)] [SReturn(f(x + 1 | 0))] ])
```

JavaScript (tested; the last function shows J1's inlining of `f`):

```js
let a = {};

let b = {};

Primitive_object.updateDummy(a, {
  value: 1,
  next: () => b,
  peer: b
});

Primitive_object.updateDummy(b, {
  value: 2,
  next: () => a,
  peer: a
});

function f(x) {
  return g(x) + 1 | 0;
}

function g(x) {
  if (x > 100) {
    return x;
  } else {
    return g(x + 1 | 0) + 1 | 0;
  }
}
```

### 5.5 `Try`, `TryFinally`, `Praise`

S3.7a implementation: exception-region selection reads no subtree flags and
walks no body. `TryFinally` inspects only the immediate body tag to fuse a
catch. Saved operands and completed blocks live in a dense frame pool; the
source traversal carries a four-byte frame index. The 10,000-deep test visits
20,001 source occurrences and copies at most 20,000 statements in every
continuation. A 40,001-node body still takes one form-selection operation.

Integration correction: when cross-module inlining borrows the cold pools
from J, the source function-owner table must first be extended to cover J-only
headers (for example a lowered one-unit-argument closure). Otherwise the next
imported function header indexes beyond that table. This does not change the
lowering rules or the default backend path.

Design (`compile_try`, `lam_compile.ml:1514-1565`).

| Continuation | `Try(body, exn, handler)` | Legacy |
| --- | --- | --- |
| **V** | a fresh `tmp` first; `let tmp;` (kind `Variable`); `try { A(tmp)(body) } catch (exn) { A(tmp)(handler) }`; value `tmp` | C:1779 |
| **D** | `let id;` with the binding's kind; `try` with both parts in `A(id)` | C:2465 |
| **A**, **E** | both parts in the continuation | C:5394, C:2658 |
| **R** | the body in the continuation with `Ret::InTry` in place of `Named`; the handler in the continuation unchanged | C:3017; in a loop C:4313 |

`TryFinally(body, fin)`: when `body` is a `Try`, one statement with `catch`
and `finally` (`compile_try_finally` (C:1400)). The body and the handler both get
the body's continuation (in **R**: both `InTry`, C:3030), because with a
`finally` the handler is not in tail position either. `fin` is lowered in
**E**. The continuations follow the table above.

Order: `tmp`, the body, the handler, `fin`.

A `try` statement's output is not finished, also in **R** (every path inside
returns or throws, but the legacy output is `BlockOutput::make`). `Praise` is
`throw v`, finished, in every continuation (`compile_primitive_js` (P:188),
P:783-789): what follows it in the same output is dropped, and a declaration
or assignment of its value is not built (`declare_compiled` (C:6648),
`assign_compiled` (C:6667)). When a finished top-level output cuts the unit short,
the exports are declared without values (C:789-807, 8.2).

Invariant: `Ret::InTry` is never replaced by `Named` on the way down, so
nothing inside a `try` body in tail position becomes a loop jump or a cheap
exit form. A nested function starts again with `Named`.

## 6. The J normalising rules

The inventory of every rewrite the J constructors perform, as C.5 is for
level L. It is the specification of `bir/j/norm.rs` (S3.2); each rule there
cites its row. "E" rows are `js_ir::build::exp`, "S" rows are
`js_ir::build::stmt`, "M" rows are `js_exp_make.rs`. A constructor not listed
builds its node as given.

Purity. Two predicates exist and differ: `expression_has_no_side_effects` (B:102)
("pure" below) and `js_expr_no_side_effects` (E:15) ("strictly pure"), which is
the same except that `**`, `/` and `%` require a literal right operand:
for integers, `**` accepts any exponent while `/` and `%` require nonzero;
float literals always qualify (including zero); bigint `**` requires the
positive-sign marker, while bigint `/` and `%` reject the digit spelling
`"0"`. These are the legacy predicate's exact syntactic tests, not a general
JavaScript exception analysis.
The E and S rows use the first, the M rows and the lowering the second,
except where a row says otherwise. Both are node flags in `Bir` (section 7).

"Equal" is `ocaml_eq_expression` (B:237) for expressions and `ocaml_eq_block` (B:217)
for statement lists: structural equality on a fixed set of kinds, false for
the others (a string append is never equal to anything).
`j/facts.rs::purity` computes both flags from immediate child facts in O(arity).
`j/equal.rs::equal` uses an explicit pair stack, stops at the first mismatch,
and counts compared node pairs. Like the legacy predicate it has no depth
limit: the bound is the smaller tree's node count plus compared literal bytes.

### 6.1 Expressions (`build::exp`)

| Row | Constructor | Trigger | Result | Implemented in |
| --- | --- | --- | --- | --- |
| J-E1 | `string_append` (B:398) | an operand is the empty string literal | the other operand | `je1_string_append` |
| | | both are string literals | one literal |  |
| | | `(a ^ "b") ^ ("c" ^ d)` | `(a ^ "bc") ^ d`, rebuilt through the constructor |  |
| | | `"a" ^ ("b" ^ c)` | `"ab" ^ c` |  |
| | | `(c ^ "b") ^ "a"` | `c ^ "ba"` |  |
| J-E2 | `length` (B:453) | a pure array or block literal, array length | the element count | `je2_length` |
| | | a string literal, string length | its UTF-16 length |  |
| | | a function literal, function length | its parameter count (minus one for a method) |  |
| J-E3 | `is_null_or_undefined` (B:480) | `null` or `undefined` | `true` | `je3_is_null_or_undefined` |
| | | a number, array or block literal | `false` |  |
| J-E4 | `bin` (B:491), tried in this order | `x + n`, `n` a negative integer literal (`rewrite_plus_negative_int_rhs` (B:765)) | `x - (-n)` | `je4_bin` |
| | | `len >= 0`, `len` a length of a pure target (`rewrite_length_bin_comparison` (B:685)) | `true` |  |
| | | `len > 0` | `len !== 0` |  |
| | | `<`, `<=`, `>`, `>=` on two integer literals (`fold_int_comparison` (B:659)); the left literal is read as unsigned | the boolean |  |
| | | `===` (`fold_strict_equality` (B:704)): two integer literals; two string literals; `null`/`undefined` against each other; `undefined` against a pure optional block; `null` or `undefined` against a pure boolean, number, `typeof`, function, array or block; two optional blocks compare their contents. `!==` is not folded | the boolean |  |
| | | `&&` | J-E5 |  |
| | | `\|\|` | J-E6 |  |
| J-E5 | `js_and` (B:797) | `x && x`, `x` a variable | `x` | `je5_js_and` |
| | | `x && (x && r)` | the right operand |  |
| | | `x && (l && x)` | `x && l` |  |
| | | `v !== undefined && v === <string or number literal>` | the right operand |  |
| | | both operands pure | J-E9, if it gives a result |  |
| J-E6 | `js_or` (B:836) | `x \|\| x`; `x \|\| (x \|\| r)`; `x \|\| (l \|\| x)` | `x`; the right operand; `x \|\| l` | `je6_js_or` |
| | | both operands pure | J-E10, if it gives a result |  |
| J-E7 | `cond` (B:512), tried in this order | both branches are `(effect, undefined)` | `(cond(test, effect_t, effect_e), undefined)` | `je7_cond` |
| | | the test is `false` or the integer `0` | the else branch |  |
| | | the test is `true`, or a pure number, array or block literal | the then branch |  |
| | | the branches are `true` and `false` | the test |  |
| | | the branches are equal | the branch if the test is pure, else `(test, branch)` |  |
| | | then is `c2 ? a : b` and `b` equals else | `cond(test && c2, a, else)` |  |
| | | then is `c2 ? a : b` and `a` equals else | `cond(test && !c2, b, else)` |  |
| | | else is `c2 ? a : b` and then equals `a` | `cond(test \|\| c2, then, b)` |  |
| | | else is `c2 ? a : b` and then equals `b` | `cond(test \|\| !c2, then, a)` |  |
| | | the test is `!c` | `cond(c, else, then)` if else is neither the integer `0` nor `undefined`; otherwise the node as given, the `!` rebuilt without its comment |  |
| | | else is `false` and J-E9 applies to `(test, then)` | its result |  |
| | | then is `false` and J-E9 applies to `(!test, else)` | its result |  |
| J-E8 | `not` (B:599) | an integer literal | `true` for 0, else `false` | `je8_not` |
| | | `!x` | `x` |  |
| | | a boolean literal | the other one |  |
| | | `===`, `!==`, `<`, `>=`, `<=`, `>` | the opposite comparison |  |
| | | `&&` or `\|\|` whose operands can both be negated (`push_negation` (B:633): `!x`, a boolean, `===`, `!==`, and these under `&&`/`\|\|`) | De Morgan |  |
| J-E9 | `simplify_and_` (B:956), on pure operands, recursion depth at most 10 | a `false` operand; a `true` operand | `false`; the other operand | `je9_simplify_and` |
| | | an operand is `a && b` or `a \|\| b` | the rule applied to the parts, recombined |  |
| | | `typeof x === "boolean" \| "string" \| "number"` with `x === <literal>` | the comparison if the literal has that type, else `false` |  |
| | | `Array.isArray(x)` with `x === <literal>` | `false` |  |
| | | `typeof x === "boolean"` with `x`, `!x` or `x !== <boolean>` | `x === true`, `x === false`, `x === <the other boolean>` |  |
| | | `typeof x === "string" \| "number" \| "object"` with `x !== <literal of that type, or null for object>` | no rewrite (the rule stops here) |  |
| | | `typeof x === ...` or `Array.isArray(x)` with `x !== <literal>` | the type test |  |
| | | equal operands | one of them |  |
| | | `x === c1` with `x === c2` or `x !== c2`, both literals | by the JavaScript equality of the literals (`js_eq_literal` (B:188)): one comparison, or `false` |  |
| J-E10 | `simplify_or_` (B:1148) | a `true` operand; a `false` operand | `true`; the other operand | `je10_simplify_or` |
| | | both operands can be negated | J-E9 on the negations, negated back |  |

### 6.2 Statements (`build::stmt`)

| Row | Constructor | Trigger | Result | Implemented in |
| --- | --- | --- | --- | --- |
| J-S1 | `exp` (B:1207) | `(a, b)` where one side is a number or `undefined` | the statement of the other side | `js1_exp` |
| | | a number or `undefined` | the empty block |  |
| J-S2 | `block` (B:1225) | no statement; one statement; one statement that is a block | the empty block; that statement; the rule again on the inner list | `js2_block` |
| J-S3 | `simplify_if` (B:1575) (`if_`), tried in this order | 0: empty-block statements in a branch | removed | `js3_simplify_if` |
| | | 1: the test is a boolean literal | the taken branch, through J-S2 |  |
| | | 2: the test is `!c` and else is not empty | `if_(c, else, then)` |  |
| | | 3: then is empty | both empty: nothing if the test is pure, else the test as a statement. Otherwise `if_(not(test), else, [])` |  |
| | | 4: each branch is exactly one `return` | `return cond(test, a, b)` |  |
| | | 5: else is exactly one `return` | one block: `if (!test) return b;` followed by then |  |
| | | 6: then ends in `return`, `throw`, `continue` or `break` | one block: `if (test) then` followed by else |  |
| | | 7: each branch is exactly one assignment, to the same target (`same_assignment_target` (B:1522)) | `target = cond(test, a, b)` |  |
| | | 8: each branch is exactly one expression statement | the statement `cond(test, a, b)` |  |
| | | 9: then is exactly `if (c2) t2 else e2`, and `e2` equals else, or `t2` (not empty) equals else | `if_(test && c2, t2, e2)`; `if_(test && !c2, e2, t2)` |  |
| | | 10: else is exactly `if (c2) t2 else e2`, and then (not empty) equals `t2`, or equals `e2` | `if_(test \|\| c2, then, e2)`; `if_(test \|\| !c2, then, t2)` |  |
| J-S4 | `normalize` (B:1268) (every statement constructor) | an integer switch on an integer literal; a string switch on a string literal | the matching clause's body, else the default's, as a block | `js4_normalize` |
| J-S5 | `unnest_block` (B:1565) | a list that is one block statement | its contents, repeatedly | `js5_unnest_block` |

Rules 5 and 6 of J-S3 return a block, and "ends in" in rule 6 looks at the
literal last statement of the list. Together with J-S5 this is the mechanism
of 1.3.

### 6.3 `js_exp_make.rs` and the helpers of the lowering

| Row | Function | Trigger | Result | Implemented in |
| --- | --- | --- | --- | --- |
| J-M0 | `remove_pure_subexpression` (E:96) | a variable, string, template, JSON or number literal; an index or array of such; a sequence | nothing; nothing; the sequence of what is left | `jm0_remove_pure_subexpression` |
| J-M1 | `js_seq` (E:399) | a side of an inner sequence, or the left operand, is a number or `undefined`; the left operand is a variable | that part dropped | `jm1_js_seq` |
| J-M2 | `compile_nullish_strict_comparison` (E:253), `compile_int_equality` (E:327) | `null`/`undefined` against each other, or against a strictly pure value that cannot be nullish; two equal float literals; two integer literals | the boolean. Otherwise a plain `===`/`!==` that J-E4 does not see | `jm2_nullish_strict_comparison`, `jm2_int_equality` |
| J-M3 | `to_int32` (E:483), `int32_bor` (E:570) | two integer literals | the result | `jm3_to_int32`, `jm3_int32_bor` |
| | | `x \| (y >>> 0)`, `(x >>> 0) \| y` | the shift dropped |  |
| | | `(x >>> n) \| 0`, `n > 0`; `(x \| 0) \| 0` | the inner expression, once |  |
| J-M4 | `int32_add` (E:488), `int32_minus` (E:498) | two integer literals | the wrapped result. Otherwise `(a + b) \| 0` through J-E4 and J-M3 | `jm4_int32_add_sub` |
| J-M5 | `int32_mul` (E:508) | a literal `0` and a pure other side | `0` | `jm5_int32_mul` |
| | | two integer literals | the wrapped result |  |
| | | a literal positive power of two | a left shift (J-M7) |  |
| J-M6 | `int32_pow` (E:545) | two integer literals | `ocaml_int32_pow` (E:535) | `jm6_int32_pow` |
| J-M7 | `int32_lsl` (E:555) | two integer literals | the result | `jm7_int32_lsl` |
| J-M8 | `int32_lsr` (E:596), `int32_bxor` (E:614), `int32_band` (E:631) | two integer literals for lsr/xor only (band does not fold literals); `(x >>> n) >>> 0`; `(x \| 0) >>> 0`; `x ^ (y >>> 0)`; `(x \| 0) & y` | the result; the redundant operation dropped | `jm8_int32_lsr`, `jm8_int32_bxor`, `jm8_int32_band` |
| J-M9 | `ocaml_typeof_expr` (E:640) | a number or length; a string; an array; a boolean | `"number"`, `"string"`, `"object"`, `"boolean"` | `jm9_typeof` |
| J-M10 | `int_bnot` (E:835) | an integer literal | the result | `jm10_int_bnot` |
| J-M11 | `pure_indexed_block_item` (E:664), `pure_record_field_item` (E:695), `direct_projection_from_pure_literal` (E:711), `poly_var_tag_access` (E:740), `poly_var_value_access` (E:750) (called from `compile_field_access` (K:186)) | a field of a strictly pure array or block literal | the element | `jm11_projection`, `jm11_poly_var_access` |
| J-M12 | `interpolated_template` (E:844) | a value that is a string or template literal without a comment | merged into the neighbouring segments; with no value left, a template literal | `jm12_interpolated_template` |
| J-M13 | `int32_div_expr` (C:6174, formerly C:6033), `int32_mod_expr` (C:6190, formerly C:6049) | `len / 2`; nonzero integer divisor; two integer literals | Division: `len >> 1`; plain division with `\| 0`; wrapped quotient. Modulo stays a plain `%`, without coercion or literal folding. A divisor that may be zero: `Primitive_int.div`/`mod_` when checks are on | `jm13_int32_div`, `jm13_int32_mod` |
| J-M14 | `push_effect_expression` (O:339), `push_s_if_empty` (O:359), `push_s_exp` (O:368) | a value used as a statement | a sequence split into statements; strictly pure parts dropped (`push_effect_expression`), or only numbers and `undefined` dropped (`push_s_exp`) | `jm14_push_effect_expression`, `jm14_push_s_exp`, `jm14_push_s_if_empty` |

Not rewriting: the comparison helpers of E (`comparison_to_binop` (E:161),
`compare_bool_literals` (E:296), `compare_string_literals` (E:364),
`compare_bigint_literals` (E:381) and the `both_*_literals` tests) compute what
the comparison arms of `compile_primitive_js` (P:188) fold; `iife` (E:780),
`fun_expr` (E:786), `string_switch_iife` (E:807), `raw_typeof_comparison` (E:653) and
`is_type_object_expr` (E:831) build nodes; `js_stmt_make.rs` holds predicates only
(`block_terminates` (S:9), `strict_single_return_expr` (S:18),
`block_finishes_output` (S:29)).

The lowering also builds nodes without a constructor, on purpose: a plain
`If` at C:4147 so that rule 2 of J-S3 does not swap it back, a plain `===` in
J-M2, `raw_bin` (B:383) in J-E5. The port keeps each such call plain.

J-E1 and J-E7 use loops and explicit suffix stacks: each reassociation or
conditional merge removes an input append/conditional node; stripping a leading
negation or paired comma suffix removes those input nodes. J-E9 uses the legacy
`n > 10` cutoff (so n=10 still tries the rules). The left-And arm can make four
recursive attempts, not three: two operand attempts, a third on `(a,b)`, and a
fourth force attempt on its result. The logical-attempt tree has a conservative
O(4^11) bound; equality and negation additionally inspect their compared trees.
Negation and equality use explicit stacks, never expression-depth recursion.
The 10,000-term chain test measures 8,188 inspected pairs/planner steps (one
step when a true operand immediately selects the chain). Successful recipes
move disjoint subtrees and copy only repeated/overlapping occurrences; failed
attempts leave both operands untouched. J-S3 loops only when it removes a leading test negation, swaps an empty then
branch into the else position, or removes a nested if. The empty-branch swap
cannot repeat without removing a negation or nested if. All other rules return.
J-S1/J-S2/J-S5 strip a comma/block shell per iteration; J-S4 scans the switch
keys once and consumes the selected statement list.

### 6.4 Implementation proofs and cost measurements

Every function in the "Implemented in" column is in `bir/j/norm.rs`.
`bir/j/plain.rs::node` is the typed, non-normalising constructor for every J
`View`; `plain::statement` additionally applies J-S4. Deliberately raw nodes
use `plain::node`, `plain::bin` or `plain::seq`. J1–J4 are not implemented here.

The following counts are **trigger groups** (nonempty Trigger cells in the
inventory, including their alternatives) and **test functions**, not generated
matrix cases. Test counts come from `cargo test ... bir::j:: -- --list` and
associate the row tags in each test name (including the J-M3–J-M8 range).
Shared matrix functions count for each named row. The functions are in
`bir/j/norm_tests.rs`, plus the original J-M14 test in `bir/j/norm.rs`.
Each row has positive and non-trigger cases; the matrices also test operand
order, differing literals, effectful operands and applicable purity boundaries.

| Row | Functions (`j/norm.rs`) | Trigger groups | Test functions |
| --- | --- | ---: | ---: |
| J-E1 | `je1_string_append` | 5 | 3 |
| J-E2 | `je2_length` | 3 | 3 |
| J-E3 | `je3_is_null_or_undefined` | 2 | 2 |
| J-E4 | `je4_bin` | 7 | 2 |
| J-E5 | `je5_js_and` | 5 | 1 |
| J-E6 | `je6_js_or` | 2 | 1 |
| J-E7 | `je7_cond` | 12 | 3 |
| J-E8 | `je8_not` | 5 | 3 |
| J-E9 | `je9_simplify_and` | 9 | 6 |
| J-E10 | `je10_simplify_or` | 2 | 3 |
| J-S1 | `js1_exp` | 2 | 1 |
| J-S2 | `js2_block` | 1 | 2 |
| J-S3 | `js3_simplify_if` | 11 | 4 |
| J-S4 | `js4_normalize` | 1 | 2 |
| J-S5 | `js5_unnest_block` | 1 | 1 |
| J-M0 | `jm0_remove_pure_subexpression` | 1 | 3 |
| J-M1 | `jm1_js_seq` | 1 | 4 |
| J-M2 | `jm2_nullish_strict_comparison`, `jm2_int_equality` | 1 | 2 |
| J-M3 | `jm3_to_int32`, `jm3_int32_bor` | 3 | 2 |
| J-M4 | `jm4_int32_add_sub` | 1 | 2 |
| J-M5 | `jm5_int32_mul` | 3 | 2 |
| J-M6 | `jm6_int32_pow` | 1 | 2 |
| J-M7 | `jm7_int32_lsl` | 1 | 2 |
| J-M8 | `jm8_int32_lsr`, `jm8_int32_bxor`, `jm8_int32_band` | 1 | 2 |
| J-M9 | `jm9_typeof` | 1 | 3 |
| J-M10 | `jm10_int_bnot` | 1 | 1 |
| J-M11 | `jm11_projection`, `jm11_poly_var_access` | 1 | 3 |
| J-M12 | `jm12_interpolated_template` | 1 | 2 |
| J-M13 | `jm13_int32_div`, `jm13_int32_mod` | 1 | 2 |
| J-M14 | `jm14_push_effect_expression`, `jm14_push_s_exp`, `jm14_push_s_if_empty` | 1 | 4 |

The 10,000-term tests measure these costs before bulk-finalisation/validation:

| Rule | Shape | Measured cost |
| --- | --- | ---: |
| J-E1 | append reassociations | 400,053 node reads |
| J-E7 | nested conditional merges | 320,082 node reads |
| J-E8 | deep De Morgan | 680,031 node reads |
| J-E9 | conjunction chain, nontrivial attempt | 8,188 planner steps/compared pairs |
| J-E10 | negated conjunction chain | 13,841 planner steps/compared pairs |
| J-S2/J-S5 | 10,000 shells around 10,000 statements | 80,024 node reads |
| J-S3 | nested if merges | 440,109 node reads |
| J-M0 | sequence chain | 130,002 node reads |
| J-M1 | sequence chain | 110,054 node reads |
| J-M14 | effect sequence chain | 150,024 node reads |

Node-read counts do not count copied literal bytes. Logical-attempt counts
include explicit negation visits and partial-equality pairs, not only recursive
attempt calls. Their depth budget is bounded; the structural inspections are
bounded by the inspected input/output trees. `Bir::j_stats` records attempt
counts and per-arena maxima. Set `RESCRIPT_J_NORMALISATION_STATS` to a separate
output directory during `RESCRIPT_BACKEND=check` corpus builds to collect JSON
snapshots on J export. Snapshots with identical counters share a filename;
maxima are independent of thread scheduling. No global counter is used.

Check-mode builds of the runtime, `tests/tests`, and a 3,735-module application
recorded zero J-E9/J-E10 attempts: the current lowering slice has no logical
constructor producers. Their corpus maximum is therefore **not applicable**,
not evidence of trigger coverage. The row oracle matrices and deep tests above
exercise those rules directly. No lowering cases or fallback baselines were
expanded by this work.


## 7. Cost

The lowering is one pass over the L tree of a unit. A step is one L node
read, one J node built, one statement pushed or copied, or one flag read.

### 7.1 Facts instead of walks

Each row is a question the legacy code answers by walking a subtree, and the
maintained fact that answers it in `Bir`. The flags are computed when a node
is built, from the children's flags, as `PURE` is (B.4). `NodeFlags` has no
free bit: J expression nodes do not use `VALUE_UNUSED`, `DEAD` or `NO_ALLOC`,
so the J flags below reuse those positions, and L nodes do not use
`JS_CHAR_PRESENT` or `JS_LOC_PRESENT`, which `HAS_EXIT` and `HAS_STATEMENT`
reuse. `Var` is an operation of both levels and carries neither L flag.

| Legacy walk | Asked by | Fact |
| --- | --- | --- |
| `lam_analysis::no_side_effects` | `lambda_is_trivial_unit_undefined` (C:3550), the predicates of K14 | `PURE` (B.4) |
| `has_exit_code(handler, in table)`, `has_exit_code(handler, any)`, `lambda_has_exit` (C:7524) | flattening (4.1 step 1), the cheap form's test, `break` in a return continuation (3.9 step 4, 4.1) | L flag `HAS_EXIT`: the subtree contains an `Exit` that is not under a `Fun`. Clear answers at once. Set: for "any" it is the answer; for "in table" the handler is walked, pruned by the flag |
| `function_has_self_tailcall` (C:6772) | 5.1 | none needed: `triggered` |
| `lambda_contains_statement_value_form` (C:5016) | 3.6 row R5 step 1 | L flag `HAS_STATEMENT`: the subtree contains, not under a `Fun`, a switch, catch, exit, try, loop, assignment, `Break` or `Continue`. `probe` does not answer it: a branch that is not free can still lower to effects followed by one return |
| every `lambda_contains_*`, `*_requires_explicit_*`, `uses_*fallthrough*` of row K14 (deleted by S3.5) | 4.1 | none needed: `in_catch` and `HAS_EXIT` |
| `free_variables(body)` | `compile_for_of` (C:2154) | `uses[v] == 0` |
| `arena_assigned_variables` (whole unit, and per inlined body in `extend_assignable` (A:280)) | `delay_safe` (A:28) | `ASSIGNED` |
| `expression_has_no_side_effects` (B:102) | J-E2, J-E4, J-E5, J-E6, J-E7, J-S3 | J flag `PURE` |
| `js_expr_no_side_effects` (E:15) | the lowering, the M rows | J flag `STRICT` (pure, and no `**`, `/`, `%` that may throw) |
| `is_pure_subexpression` (E:146) | J-M0 | J flag `J_SUBEXPR`, reusing L `DEAD`; distinct from both purity predicates |
| `delay_safe` (A:28) | sequencing | J flag `DELAY_SAFE`. It depends on `ASSIGNED` of the variables in the expression, which is final before lowering starts: an assignment the lowering builds (a result temporary, a handler parameter) does not set it in the lowering's arena, as the legacy `assignable` set holds the targets of L assignments only |
| `runs_no_code` (A:90) | sequencing | Iterative inspection of the owned record-field spine; unknown property reads stop it. Variables read the final `JS_GLOBAL` fact. This predicate differs from `J_SUBEXPR` and does not share its bit |
| `lam_subst::subst` of a handler per raise (`resolve_static_raise` (C:6113)) | K15 | removed (Q1) |
| the second and third lowering of a branch | 3.6 | `probe` |
| the second lowering of a function | 5.1 | `triggered` |
| `Vec<Stmt>` concatenation up the spine | everywhere | the statement stack (1.3) |

### 7.2 What must never happen

1. Lowering a node more than once. (The debug assertion of invariant P1 does,
   and only below its size bound.)
2. Walking a subtree to answer purity, "has an exit", "is assigned", "is
   used", or "needs statements".
3. Copying a statement list more than once (stack to list).
4. Recursing on the top-level spine or on a `Let`/`Seq` chain with the Rust
   stack: both are as long as the module. The spine is a loop (3.4); `Let`
   and `Seq` in a continuation that passes through unchanged (`k(body)`,
   `k(second)`) are a loop too.
5. Substituting a handler or a function body during lowering, except the
   cross-module attempt of 3.3, which is `Unsupported` until S3.8.

### 7.3 What remains bounded but not constant

| Operation | Cost | Bound |
| --- | --- | --- |
| lowering a node | the node, its J nodes, its statements | constant per node, plus the rows below |
| grouping switch cases and exit handlers (3.9 step 2) | each case is compared with the heads of the groups before it by `eq_approx`, which stops at the first difference | `cases x groups` comparisons. Quadratic for a switch with many distinct bodies. The step count of the compared node pairs is reported per corpus (as `Stats::compared` is for N11, C.5). Open (Q7): whether a cached structural hash is needed |
| J-E7, J-S3 rules that compare branches (`ocaml_eq_expression`, `ocaml_eq_block`) | stops at the first difference | counted the same way |
| J-E9 | O(4^11) bounded logical attempts, plus equality/negation inspections and duplicated output | counted (section 6) |
| flattening catches | one flag read per handler; a walk of a handler that has `HAS_EXIT`, over its nodes that have the flag, with one label lookup per exit met | a handler is tested once, by the chain that reaches its catch; a node is read once per handler it lies in whose catch is tested that way, so the bound is the nesting depth of handlers that hold exits. Measured at 10,000 nested catches: 9,999 flag reads and no node read when the handlers hold no exit; 9,999 flag reads and 9,999 node reads when each handler is one exit to the catch around it; one flag read for a handler of 60,001 nodes without an exit |
| sequencing arguments | one right-to-left scan; a held argument's literal is entered once | linear in the arguments |
| `source_loc_of_lam` (source maps only) | a descent along first children | the depth of the case body, once per clause |
| label numbers (4.5) | five integers per output that has labels; one prefix sum per group | linear in the labels and conditionals of a group that has labels |
| `realize` | each node of a `Free` once | a `Free` is realized once |
| a conditional (3.6) | constant, plus the statements of a branch that becomes a list (copied once) or is discarded; a branch kept as the statements after a guard is not read | each statement is written once and copied to a list once. Measured at 10,000 nested conditionals whose innermost branch needs a statement: 20,001 copies in **V** and **A**, 10,000 in **R** |
| row R5 step 0 | one `TRIVIAL_UNIT` flag read per branch | maintained with `HAS_EXIT` and `HAS_STATEMENT` by `Bir::control_facts` during construction/import and repair; independently checked by `Bir::validate` |
| row R5 step 1 | the expression statements that lead each branch, stopping at the first other statement | a statement leads the branch of one conditional: an enclosing branch starts with a guard or with other statements, unless a test in between is a boolean literal (rule 0 keeps its branch without a guard) |
| `S.if_` | `norm::js3_simplify_if` takes two list-pool handles; shared rules 0 to 6 also accept statement-stack run handles so retained tails stay in place | consumed statements and shells, plus structural comparisons and J expression rules; no per-branch vectors |

S3.9 primitive costs: the resume is two `u32` handles (8 bytes), retaining
an existing source-list handle rather than allocating an operand vector. Up to
four sequenced outputs and values are inline. Literal min/max duplication copies
only leaf handles and decoration, never a generic subtree/hash-map copier.
Module constant summaries are acquired once per imported module into an
`ImportId`-indexed table; the summary state is 16 bytes. Export lookup still uses
field names because the summary interface has no field-index handle.

The primitive cost tests include 10,000 nested identities and a 10,000-element
block (10,001 source visits / 10,000 argument steps each), 10,000 dictionary
entries (30,002 source visits / 30,001 argument steps / 50,003 immediate
primitive steps), and 10,000 runtime-compare shells stripped by one comparison
(20,003 source visits / 20,002 argument steps / 40,004 immediate primitive
steps). These are opt-in lowering costs: this slice claims no improvement to
the default emitted backend. Arena-owned variable-width cold payloads (block
metadata, property lists, templates) continue to use the existing J pool API;
this slice does not replace those representations.

S3.4 switch costs (`switch.rs`, `variant.rs`, `untagged.rs`, `location.rs`):

- Source bodies have dense 16-byte fingerprint/exit records. A fingerprint
  indexes case positions, and candidate matches are confirmed with iterative
  `eq_approx`; case heads/links and plan handles are dense arrays. A primitive's
  payload is borrowed, not cloned just to dispatch on it.
- Direct/named grouping takes expected O(cases + newly fingerprinted nodes +
  confirmed pairs), preserving last-member group order. The unchanged untagged
  planner retains its own grouping/simplification costs; the new emitter is an
  explicit linear program over its emitted tree. This does not claim that the
  existing planner's pairwise grouping became linear.
- Continuation handles are 4 bytes. Emission operations are 8 bytes, pending
  untagged walks 12, and action/output records 16. Cold integer/string, named,
  and untagged plans are respectively 200, 88, and 336 bytes, pinned by tests.
- Source maps alone allocate an 8-byte-per-source-node location cache. Each
  search node is visited once; a located NONE stops the search before filtering,
  and fallthrough labels retain their own location rather than the group's.
- Repeated untagged outputs use the arena's existing subtree copier, with
  binder remapping and bulk use-count finalization. Single-use runs are moved,
  not copied. The existing copier has its existing map/allocation costs; no
  claim of an allocation-free copier is made here.

| 10,000-element shape | Source visits | Fingerprint visits | Equality confirmations |
| --- | ---: | ---: | ---: |
| distinct integer bodies | 10,002 | 10,000 | 0 |
| equal pairs | 5,002 | 10,000 | 5,000 |
| one shared body | 3 | 10,000 | 9,999 |
| nested integer switches (all five continuations) | 20,001 | 10,000 | 0 |
| distinct named bodies | 10,002 | 10,000 | 0 |
| nested small named sides | 20,001 | 0 | 0 |
| nested untagged payload dispatches | 20,001 | 10,000 | 0 |

A separate 10,000-switch source-location chain takes 10,001 location visits;
repeating the search takes none. Mapped oracle tests cover all four dispatch
families and all five continuations. Normalized J expressions also cache delay
safety from immediate children: corpus checking exposed an unnecessary held
arithmetic argument when a later argument was an untagged switch.

S3.5 exit costs (`exit.rs`):

- The jump-table entry is 8 bytes, the traversal frame of a catch a 4-byte
  handle, of an exit 16 bytes; the cold plan of a catch is 168 bytes. The
  handlers of the catches being lowered are one stack of 8-byte entries, and
  the walk of a handler that has an exit reuses one work vector: nothing is
  allocated per catch with one handler or per exit. A table of several
  handlers allocates the group vectors of the switch lowering once.
- The form of a catch costs at most two flag reads: one per flattened
  handler, one for the cheap form.
- An exit costs one label lookup and one step per argument. Arguments are
  lowered last first; with more than one, each run is moved once to its
  reserved slot.

| 10,000-element shape (every continuation) | Source visits | Flag reads | Handler nodes read | Fingerprint visits |
| --- | ---: | ---: | ---: | ---: |
| nested catches, one table | 20,003 | 9,999 | 0 | 10,000 |
| nested catches, each handler exits to the catch around it | 20,003 | 9,999 (10,000 in **R**) | 9,999 | 0 |
| one catch, handler of 60,001 nodes without an exit, in **R** | | 1 | 0 | 0 |

### 7.4 Step-count tests each stage adds

In the form of C.6: a test builds a unit, lowers it, and asserts the number
of steps. Each slice adds the tests of its constructs on a 10,000-deep and a
10,000-wide input, with a bound stated as steps per L node.

| Slice | Tests |
| --- | --- |
| S3.3 | a chain of 10,000 `Let`s; 10,000 nested `Seq`s in first and in second position; a call with 10,000 arguments, one with a statement last (sequencing); 10,000 nested conditionals in **V** whose innermost branch needs a statement (the case the legacy code lowers 2^10,000 times): linear, each branch lowered once; the same in **D**, **E** and **R**; a 10,000-element block literal; `a_statement_is_copied_once`: the stack-to-list copies equal the statements |
| S3.4 | a switch with 10,000 cases with one shared body, and with 10,000 distinct bodies (reports the comparisons; the bound is set after Q7); 10,000 nested switches |
| S3.5 | 10,000 nested catches that flatten into one table; 10,000 nested catches that do not flatten (each handler exits to the one before); a handler of 40,000 nodes without `HAS_EXIT` costs one flag read |
| S3.6 | a recursive function with 10,000 self calls in 10,000 switch cases; one whose only self call is not in tail position (lowered once, not twice) |
| S3.7 | 10,000 nested loops with a labelled `break` in the innermost; the label property test of 4.5; a `LetRec` of 10,000 members |
| S3.8 | an external call with 10,000 arguments |
| S3.9 | 10,000 JSX children and props; 10,000 scoped callee/key members; 10,000 await shells, record overrides/rest exclusions, flat-make segments (success and failure), and import path segments |

### S3.9 measured costs and policy boundaries

The tests count source dispatch visits, argument-sequencing steps and immediate
primitive/path steps separately. Each fixture below has 10,000 elements.

| Shape | Source visits | Sequencing steps | Primitive/path steps |
| --- | ---: | ---: | ---: |
| JSX children, statement-producing last child | 20,003 | 30,000 | 40,001 |
| JSX props, half absent optional props | 10,002 | 10,001 | 20,002 |
| JSX scoped callee | 2 | 1 | 10,001 |
| JSX key record-member chain | 10,003 | 10,002 | 30,004 |
| Await shells | 10,001 | 10,000 | 20,000 |
| Record-copy overrides | 10,002 | 0 | 40,002 |
| Record-rest excluded labels | 2 | 1 | 10,002 |
| Successful flat-make path | 1 | 0 | 10,001 |
| Failed flat-make path | 10,001 | 10,000 | 40,000 |
| External import value path | 1 | 0 | 10,001 |

Flat-make paths are recognized before argument lowering. Successful paths
consume their source spine without constructing intermediate member expressions;
failed paths are memoized in a dense source-node table, preventing quadratic
rescans of nested `make` fields over a non-module base. The record-copy resume
is 12 bytes; the primitive resume is now 8 bytes because it no longer needs a
source handle after dispatch.

Awaited-unit membership is recorded at each `Let` on the existing source walk
in a `VarId`-indexed table, rather than by a separate unit traversal. The
candidate transports its own dynamic dependency list to the shared tail; the
check no longer borrows the legacy lowering's list. Invalid import diagnostics
remain owned by the legacy side of check mode, while both expressions are
undefined. External module identity uses the first bundle/default binding.

`jsx_preserve` affects the shared passes and printer, not `compile_jsx` or
`jsx_callee`. The rule oracle prints both settings; JSX metadata retains
fragment, multi-child, optional-prop, spread and key policy. The declaration
exception for record copies is documented in section 3.4. These are opt-in
lowering changes; they claim no default-path performance improvement.

### 7.5 Allocation-site inventory (S3.2d baseline)

Baseline: `e5ada1df93`. This is the **pre-conversion inventory**, not a claim
that lowering is allocation-free. `pending` means the site is still present.
Line numbers refer to this baseline; function names are the stable references.
The excluded concurrent slice is `loops.rs`, `label.rs`, and `rec.rs`.
Test modules (including `oracle_tests.rs`) are excluded.

The required discovery command is:

```sh
rg -n 'Vec::new|vec!\[|SmallVec|Box::new|\.collect\(|\.to_vec\(|\.clone\(\)|String::' compiler-rust/src/bir/lower
```

The table also includes `Vec` fields/signatures, `Vec::with_capacity`,
turbofish `collect`, `to_owned`, and `into_vec`, which that command misses.
A signature/import row identifies storage/API ownership, not a separate
allocation instruction. Empty-vector constructors are kept even though they
allocate only on growth; fixed-capacity small vectors are not exempted.
"Per construct" includes per call, catch, switch, function or literal,
not once per compilation. Payload clones must be checked through their
nested fields (e.g. a function attribute owns an optional directive string).

Rows marked `removed` describe implemented changes; `pending` rows remain
intended design, **not implemented state**.
In particular, switching a local vector to a pool handle requires changing
consuming APIs too: `JsPayload::Object` owns a property-key vector, switch
headers own keys/clauses, and the untagged dispatch planner owns its plan.
Moving those allocations outside this directory would not satisfy the audit.
The statement stack and node-list pool must be used end to end.

| Baseline file:line and function/type | Site | Frequency | Replacement / reason retained | State |
| --- | --- | --- | --- | --- |
| `args.rs:46` `evaluate_now` | `fn evaluate_now(&mut self, root: NodeId) -> (Vec<NodeId>, NodeId) {` | per construct/walk | reusable scratch buffer; clear, do not free | pending |
| `args.rs:51` `Work` | `let mut work = vec![Work::Enter(root)];` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `args.rs:52` `Work` | `let mut values = Vec::new();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `args.rs:53` `Work` | `let mut statements = Vec::new();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `args.rs:111` `Work` | `let children: Vec<_> = values.drain(values.len() - count..).collect();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `args.rs:163` `sequence_arguments` | `args: smallvec::SmallVec<[Out; 4]>,` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `args.rs:164` `sequence_arguments` | `) -> (Span, smallvec::SmallVec<[NodeId; 4]>) {` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `args.rs:178` `sequence_arguments` | `let mut values = smallvec::SmallVec::with_capacity(args.len());` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `args.rs:184` `sequence_arguments` | `(Vec::new(), value)` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `call.rs:9` `Call` | `pub operands: Vec<NodeId>,` | per construct | pooled source operand lists and retained spine scratch; four-byte call frame | removed |
| `call.rs:32` `application` | `let mut reversed: Vec<_> = args.iter().rev().copied().collect();` | per construct | pooled source operand lists and retained spine scratch; four-byte call frame | removed |
| `call.rs:48` `application` | `let mut operands = Vec::with_capacity(1 + reversed.len());` | per construct | pooled source operand lists and retained spine scratch; four-byte call frame | removed |
| `call.rs:66` `application` | `return Ok(Call { tail: None, operands: vec![reduced], inline: true, status, loc, external: None });` | per construct | pooled source operand lists and retained spine scratch; four-byte call frame | removed |
| `call.rs:94` `inline_external_function` | `let root = lambda.function_(function.arity, &function.params, body, function.attr.clone(), function.loc);` | per construct | borrow payload or retain typed pool handle | pending |
| `call.rs:104` `inline_external_function` | `let mut foreign = Vec::new();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `call.rs:175` `finish_application` | `.collect();` | per construct | reusable traversal/output/argument buffer retained in lowering state | removed |
| `call.rs:197` `finish_application` | `self.apply_with_arity(callee, arity, values.into_vec())` | per construct | reusable scratch buffer; clear, do not free | pending |
| `call.rs:267` `resolve_cmj_module_field_arity` | `crate::cmi::persistent_env::CmjExportArity::Single(arity) => Some(arity.clone()),` | per construct | borrow payload or retain typed pool handle | pending |
| `call.rs:289` `apply_with_arity` | `args: Vec<NodeId>,` | per construct | reusable scratch buffer; clear, do not free | pending |
| `call.rs:300` `apply_with_arity` | `callee = self.call_node(callee, &remaining[..count], full.clone());` | per construct | stays: call-info scalar clone; no heap value | non-allocating |
| `call.rs:313` `apply_with_arity` | `let mut full_args = remaining.to_vec();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `cond.rs:154` `conditional_children` | `into: &mut Vec<(Cx, NodeId)>,` | per construct | reusable scratch buffer; clear, do not free | pending |
| `exit.rs:75` `Plan` | `groups: Vec<usize>,` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:76` `Plan` | `next: Vec<usize>,` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:77` `Plan` | `bodies: Vec<NodeId>,` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:78` `Plan` | `output: Vec<NodeId>,` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:79` `Plan` | `clauses: Vec<ClauseMeta>,` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:282` `catch` | `(Vec::new(), Vec::new(), Vec::new())` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:300` `catch` | `output: Vec::new(),` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:301` `catch` | `clauses: Vec::new(),` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:314` `catch_children` | `pub(super) fn catch_children(&self, cx: Cx, frame: Catch, into: &mut Vec<(Cx, NodeId)>) {` | per construct | borrows the retained source traversal queue; owns no buffer | retained |
| `exit.rs:436` `exit_dispatch` | `let mut keys = Vec::with_capacity(plan.len as usize);` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:437` `exit_dispatch` | `let mut clauses = Vec::with_capacity(plan.len as usize);` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:438` `exit_dispatch` | `let mut actions = Vec::with_capacity(plan.len as usize);` | per construct | typed grouping/output spans and pooled switch keys, clauses and actions | removed |
| `exit.rs:509` `exit_children` | `pub(super) fn exit_children(&self, cx: Cx, exit: &Exit, into: &mut Vec<(Cx, NodeId)>) {` | per construct | borrows the retained source traversal queue; owns no buffer | retained |
| `expr.rs:42` `expression_children` | `into: &mut Vec<(Cx, NodeId)>,` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `expr.rs:278` `finish_expression` | `let attr = attr.clone();` | per visited node | borrow payload or retain typed pool handle | pending |
| `expr.rs:308` `drop_pure_effect` | `let mut effects = Vec::new();` | per construct/walk | reusable traversal/output/argument buffer retained in lowering state | removed |
| `external.rs:8` `module` | `use smallvec::SmallVec;` | declaration | removed SmallVec import | removed |
| `external.rs:64` `compile_js_object_create` | `args: SmallVec<[NodeId; 4]>,` | per construct | list-pool handle; no transient argument collection | removed |
| `external.rs:68` `compile_js_object_create` | `let mut keys = Vec::new();` | per construct | PropertySpan into the arena property-key pool | removed |
| `external.rs:69` `compile_js_object_create` | `let mut values = Vec::new();` | per construct | ListId adopted directly by object_from_list | removed |
| `external.rs:70` `compile_js_object_create` | `let mut effects: SmallVec<[NodeId; 4]> = SmallVec::new();` | per construct | single Option<NodeId>, fused in source order | removed |
| `external.rs:71` `compile_js_object_create` | `let mut pending: Vec<(u32, NodeId)> = Vec::new();` | per construct | State::external_pending, taken, drained and returned | removed |
| `external.rs:229` `translate_scoped_global_value` | `let head = scopes.first().map_or(name, String::as_str);` | per construct | stays: borrowed string projection; no allocation | non-allocating |
| `external.rs:266` `translate_scoped_module_value` | `let head = scopes.first().map_or(name, String::as_str);` | per construct | stays: borrowed string projection; no allocation | non-allocating |
| `external.rs:287` `external_module_binding` | `bundle: name.to_owned(),` | per construct | borrowed module spelling; owned import metadata remains in import.rs | removed |
| `external.rs:312` `compile_js_call` | `args: SmallVec<[NodeId; 4]>,` | per construct | list-pool handle; no transient argument collection | removed |
| `external.rs:384` `compile_js_call` | `args.collect(),` | per construct | list-pool handle; no transient argument collection | removed |
| `ffi_args.rs:6` `module` | `use smallvec::SmallVec;` | declaration | SmallVec import moved into test module only | removed |
| `ffi_args.rs:112` `hold_external_args` | `args: SmallVec<[Out; 4]>,` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:113` `hold_external_args` | `) -> SmallVec<[Out; 4]> {` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:115` `hold_external_args` | `let mut held = SmallVec::with_capacity(args.len());` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:136` `hold_external_obj_args` | `args: SmallVec<[Out; 4]>,` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:137` `hold_external_obj_args` | `) -> SmallVec<[Out; 4]> {` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:138` `hold_external_obj_args` | `let params: SmallVec<[&ObjParam; 4]> = specs` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:146` `hold_external_obj_args` | `.collect();` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:147` `hold_external_obj_args` | `let mut suffix: SmallVec<[LaterLiteral; 4]> = SmallVec::with_capacity(args.len());` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:200` `hold_external_obj_args` | `.collect()` | per construct | borrowed output slice and reusable suffix/spec-index buffers | removed |
| `ffi_args.rs:299` `external_dispatch` | `let mut keys = Vec::new();` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:300` `external_dispatch` | `let mut actions = Vec::new();` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:301` `external_dispatch` | `let mut clauses = Vec::new();` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:363` `external_polyvar_string_expr` | `let cases: Vec<_> = cases` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:365` `external_polyvar_string_expr` | `.map(&#124;(key, value)&#124; (key.clone(), plain::string(&mut self.arena, value)))` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:366` `external_polyvar_string_expr` | `.collect();` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:389` `external_polyvar_int_expr` | `let cases: Vec<_> = cases` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:391` `external_polyvar_int_expr` | `.map(&#124;(key, value)&#124; (key.clone(), plain::int(&mut self.arena, *value as i32)))` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:392` `external_polyvar_int_expr` | `.collect();` | per construct | pooled keys, clauses and action lists; borrowed case strings | removed |
| `ffi_args.rs:403` `external_polyvar_event_exprs` | `) -> SmallVec<[NodeId; 2]> {` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:427` `external_polyvar_event_exprs` | `smallvec::smallvec![tag, value]` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:438` `lower_external_arg_values_and_effect` | `) -> (SmallVec<[NodeId; 2]>, Option<NodeId>) {` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:441` `lower_external_arg_values_and_effect` | `smallvec::smallvec![self.external_option_unwrap_expr(cx, raw)],` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:454` `lower_external_arg_values_and_effect` | `return (SmallVec::new(), None);` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:456` `lower_external_arg_values_and_effect` | `Attr::Ignore => return (SmallVec::new(), self.external_arg_effect(cx, arg)),` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:460` `lower_external_arg_values_and_effect` | `SmallVec::new()` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:462` `lower_external_arg_values_and_effect` | `smallvec::smallvec![plain::node(&mut self.arena, View::JUndefined, 1)]` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:476` `lower_external_arg_values_and_effect` | `(smallvec::smallvec![value], None)` | per construct | fixed [Option<NodeId>; 2], 16 bytes; no spill path | removed |
| `ffi_args.rs:502` `assemble_external_args_no_splice` | `args: SmallVec<[NodeId; 4]>,` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:503` `assemble_external_args_no_splice` | `) -> (SmallVec<[NodeId; 4]>, Option<NodeId>) {` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:505` `assemble_external_args_no_splice` | `let mut values = SmallVec::with_capacity(specs.len());` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:506` `assemble_external_args_no_splice` | `let mut effects: SmallVec<[NodeId; 4]> = SmallVec::new();` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:548` `assemble_external_args_with_splice` | `args: SmallVec<[NodeId; 4]>,` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:549` `assemble_external_args_with_splice` | `) -> (SmallVec<[NodeId; 4]>, Option<NodeId>) {` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:551` `assemble_external_args_with_splice` | `let mut values = SmallVec::with_capacity(specs.len());` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:552` `assemble_external_args_with_splice` | `let mut effects: SmallVec<[NodeId; 4]> = SmallVec::new();` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:595` `assemble_external_args` | `args: SmallVec<[NodeId; 4]>,` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `ffi_args.rs:597` `assemble_external_args` | `) -> (SmallVec<[NodeId; 4]>, Option<NodeId>) {` | per construct | ListId input/output and reusable argument assembly buffer | removed |
| `import.rs:110` `external_module` | `name: external.bundle.clone(),` | per construct | borrow payload or retain typed pool handle | pending |
| `import.rs:114` `external_module` | `.clone()` | per construct | borrow payload or retain typed pool handle | pending |
| `import.rs:176` `compile_import` | `.push(self.arena.pools.j_modules[module.index()].clone());` | per construct | borrow payload or retain typed pool handle | pending |
| `import.rs:194` `capitalize` | `let mut result = String::with_capacity(s.len());` | per construct | reusable scratch buffer; clear, do not free | pending |
| `import.rs:218` `external_binding_name` | `let mut result = String::new();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `import.rs:234` `external_binding_name` | `name.clone()` | per construct | borrow payload or retain typed pool handle | pending |
| `jsx.rs:70` `compile_jsx` | `let mut props = Vec::with_capacity(jsx.jsx_props.len());` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `jsx.rs:71` `compile_jsx` | `let mut values = Vec::with_capacity(` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `jsx.rs:159` `duplicate_jsx_key` | `let mut spine = smallvec::SmallVec::<[NodeId; 4]>::new();` | per visited node | list-pool handle (outputs: reusable output-buffer span) | pending |
| `konst.rs:55` `Work` | `let mut work = vec![Work::Enter(root)];` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `konst.rs:56` `Work` | `let mut values: Vec<(NodeId, bool)> = Vec::new();` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `konst.rs:60` `Work` | `let constant = self.arena.constant(id).clone();` | per visited node | borrow payload or retain typed pool handle | pending |
| `konst.rs:177` `Work` | `let children: Vec<_> = values.drain(start..).map(&#124;(node, _)&#124; node).collect();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `mod.rs:190` `children` | `fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>);` | per construct | reusable scratch buffer; clear, do not free | pending |
| `mod.rs:230` `Work` | `let mut work = vec![Work::Enter(cx, node)];` | per construct | reusable traversal/output/argument buffer retained in lowering state | removed |
| `mod.rs:231` `Work` | `let mut values = Vec::new();` | per construct | reusable traversal/output/argument buffer retained in lowering state | removed |
| `mod.rs:232` `Work` | `let mut children = Vec::new();` | per construct | reusable traversal/output/argument buffer retained in lowering state | removed |
| `mod.rs:295` `Lowered` | `pub dynamic_imports: Vec<crate::js_ir::ModuleId>,` | per construct | reusable scratch buffer; clear, do not free | pending |
| `mod.rs:333` `State` | `tail_frames: Vec<tail::Frame>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:334` `State` | `tail_functions: Vec<Option<LoopRef>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:335` `State` | `tail_copies: Vec<Option<VarId>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:336` `State` | `tail_assignments: Vec<NodeId>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:337` `State` | `tail_order: Vec<VarId>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:338` `State` | `rec_values: Vec<Option<NodeId>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:339` `State` | `switches: Vec<Option<switch::Plan>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:340` `State` | `variants: Vec<Option<variant::Plan>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:341` `State` | `untagged: Vec<Option<untagged::Plan>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:342` `State` | `switch_facts: Vec<switch::Facts>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:343` `State` | `switch_work: Vec<(NodeId, bool)>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:344` `State` | `switch_pairs: Vec<(NodeId, NodeId)>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:345` `State` | `switch_primitive_hashes: Vec<u64>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:346` `State` | `switch_constant_hashes: Vec<u64>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:352` `State` | `idents: Vec<Ident>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:356` `State` | `invalid_module_paths: Vec<bool>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:357` `State` | `awaited_units: Vec<bool>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:358` `State` | `dynamic_imports: Vec<crate::js_ir::ModuleId>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:359` `State` | `external_references: Vec<Option<crate::bir::ImportId>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:360` `State` | `external_globals: Vec<Option<VarId>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:361` `State` | `inline_globals: Vec<Ident>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:363` `State` | `external_bindings: Vec<[Option<VarId>; 2]>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:364` `State` | `module_constants: Vec<ModuleConstants>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:366` `State` | `located_functions: Vec<bool>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:372` `State` | `switch_locations: Vec<location::Fact>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:373` `State` | `location_work: Vec<(NodeId,bool)>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:380` `State` | `scratch: Vec<NodeId>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:383` `State` | `jumps: Vec<exit::Jump>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:385` `State` | `catch_table: Vec<(NodeId, crate::bir::CatchId)>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:386` `State` | `catches: Vec<Option<exit::Plan>>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:387` `State` | `tries: Vec<try_::Plan>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:389` `State` | `catch_work: Vec<NodeId>,` | once per unit | stays: reusable lowering-state storage | retained |
| `mod.rs:418` `new` | `.collect();` | once per unit | stays: once per unit | retained |
| `mod.rs:424` `new` | `tail_frames: Vec::new(), tail_functions: Vec::new(), tail_copies: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:425` `new` | `tail_assignments: Vec::new(), tail_order: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:426` `new` | `rec_values: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:427` `new` | `switch_facts: vec![switch::Facts::default(); input.arena.nodes.len()],` | once per unit | stays: once per unit | retained |
| `mod.rs:428` `new` | `switches: Vec::new(), variants: Vec::new(), untagged: Vec::new(), switch_work: Vec::new(), switch_pairs: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:429` `new` | `switch_primitive_hashes: Vec::new(), switch_constant_hashes: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:431` `new` | `invalid_module_paths: vec![false; input.arena.nodes.len()],` | once per unit | stays: once per unit | retained |
| `mod.rs:432` `new` | `awaited_units: vec![false; input.arena.vars.len()],` | once per unit | stays: once per unit | retained |
| `mod.rs:433` `new` | `dynamic_imports: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:434` `new` | `external_references: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:435` `new` | `external_globals: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:436` `new` | `inline_globals: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:438` `new` | `external_bindings: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:439` `new` | `module_constants: (0..arena.pools.j_modules.len()).map(&#124;_&#124; ModuleConstants::Unread).collect(),` | once per unit | stays: once per unit | retained |
| `mod.rs:447` `new` | `located_functions: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:453` `new` | `switch_locations: Vec::new(), location_work: Vec::new(), location_steps: 0,` | once per unit | stays: once per unit | retained |
| `mod.rs:457` `new` | `scratch: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:458` `new` | `jumps: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:459` `new` | `catch_table: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:460` `new` | `catches: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:461` `new` | `tries: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:463` `new` | `catch_work: Vec::new(),` | once per unit | stays: once per unit | retained |
| `mod.rs:560` `enter` | `let args = args.to_vec();` | per construct | pooled source operand lists and retained spine scratch; four-byte call frame | removed |
| `mod.rs:713` `children` | `fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>) {` | per construct | reusable scratch buffer; clear, do not free | pending |
| `out.rs:52` `StatementStack` | `slots: Vec<Option<Slot>>,` | once per unit | stays: reusable statement-stack storage | retained |
| `out.rs:53` `StatementStack` | `held: Vec<NodeId>,` | once per unit | stays: reusable statement-stack storage | retained |
| `out.rs:62` `StatementStack` | `empties: Vec<(u32, NodeId)>,` | once per unit | stays: reusable statement-stack storage | retained |
| `out.rs:378` `FreePool` | `nodes: Vec<Option<Free>>,` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `out.rs:435` `Work` | `let mut work = vec![Work::Enter(root, cx)];` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `out.rs:436` `Work` | `let mut outputs = Vec::new();` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `prim.rs:122` `finish_primitive_payload` | `.collect();` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `prim.rs:127` `finish_primitive_payload` | `let mut outputs: smallvec::SmallVec<[Out; 4]> = outputs;` | per visited node | reusable traversal/output/argument buffer retained in lowering state | removed |
| `prim.rs:164` `finish_primitive_payload` | `.collect::<Vec<_>>(),` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `prim.rs:173` `finish_primitive_payload` | `let (keys, kept): (Vec<_>, Vec<_>) = entries.into_iter().unzip();` | per visited node | property-key pool handle (requires J payload API change) | pending |
| `prim.rs:195` `finish_primitive_payload` | `let mut keys = Vec::new();` | per visited node | property-key pool handle (requires J payload API change) | pending |
| `prim.rs:196` `finish_primitive_payload` | `let mut kept = Vec::new();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `prim.rs:272` `finish_primitive_payload` | `let info = self.arena.js_info(crate::bir::JsPayload::Block(tag.clone()));` | per visited node | borrow payload or retain typed pool handle | pending |
| `prim.rs:372` `finish_primitive_payload` | `norm::jm12_interpolated_template(&mut self.arena, segments.clone(), values.into_vec())` | per visited node | borrow payload or retain typed pool handle | pending |
| `prim.rs:381` `finish_primitive_payload` | `.collect();` | per visited node | reusable scratch buffer; clear, do not free | pending |
| `prim_block.rs:13` `flat_make_field` | `let mut segments = smallvec::SmallVec::<[&str; 4]>::new();` | per visited node | list-pool handle (outputs: reusable output-buffer span) | pending |
| `prim_block.rs:14` `flat_make_field` | `let mut visited = smallvec::SmallVec::<[NodeId; 4]>::new();` | per visited node | list-pool handle (outputs: reusable output-buffer span) | pending |
| `record.rs:38` `record_copy` | `let mut operands = vec![*init];` | per construct | reusable scratch buffer; clear, do not free | pending |
| `record.rs:39` `record_copy` | `let mut keys = vec![PropertyKey::RecordSpread];` | per construct | property-key pool handle (requires J payload API change) | pending |
| `record.rs:83` `record_children` | `pub(super) fn record_children(&self, cx: Cx, record: &Record, into: &mut Vec<(Cx, NodeId)>) {` | per construct | reusable scratch buffer; clear, do not free | pending |
| `record.rs:105` `finish_record` | `let mut values = Vec::with_capacity(self.source.lists.get(record.operands).len());` | per construct | reusable scratch buffer; clear, do not free | pending |
| `record.rs:154` `duplicate_record` | `.js_info(JsPayload::Object(vec![PropertyKey::RecordSpread]));` | per construct | property-key pool handle (requires J payload API change) | pending |
| `record.rs:177` `record_rest` | `.collect();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `scope.rs:16` `Scope` | `pub(crate) uses: Vec<Uses>,` | once per unit | stays: dense variable-indexed table | retained |
| `scope.rs:24` `new` | `uses: vec![Uses::default(); variables],` | once per unit | stays: once per unit | retained |
| `switch.rs:33` `Plan` | `groups: Vec<usize>,` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:34` `Plan` | `next: Vec<usize>,` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:35` `Plan` | `pub(super) bodies: Vec<NodeId>,` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:37` `Plan` | `output: Vec<NodeId>,` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:38` `Plan` | `clauses: Vec<ClauseMeta>,` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:71` `integer_switch` | `let keys = h.keys[..n].to_vec();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:75` `integer_switch` | `let mut actions = all[..n].to_vec();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:82` `integer_switch` | `clauses: Vec::new(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:140` `plan_switch` | `(0..count).collect(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:141` `plan_switch` | `vec![NONE; count],` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:142` `plan_switch` | `self.source.lists.get(operands)[..count].to_vec(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:169` `plan_switch` | `output: Vec::new(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:170` `plan_switch` | `clauses: Vec::new(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:205` `group_switch_cases` | `) -> (Vec<usize>, Vec<usize>, Vec<NodeId>) {` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:212` `group_switch_cases` | `let cases = self.source.lists.get(operands)[..count].to_vec();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:213` `group_switch_cases` | `let fingerprints: Vec<_> = cases.iter().map(&#124;n&#124; self.switch_facts[n.index()]).collect();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:217` `group_switch_cases` | `let mut groups = Vec::new();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:218` `group_switch_cases` | `let mut next = vec![NONE; cases.len()];` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:219` `group_switch_cases` | `let mut heads: Vec<usize> = (0..cases.len()).collect();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:253` `group_switch_cases` | `let bodies = groups.iter().map(&#124;&i&#124; cases[i]).collect();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:547` `switch_children` | `pub(super) fn switch_children(&self, cx: Cx, frame: Switch, into: &mut Vec<(Cx, NodeId)>) {` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:684` `finish_switch` | `let mut keys = Vec::new();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:685` `finish_switch` | `let mut clauses = Vec::new();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:686` `finish_switch` | `let mut actions = Vec::new();` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:693` `finish_switch` | `crate::lambda::SwitchCaseTag::String(self.arena.text(*text).to_owned()),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:695` `finish_switch` | `key => key.clone(),` | per construct | pooled group/output runs and typed key/clause/action handles | removed |
| `switch.rs:831` `prepare_switch_hashes` | `let mut bytes = Vec::new();` | once per unit | retained serialization scratch buffer | removed |
| `switch.rs:892` `switch_constants_equal` | `let mut work = smallvec::SmallVec::<[(crate::bir::ConstId, crate::bir::ConstId); 8]>::new();` | per construct | retained constant-pair scratch buffer | removed |
| `switch.rs:962` `finish_small_switch` | `let key = self.arena.switch(plan.header).keys[0].clone();` | per construct | borrowed key from its temporarily acquired pool; no clone | removed |
| `tail.rs:40` `finish_self_call` | `pub(super) fn finish_self_call(&mut self, frame: LoopRef, statements: Span, values: smallvec::SmallVec<[NodeId; 4]>) -> Probed {` | per construct | borrowed node slice supplied by reusable sequencing buffer | removed |
| `try_.rs:65` `try_children` | `pub(super) fn try_children(&self, cx: Cx, frame: Try, into: &mut Vec<(Cx, NodeId)>) {` | per construct | reusable scratch buffer; clear, do not free | pending |
| `unit.rs:33` `lower` | `.collect();` | once per unit | stays: once per unit | retained |
| `untagged.rs:53` `Plan` | `program: Vec<Op>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:55` `Plan` | `actions: Vec<Action>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:56` `Plan` | `cached: Vec<Option<NodeId>>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:57` `Plan` | `finished: Vec<Finished>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:58` `Plan` | `remaining: Vec<u32>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:59` `Plan` | `marks: Vec<Span>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:60` `Plan` | `outputs: Vec<Output>,` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:82` `untagged_switch` | `let facts = facts.clone();` | per construct | borrow source matching facts while appending to the unit graph | removed |
| `untagged.rs:83` `untagged_switch` | `let mut literal_arms = Vec::with_capacity(n);` | per construct | input buffer retained; mixed/literal planner still copies it via Cow::into_owned | pending |
| `untagged.rs:84` `untagged_switch` | `let mut payload_arms = Vec::with_capacity(h.keys.len() - n);` | per construct | retained payload-arm buffer; owned tag clones tracked separately | removed |
| `untagged.rs:88` `untagged_switch` | `literal_arms.push((tag.literal.clone(), i as u32))` | per construct | borrow payload or retain typed pool handle | pending |
| `untagged.rs:91` `untagged_switch` | `block.block_type().expect("untagged payload").clone(),` | per construct | borrow payload or retain typed pool handle | pending |
| `untagged.rs:97` `untagged_switch` | `let sources = self.source.lists.get(operands).to_vec();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:135` `untagged_switch` | `let remaining = actions.iter().map(&#124;a&#124; a.uses).collect();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:136` `untagged_switch` | `let cached = vec![None; actions.len()];` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:137` `untagged_switch` | `let finished = vec![Finished::False; actions.len()];` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:153` `untagged_switch` | `marks: Vec::new(),` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:154` `untagged_switch` | `outputs: Vec::new(),` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:167` `untagged_program` | `) -> (Vec<Op>, Vec<Action>) {` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:168` `untagged_program` | `let mut program = Vec::new();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:169` `untagged_program` | `let mut actions: Vec<Action> = Vec::new();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:170` `untagged_program` | `let mut cache = vec![[NONE; 2]; sources.len()];` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:171` `untagged_program` | `let mut work = vec![Work::Visit(plan.root(), depth)];` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:248` `untagged_children` | `pub(super) fn untagged_children(&self, cx: Cx, frame: Untagged, into: &mut Vec<(Cx, NodeId)>) {` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:332` `copy_dispatch_output` | `let mut vars = Vec::new();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:333` `copy_dispatch_output` | `let mut labels = Vec::new();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:414` `advance_untagged` | `let body: Vec<_> = self.statements.statements(out.run).collect();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:489` `untagged_switch_statement` | `.collect::<Vec<_>>(),` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:511` `untagged_switch_statement` | `.collect(),` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:522` `untagged_switch_statement` | `let mut actions = Vec::with_capacity(keys.len() + usize::from(has_default));` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:523` `untagged_switch_statement` | `let mut clauses = Vec::with_capacity(actions.capacity());` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:589` `untagged_test` | `let mut work = vec![(test, false)];` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `untagged.rs:590` `untagged_test` | `let mut values = Vec::new();` | per construct | typed unit-owned pool runs or retained scratch; no construct-owned vector | removed |
| `variant.rs:29` `Plan` | `sides: Vec<Side>,` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:89` `named_variant` | `let tag_name = facts.tag_name.as_deref().unwrap_or("TAG").to_owned();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:90` `named_variant` | `let keys: Vec<_> = h` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:101` `named_variant` | `.collect();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:102` `named_variant` | `let mut keys = [keys, Vec::new()];` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:131` `named_variant` | `let mut sides = Vec::with_capacity(2);` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:139` `named_variant` | `let actions: Vec<_> = range` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:140` `named_variant` | `.clone()` | per construct | borrow payload or retain typed pool handle | pending |
| `variant.rs:143` `named_variant` | `.collect();` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:147` `named_variant` | `clauses: Vec::new(),` | per construct | reusable scratch buffer; clear, do not free | pending |
| `variant.rs:183` `literal_tag` | `Literal::String(s) => Tag::String(s.clone()),` | per construct | borrow payload or retain typed pool handle | pending |
| `variant.rs:185` `literal_tag` | `Literal::Float(s) => Tag::Float(s.clone()),` | per construct | borrow payload or retain typed pool handle | pending |
| `variant.rs:186` `literal_tag` | `Literal::BigInt(s) => Tag::BigInt(s.clone()),` | per construct | borrow payload or retain typed pool handle | pending |
| `variant.rs:255` `variant_children` | `pub(super) fn variant_children(&self, cx: Cx, frame: Variant, into: &mut Vec<(Cx, NodeId)>) {` | per construct | reusable scratch buffer; clear, do not free | pending |

The external allocation tests now start from their Lambda source nodes, after
one-time import, and include source traversal, constant lowering, FFI holding,
argument sequencing, emission, deferred realization and release of the J output.
After warming and reserving another pass's append-only pool growth, 10,000
eight-argument calls and one 10,000-field object allocate zero times. Source
visits are 99,999 and 10,001; primitive steps are 250,000 and 40,001.
A separate whole-Lambda FFI test lowers 10,000 string-dispatch cases with zero
allocations, two source visits and 10,004 primitive steps. All three tests assert
unchanged recorded buffer capacities. Import and final unit export are outside
these scopes; no claim is made that their once-per-unit allocations disappear.

Property spans are 8 bytes, operand-list handles 4 bytes, pending entries 8
bytes, and `JsPayload` 40 bytes. Bounded FFI argument conversion uses a fixed
16-byte pair of optional handles, with no spill path. Switch keys and clauses
are stored in typed pools, referenced by 8-byte spans; the cold stored switch
record is 96 bytes. Existing import builders transfer their owned input into
these pools; the FFI emitter writes directly into the pools without an owned
intermediate switch header. Other switch emitters' transient input vectors
remain pending in their inventory rows.

Source traversal, deferred realization, constant traversal, argument holding
and sequencing retain their work buffers between probes. Debug child-sharing
validation uses a reusable dense epoch table rather than a per-node hash set;
the sharing check still happens before mutation. Module metadata still owns
spelling/attributes at the J bridge boundary; borrowing the module-itself
spelling removes its temporary descriptor, not those outstanding allocations.

The direct-switch slice stores grouped case heads/links, representative source
bodies, lowered actions and clause metadata in flat unit-owned pools. A source
frame remains a 4-byte switch handle; its cold plan is 108 bytes (formerly 200).
The 24-byte group descriptor is cold data; helpers borrow it. Fingerprints are
values without arena identities, so their retained hash table maps fingerprints
to case positions while all per-case state remains in dense indexed arrays.
A 10,000-case whole-Lambda switch with distinct string-valued bodies allocates
zero times after warming and pool reservation, at 10,002 source visits and
20,000 grouping steps; recorded capacities remain unchanged. Pooled J keys
retain interned spelling handles, including floats and big integers, rather
than cloning strings into each output header.

The untagged plan now contains **no owned vectors**. Its 120-byte cold record
refers to typed unit-wide program/action/stack pools; the shared dispatch graph's
four pools also live once per lowering state. The owned legacy planner API and
borrowed append API invoke the same planning function. Source-body equivalence
is computed through the existing structural grouping pass, then the planner uses
dense aliases. Incomparable bodies receive no alias, even for self-comparison.

A complete Lambda fixture with 10,000 nested single-payload dispatches now runs
twice with **zero allocations** in the measured second pass and unchanged
recorded capacities: 20,001 source visits, 10,000 emission-program steps and
20,000 grouping steps. It includes planning, traversal, emission, realization
and release. Import is outside measurement; append-only growth is pre-reserved
after warming. This does **not** prove the mixed/literal 10,000-case fixture:
its shared planner still uses temporary vectors and clones owned tag metadata.
Subtree copying and literal-test conversion also remain outstanding.

| Additional owning API/site | Frequency | Disposition |
| --- | --- | --- |
| `untagged.rs` former `Plan.dispatch` | per construct | converted: four graph pools owned by `State::untagged_dispatch` |
| `untagged_dispatch.rs` `PlanInput.literal_arms.into_owned()` | per mixed/literal plan | pending: borrowed input still copied by the general planner; not counted as an allocation removal |
| `untagged_dispatch.rs` grouping, payload partitioning and simplification vectors | per general plan | pending: replace with typed runs and retained scratch |
| `untagged.rs` literal and instance arm metadata clones | per arm | pending: replace owned tag payloads with metadata handles |
| `edit.rs` `copy_subtree_recording` temporary maps and vectors | per copied action | pending: reusable indexed copy state required |

Catch plans now own no vectors and occupy 80 bytes (120 before the output
conversion, 168 before grouping was pooled). The 10,000-catch whole-Lambda
fixture emits a flattened integer dispatch and measures zero allocations on its
warmed second pass, with unchanged recorded capacities, 20,001 source visits,
9,999 flattening flag reads and 20,000 grouping steps. This also exposed constant
interning's temporary serialized-key vector: constant keys now use an 8-byte
byte-pool span and retained encoding scratch, rather than one owned vector per
constant. Compound constant contents and canonical encodings are unchanged.

The tail-call argument consumer already borrows the sequencing buffer. Its
whole-Lambda call test exposed three earlier copies (source args, reversed spine,
and call operands): those are now source list handles and retained spine scratch.
A call's 64-byte cold metadata record lives in a unit pool; the walk carries a
4-byte handle. Copied-parameter name formatting also uses retained string scratch.
The 10,000-argument test establishes an enclosing function context, then lowers
the entire Lambda call, arguments, sequencing and jump emission and releases the
output twice. The measured pass allocates zero times with unchanged capacities,
10,002 source visits and 10,001 argument visits (including the callee). This
fixture does not measure wrapping the enclosing function into a loop.

### 7.5.1 Concurrent loop, label and recursive-value additions

The baseline exclusions for `loops.rs`, `label.rs` and `rec.rs` no longer apply
after integrating `81b8b26a5`. These are the new production `Vec` sites; no
production `SmallVec` site was introduced in these three files. Test-fixture
vectors are not compile-path allocations.

| Site at integration | Storage | Frequency | Disposition |
| --- | --- | --- | --- |
| `loops.rs:59` `loop_children` | borrowed `&mut Vec<(Cx, NodeId)>` | shared source traversal | retained caller-owned buffer; not an owned construct vector |
| `rec.rs:77` `recursive_children` | borrowed `&mut Vec<(Cx, NodeId)>` | shared source traversal | retained caller-owned buffer; not an owned construct vector |
| `rec.rs:93` `recursive_dummy` | `JsPayload::Object(Vec::new())` | per dummy | removed: `object_info(&[])` adopts property-pool metadata |
| `label.rs:115` `Schedule.frames` | `Vec<Frame>` | once-per-unit stack | retained typed frame pool; high-water capacity reused |
| `label.rs:116` `Schedule.values` | `Vec<Edge>` | once-per-unit stack | retained typed event stack; high-water capacity reused |
| `label.rs:117` `Schedule.edges` | `Vec<Edge>` | once-per-unit pool | retained indexed event-edge pool |
| `label.rs:118` `Schedule.steps` | `Vec<Step>` | once-per-unit pool | retained indexed scheduling-step pool |
| `label.rs:119` `Schedule.costs` | `Vec<[Cost; 6]>` | once-per-unit pool | retained dense costs indexed by scheduling step |
| `label.rs:120` `Schedule.numbers` | `Vec<Option<u32>>` | once-per-unit pool | retained dense numbers indexed by loop |
| `label.rs:121` `Schedule.work` | `Vec<Work>` | once-per-unit stack | retained scheduling scratch; high-water capacity reused |

The 10,000-node whole-Lambda while-loop fixture confirms that this retained
storage allocates zero times after warming and explicit append-only reservation.
It includes output release, checks unchanged loop/scheduler capacities, and records
20,001 source visits. No production loop buffer needed replacement.

The labelled-loop fixture also lowers and releases 10,000 nested loops twice,
including an actual switch-nested break and symbol resolution. Its warmed pass
allocates zero times, preserves recorded capacities, visits 20,005 source nodes
and performs 30,007 scheduling steps. The second pass assigns a fresh label
number rather than reusing the first result. Scheduler vectors remain justified
unit-owned pools, not per-construct collections.

The integration keeps method-callee evaluation order and default-first string
switch traversal from trunk. Group outputs still write their stable pooled slots,
so no vector rotation is needed. Label finalization runs after each successful
probe while the retained traversal counts only that probe's new visits. All four
existing whole-Lambda zero-allocation fixtures still pass after integration.

## 8. The gate and the slices

### 8.1 The gate

Stage name `lower` in `bir::shadow` (C.7 step 7), run in `Check` mode
(G.1) for every unit. `New` retains the legacy lowering until the complete
backend can replace it; this slice does not activate application lowering there:

1. **Input.** The simplified Lambda the legacy lowering receives: after
   `simplify_in_arena`, `add_flat_make_aliases` and
   `drop_toplevel_pure_sequence_heads`
   (`compile_deps_program_in_arena` (C:663)), imported into a fresh `Bir`
   (`bridge::import_lambda`, S2.2). Until S4 switches on, this is the only source of
   level L for the lowering, so both sides start from the same tree.

   The simplified cut can share source handles. `import_lambda` treats
   binder-free shared subtrees as occurrences, copying once per incoming edge,
   as the legacy lowering does. One memoized bottom-up pass establishes
   binder-freedom. The expansion is bounded to four times the reachable source
   nodes. A repeated subtree containing a binder returns
   `Unsupported("shared Lambda subtree with binder")`; exceeding the budget
   returns `Unsupported("shared Lambda expansion")`. These two bridge reasons
   are permitted for the `lower` stage and counted separately. Earlier stage
   baselines are unchanged. A concrete sharing producer is
   `lam_pass_lets_dce::LetsState::simplif`: its Var arm reuses the replacement
   handle installed by `simplif_alias`, demonstrated by the bridge regression
   `simplify_lets_creates_shared_constant_occurrences`.

   A static-catch label is itself a binder, including catches without handler
   parameters. Shared catches therefore use the binder fallback; labels are
   never freshened per occurrence. This also covers distinct rebuilt catch
   nodes that retain the same label identity. The lower-stage report separately counts
   units blocked only by shared catch labels, in addition to the total binder
   fallback count. A catch-only share above 5% of a corpus is reported prominently.
2. **New side.** Lower to J; export the J program, not flattened, to a
   `JsArena` with plain constructors (`bridge_j::export_js`, added in S3.1a: no
   smart constructor, no `normalize`). The flattening of 1.3 is the legacy
   pass 1 of the shared tail until S3.2 replaces it. Variables the lowering created get
   identifiers whose stamps follow their `order`, above every stamp of the
   unit.
3. **Legacy side.** `compile_expr` on the same Lambda, as today.
4. **Shared tail.** Both `JsArena` programs then go through the same legacy
   code: export extraction and coercion (8.2), the six JS passes (A.6), and
   the legacy printer (`print_deps_program_with_directives_and_options`),
   ES module format, no source map.
5. **Compare** two texts per unit, byte for byte:
   - `lower`: printed **before** the JS passes, straight after coercion. This
     is the legacy JS IR "at the same point"; the passes are not run, so
     every declaration prints;
   - `lower+passes`: printed after the passes. This catches J data the first
     text does not show and the passes or the printer read: call information,
     declaration kinds, `is_unit`, mutability flags, field positions,
     comments.

   A difference is an error naming the unit, which of the two texts, and the
   first differing line. With source maps on, the mapping sequences of the two
   sides are compared as well (E.8).
6. **`Unsupported(reason)`** is returned by the lowering at the first
   construct it has no rule for; the unit then counts as a fallback with that
   reason. Reasons are static strings; each slice below lists the reasons it
   removes. `compiler-rust/tests/backend_coverage.txt` gets the stage `lower`
   and `scripts/test_backend_coverage.py` gets it in `STAGES`: the number of
   fallbacks and each reason's count must not grow, and each slice lowers
   them.

Text through the legacy printer is the comparison because it is total (it
prints every J node the legacy code can build), it is what the passes'
consumers see, and it ignores identifier stamps except through the name
choices of A.7. A structural comparison of two `JsArena`s would also compare
stamps and list layout, which are not required to agree.

Before S3.2 exists, the six JS passes of step 4 are the legacy ones on both
sides, so S3.3 to S3.9 do not depend on S3.2 being finished: only on S3.1's
emit not being involved. (H.1 orders S3.3 after S3.2; with this gate they can
proceed in parallel. Section 9.)

When legacy Rust and OCaml disagree on a case the gate reports, the legacy
code is fixed first, in its own pull request with a parity fixture; the
lowering is never made to differ from its oracle.

### 8.2 Exports

Export extraction and coercion are not lowering of a construct: they run
after `compile_expr`, on the JS IR
(`extract_toplevel_exports` (O:209), `coerce_toplevel_exports_with_name_reservations` (C:987),
`resolve_export_aliases` (O:30), and helpers in `js_shake.rs`), and the gate
shares them (8.1 step 4). H.1 puts "exports and their coercion" in S3.3; with
the shared tail they need no port for S3.3 to S3.9 to be checked. The port to
`Bir` is its own slice, S3.9b below, and it is the last one, because
`RESCRIPT_BACKEND=new` can emit from `Bir` only when it exists.

What the lowering must provide for the shared tail: the unit's last value is
the export block (`Pmakeblock(ModuleExport)`), lowered in **V**, so that
`extract_toplevel_exports` finds it as today; and the `finished` flag of the
unit's output (a unit that always throws, C:774-807).

### 8.3 The slices

Every slice: files under `compiler-rust/src/bir/lower/`; gate 8.1 on the
runtime library, `tests/tests` and the parity fixtures, with the fallback
counts of its reasons at zero; `cargo test` with the step-count tests of 7.4;
a test per rule in the form of C.7 step 8 (the same Lambda to the legacy
function and to the new one, the two printed texts compared); no change to
which JavaScript is emitted in the default mode; the instruction-count check
(dormant code, H).

| Slice | Constructs and contexts | Files | Removes the reasons | Size (lines) | Depends on | Reviewer |
| --- | --- | --- | --- | ---: | --- | --- |
| S3.3 | `Cx`, `Out`, the statement stack, `probe`/`realize` (1.2 to 1.5). `Var`, `Global`, `Const`; `Fun` not bound by `LetRec`; `Let`; `Seq`; `If` (3.6, all rows); the short circuits; `Apply` with a local or cross-module callee, sequencing, call form by status and by the other module's arity; `Prim` of the groups of 3.5 from "Lengths" to "Control" except `PrecordRest`; the top-level spine. All of **V**, **E**, **D**, **A**, **R**. The J flags of 7.1. `bridge::export_js`, the `lower` stage, the ratchet | `mod.rs`, `out.rs`, `expr.rs`, `cond.rs`, `call.rs`, `args.rs`, `prim.rs`, `konst.rs`, `unit.rs`; `bir/bridge.rs`, `bir/shadow.rs`, `scripts/test_backend_coverage.py` | none: it introduces `"switch"`, `"string switch"`, `"static catch"`, `"let rec"`, `"loop"`, `"try"`, `"assign"`, `"external"`, `"jsx"`, `"import"`, `"await"`, `"record copy"`, `"record rest"`, `"cross-module inline"` | 4,500 | S2.2 | strong for `cond.rs` (3.6) and `args.rs` (3.3); the rest is arm-by-arm |
| S3.4 | `Switch`, `StrSwitch` in every continuation: integer, string, named variant, untagged (3.9); `switch_depth` | `switch.rs`, `variant.rs`, `untagged.rs` | `"switch"`, `"string switch"` | 3,000 | S3.3 | normal; the forms are many but each is a port of one function of V |
| S3.5 | `Catch`, `Exit` (section 4); `HAS_EXIT`; `in_catch` | `exit.rs` | `"static catch"` | 1,200 | S3.4 (the dispatch is a switch; most catches hold one) | **strongest**. The legacy choice (row K14) and the design (4.1) are different programs that must agree; every difference has to be classified as a defect of the new code or of the legacy code |
| S3.6 | `LetRec` whose members are all functions; self tail calls (5.1); `Value(Return)` | `rec.rs`, `tail.rs` | `"let rec"` for function groups | 1,000 | S3.5 (a self call in a handler, a catch in a loop function) | **strong**: Q3 and Q5 surface here |
| S3.7 | `While`, `For`, `ForOf`, `ForAwaitOf`, `Break`, `Continue`, loop frames and label numbers (4.5); `Assign`; `Try`, `TryFinally`, `Ret::InTry` (5.5); `LetRec` with value members (5.3) | `loops.rs`, `label.rs`, `try_.rs`, `rec.rs` | `"loop"`, `"try"`, `"assign"`, the rest of `"let rec"`; introduces and then removes `"loop label under a re-lowered conditional"` | 2,500 | S3.4 (`switch_depth`), S3.6 | **strong** for `label.rs` only (4.5, Q2) |
| S3.8 | Externals: `PjsCall`, `PjsApply`, `PjsObjectCreate`, `PjsObjectGet`, `PjsObjectSet`, `PjsFnMethod`; argument holding and assembly; external module identifiers; the cross-module inline attempt (3.3) | `external.rs`, `ffi_args.rs` | `"external"`, `"cross-module inline"` | 3,000 | S3.3 | normal; needs its own table of X's functions first (below) |
| S3.9 | `Pjsx`; `Pimport` and awaited units; `Pawait`; the record copy (3.4) and `PrecordRest`; the flat `make` read | `jsx.rs`, `import.rs`, `record.rs` | `"jsx"`, `"import"`, `"await"`, `"record copy"`, `"record rest"` | 1,500 | S3.3 | normal |
| S3.9b | Export extraction and coercion on J-level `Bir` (8.2) | `export.rs` | none: it lets `New` emit from `Bir` | 1,500 | S3.2, S3.9 | strong: `lam_coercion.rs` and the tail-move helpers of `js_shake.rs` decide names and statement order |

Order: S3.3, then S3.4, S3.5, S3.6, S3.7 in sequence; S3.8 and S3.9 in
parallel with them once S3.3 has landed; S3.9b last. S3.10 (H.1) follows.

Which units each slice unlocks is not known; a unit is supported only when
every construct in it is, and most units have a switch. The histogram of
reasons that S3.3 writes is the measurement, and the first thing its pull
request reports (Q8).

What a slice is given. The author gets this document, the rows of section 3
or 4 or 5 for the constructs, and the legacy functions of the rows of section
2. For each construct the work is: write the arm for `Cx`, cite the legacy
functions, add the rule test, remove the reason. A difference under the gate
that the author cannot explain from this document is reported, not worked
around.

S3.8 is the one slice this document does not specify to the level of the
others: section 3.5 lists the external primitives and row H14 the functions
(58 names in X), but the argument assembly (`assemble_external_args` (X:959),
`lower_external_arg_values_and_effect` (X:782), `hold_external_args` (X:254)) was read
for its order only. Whoever starts S3.8 writes that table first, in the form
of 3.5 (Q9).

## 9. Corrections to BACKEND_REDESIGN.md

Where the code disagrees with the design document. Each is also applied
there, in the section named.

**A.5**

1. "One function per context", with five named: there are seven families
   (rows K1 to K7 of section 2), three state stacks for exits and four more
   pieces of context state (rows K8 to K11). `Compiled` is returned by two of
   the families (K1 and K2).
2. "Static catch: inline handler, fallthrough, or an `exit` variable": the
   inline form (`with_static_handler` (C:6075)) is entered only when the body
   contains no exit to the label (C:3167), so the handler substitution
   of `resolve_static_raise` (C:6113) does not run for a well-formed catch. There
   are two forms, as in OCaml (4.1; Q1).
3. "Loops, labels (`loop_N`, numbered per top-level group)": the number also
   counts lowerings whose output is discarded (4.5, tested), and a labelled
   `break` is emitted inside any L switch, also one printed as `if`
   statements (4.4, tested).
4. "Order dependence: temporaries and `exit` identifiers are created in
   traversal order": the traversal lowers the branches of a conditional two
   or three times (3.6) and a recursive function up to twice (5.1); "order"
   is that of the pass whose output is kept (3.8). OCaml and the legacy code
   already differ in identifier numbers (OCaml creates `exit` for the cheap
   form and lowers a switch's default before its cases); neither is visible.
5. "Folding in JS smart constructors": two different purity predicates are
   in use (`expression_has_no_side_effects` (B:102) and
   `js_expr_no_side_effects` (E:15); section 6), and the lowering builds some
   nodes plainly so that a rule does not fire (section 6.3).
6. The files of A.5 are about 16,000 lines, not 15,000 (C 7,938, V 1,948, X
   1,452, U 1,302, P 1,042, E 895, A 587, O 417, K 274, S 85).

**A.7 and E.3**

7. "Point (c) is the only place where stamp order reaches the output": the
   declarations `let x = _x` at the top of a tail-call loop are ordered by
   the parameters' identifiers, stamp first (`ext_ident_cmp` (C:6854), C:4043;
   5.1). Parameters of one function are created together, so the key in `Bir`
   is `order`; the measurement E.3 asks for should count this site too.

**B.3**

8. The continuation is `Effect(tail)`, `Value(tail)`, `Declare`, `Assign`,
   where the tail is "not tail", "return in a try body", or "return, with the
   function's loop record and the `in_catch` bit" (1.2). B.3 lists four
   continuations and "a tail flag with the enclosing tail-loop state", which
   omits `Value` in tail position, the try case and `in_catch`; without
   `in_catch` the form of a static catch cannot be decided without walking
   (row K14).
9. The `TAIL` flag and `FuncHeader::SELF_TAILCALL` are not needed by the
   lowering: OCaml's `triggered` protocol decides after one lowering (5.1).
   As built, `mark_tail_positions` (D:729) and `tail_child` (D:777) also disagree
   with the legacy rule: they do not follow the right operand of `&&`/`||` or a `Try`
   handler (the legacy code and OCaml do; tested, 5.2), and they treat a
   function bound by `Let` as able to call itself. The flags should be
   removed or left unused; they must not be read by S3.6. (Removed since,
   with `mark_tail_positions` and `tail_child`: #198.)
10. "A J statement list is a `ListId`": lowering needs block statements as
    real nodes until a unit is done (1.3), and builds lists through a stack.
11. The J opcode list omits kinds the legacy IR has. `bir/node.rs` already
    defines `JFlatCall`, `JJson` and `JRecordRest`; the block tag read
    (`ExprKind::CamlBlockTag`) and the interpolated template
    (`ExprKind::InterpolatedTemplate`, beside the plain template literal) have
    no opcode by name in either. S3.2's import decides their encoding.
12. "Loops ... labels are assigned by lowering (`loop_N`, counter reset per
    top-level group)": see correction 3.

**C.2 and C.4**

13. Row 10, "P for flatten: it is a normalising rule (statement lists are
    built flat)", and C.4's "`flatten_block`: flat statement lists by
    construction": not while lowering. Rules 5 and 6 of J-S3 build blocks
    that later rules must not see through (1.3, section 6.2). Flattening is
    one rule applied when a unit's lowering is done.
14. Row 11, "Lowering is one recursive walk in today's order": it is one
    walk; "today's order" is the kept pass (correction 4), and label numbers
    need the schedule of 4.5.

**H.1**

15. S3.3 "needs a table": this document. Its file list gains `out.rs`,
    `cond.rs`, `args.rs`, `unit.rs`, `bir/bridge.rs` (`export_js`) and the
    coverage script; "exports and their coercion" moves to S3.9b (8.2);
    size 4,500.
16. S3.3 does not depend on S3.2 for its gate (8.1): the legacy JS passes
    run on both sides. It depends on S2.2. S3.9b depends on S3.2.
17. "S3.4 to S3.9: switches and variants; static catch and exits; tail
    loops; loops, `try`, `let rec`; externals and FFI arguments; JSX, record
    spread, `await`, dynamic import": `let rec` of functions belongs with
    tail loops (every function member goes through 5.1), and `Assign` with
    loops. The table of 8.3 replaces the row.
18. S3.2 "fed by importing the JS IR before the JS passes": `import_js` was
    not built (`bir/bridge.rs` returns `Unsupported("JS arena import not
    implemented")`); S3.3 adds the opposite direction, `export_js`. Both
    directions now exist in `bir/bridge_j.rs` (#167); the stub in
    `bir/bridge.rs` is still there.

## 10. Open questions

Each with the experiment that settles it; resolved rows retain their measured result.

| # | Question | Experiment |
| --- | --- | --- |
| Q1 | **Measured by S3.5: never.** A counter at the two entries of `with_static_handler` stayed at zero over the runtime library, Belt, `tests/tests` (736 modules) and a 3,735-module application. The legacy path remains until the legacy lowering is deleted; the new lowering has no counterpart (4.1). Original question: is the handler substitution of row K15 (`resolve_static_raise` (C:6113), `compile_hoisted_static_raise_chain_return_tail` (C:3932)) ever executed? By reading it needs a catch whose body has no exit to its label, which `simplify_exits` removes | count its successful returns in a `Check` build over the three in-repository corpora and the application; zero closes the row |
| Q2 | **Resolved and implemented:** symbolic scheduling matches 512 generated shapes; real-switch conditional probes consume discarded labels, including self-tail-call branches (4.5) | OCaml/Rust parity: `tests/tests/src/lowering_conditional_loop.res` and its `.mjs`; corrected switch-context entry and value-probe order. Reference: `compiler/core/lam_compile.ml:793,1636-1644,2086-2118` |
| Q3 (resolved) | Yes: `(if c unit unit)` in a unit-returning function. R5 drops the pure test and emits no statements; R6 emits `return;`, which exits the enclosing loop. Both rules are required. | `tail_conditional_oracle_tests::q3_unit_conditional_distinguishes_return_rows` compares the same raw Lambda under both legacy rows; `lower::tail::tests::q3_unit_branch_must_return_from_the_loop` compares the enclosing recursive function with the new lowering. 192 generated loop-conditional shapes compare new and legacy J in five continuations and both probe modes. |
| Q4 | Is a `LetRec` reachable in the continuations where the legacy code lowers its body as a value (K2, K4, K5, K7; 3.4)? | count in a `Check` build; if reachable, compile one such unit with OCaml |
| Q5 | **Resolved:** the self call after nested `let rec` is a loop jump; the enclosing `Tail_with_name` return label survives the nested bindings (5.1) | OCaml/Rust parity: `tests/tests/src/lowering_nested_rec.res` and its `.mjs`, with and without capture; corrected the precheck and tail-loop body lowering. Reference: `compiler/core/lam_compile.ml:525-568,1745-1752,2046-2057` |
| Q6 | Does the cross-module inline attempt in the lowering (3.3) fire after the three inlining rounds? | count with cross-module inlining on, over a corpus built that way |
| Q7 | Is pairwise grouping of switch cases (7.3) ever a measurable cost? | the comparison count per corpus, reported by S3.4; a cached structural hash only if it is above 1% of lowering |
| Q8 | How many units does each slice unlock? | the reason histogram of S3.3's first `Check` run |
| Q9 | The exact order and holding rules of external arguments (S3.8) | the table S3.8 writes first, from X |
| Q10 | Termination measures for J-E7 and J-S3 (section 6) | S3.2 |
| Q11 | Whether invariant P1 (1.5) holds for every construct: `probe` then `realize` equals a direct lowering | the debug assertion, on from S3.3 |

### S3.6 measured lowering work

The S3.6 cost tests count source entries and tail-loop work independently:

| Shape | Source entries | Sequenced tail operands | Parameters | Body statements moved |
| --- | ---: | ---: | ---: | ---: |
| 10,000 distinct switch cases, each a self tail call | 30,005 | 20,000 | 1 | 1 |
| Same switch, each recursive call an argument of another call | 50,005 | 0 | 0 | 0 |
| 10,000 recursive function members without tail calls | 20,002 | 0 | 0 | 0 |
| One self call exchanging 10,000 parameters | 10,005 | 10,001 | 10,000 | 10,001 |

Both switch functions are lowered once; the second creates no loop record.
The 10,000-parameter case takes 9,999 sort comparisons and emits each alias
and assignment once.
Construction of 10,001 tail candidates takes 780,060 arena visits, including
all ordinary node construction facts. The two endpoint and candidate-cell
representations are each 8 bytes; the recursive group and loop frame are each
16 bytes. Loop headers use a pooled parameter-reference run because a mix of
unchanged parameters and lazily created copies is not a contiguous VarId run.

The default compiler still uses the legacy backend; this slice itself saves
nothing on that path. The separate short-circuit correction changes default
JavaScript only where the old loop probe differed from the OCaml reference.
