# Three trees plus the type graph

Status: design. No production code changes with this
document. T1, T2 and T7 have been implemented since ([STATUS.md](STATUS.md)).
It answers six questions from the code and one profile, states how
many intermediate representations a batch build needs, and re-cuts the work
that is in flight.

Conventions.

- Code is cited by file and function under `compiler-rust/src/` (and
  `rewatch/src/` where said), never by line.
- "Measured" is a number from the profile of section 6 or from a document
  cited by name. "Extrapolated" is arithmetic on measured numbers. "Read" is a
  claim from reading the cited code. "Tested" means the compiler of trunk
  `aa6ea01f5` was run on a small file while writing this and the output is
  quoted.
- The contract is unchanged: the generated JavaScript is the reference
  compiler's, and the same programs are accepted, rejected and reported. No
  intermediate tree has to match the reference compiler's.
- Related documents: [FRONTEND_REWRITES.md](FRONTEND_REWRITES.md),
  [CHECKER_REDESIGN.md](CHECKER_REDESIGN.md) (section K),
  [BACKEND_REDESIGN.md](BACKEND_REDESIGN.md),
  [BACKEND_LOWERING.md](BACKEND_LOWERING.md). [PRINTER_INSTRUCTIONS.md](PRINTER_INSTRUCTIONS.md) arrived with pull request
  #175 and is quoted from there.

## 0. Summary

**The answer is three trees**: the syntax tree, one core IR (`Bir` at level
L), and the oxc JavaScript tree. Beside them: the type graph, the checker's
results as tables indexed by syntax node, and the lowering's statement stack.
None of those three is a tree that a pass walks.

Today a module is materialised six times (seven with the oxc printer): the
parse tree, the rebuilt spine of it that the built-in rewrites produce, the
typed tree, raw Lambda, Lambda, the JS IR, and the oxc tree. The backend
documents as written end at five (syntax, typed tree, `Bir`, a JS-level
dialect of `Bir`, oxc).

| Question | Verdict |
| --- | --- |
| Q1. Can the four JS-level rounds be decided before or during lowering? | **Yes, with this condition:** three of them are decided when the lowering closes a scope, not when it writes a statement, because they read use counts that JavaScript-level folding changes (tested, 1.1). The fourth (removal of unused top-level declarations) stays as one filter over a table of top-level declarations with their references. No round needs a tree |
| Q2. Can names be chosen while lowering creates scopes? | **No at creation, yes at close.** A function's names depend on its final free variables and on which declarations survive. They can be assigned when the scope closes, from a log of naming events the lowering writes, without walking the finished tree |
| Q3. Can the lowering write oxc nodes directly? | **Yes, with this condition:** through a thin builder of our own whose storage is oxc nodes. The facts the normalising rules read (purity flags, block shape, call information) live in the builder's handle and in a dense table indexed by oxc's `node_id`; detaching a child is a 16-byte move |
| Q4. Can side tables replace the typed tree for every reader? | **Yes, with this condition:** in a batch build. Patterns keep a pool (the match compiler and the exhaustiveness check build patterns that have no syntax node). Editor tooling reads the typed tree today and keeps doing so until it is ported; builds write no `.cmt` file today |
| Q5. What does typed-tree construction cost? | **1.28% of the build measured** for the mechanisms the method can see (pool pushes, moves of owned nodes, the arena's drop, clones); reading it back through accessors is 0.12%. The cost of filling a node inside the checker's own code is not separable by this method |
| Q6. Where do the built-in rewrites go? | **Yes, with this condition:** no rewrite moves to the parser (the formatter would see it). Rewrites are either typed directly where the node is consumed, or recorded as an expansion (a few appended nodes and one entry in a sparse table read at the consumption point). The three validation walks stay as read-only walks of the tree as written |

Saving, in percent of a clean build of `tests/tests` (section 9): **3.9% to
6.9%** against today from the changes that are new in this document (no
rebuilt parse spine, no typed tree in a batch build, unit reads without a
walk, printing through oxc without a naming pass), on top of the 8.5% to
11.9% that the level L rounds, the conversion and the lowering already plan
for. Whole pipeline against today: **12.4% to 18.8%**, all of it
extrapolated from measured costs. Against the five-tree plan as pull request
#175 measured it, this plan also avoids 2.8% to 3.1% of measured cost (the
naming pass and the adapter of the JS-level dialect).

The typed tree is the weakest of the three removals: its measured cost is
1.3%, and the readers that must be ported are 35,000 lines. It is last in the
order, and the plan is valid if it stops at four trees.

## 1. Q1: the four JS-level rounds

The rounds are today's passes 3 to 6 of `LambdaCompiler::
compile_deps_program_with_lower_check` (`lambda/lam_compile.rs`), in
BACKEND_REDESIGN C.3 the rounds J1 to J4. Self cost of the pass files in the
profile of section 6: `js_pass_flatten_and_mark_dead.rs` 30.4 M,
`js_shake.rs` 20.8 M, `js_pass_tailcall_inline.rs` 6.4 M,
`js_pass_record_rest.rs` 0.04 M, and `js_ir/walk.rs` (the visitors they and
the shadow renaming use) 49.7 M: 107 M, 2.5% of the build, not counting the
allocator.

### 1.1 J1: tail-call inlining

- **Code.** `tailcall_inline_program`, `TailcallInlineState::{new,
  transform_statement, try_inline_single_return_statement, inline_named_call,
  inline_function_call}`, `inline_tailcall_call`, `SubstituteInline`
  (`lambda/js_pass_tailcall_inline.rs`).
- **Reads.** (a) The number of `Var` occurrences of every local in the whole
  JS program before the pass (`UseCounts`); (b) whether a declaration's value
  is strictly pure (`js_expr_no_side_effects`); (c) the export set; (d) the
  set of functions called by the final `return f(...)` of some block
  (`collect_tail_callees`); (e) at the site: the last statement of a block is
  `return f(args)`, `f` is a variable with status `OncePure` bound by a
  lexical `let` to a function literal that is not a method, not `async` and
  has no directive, with as many parameters as arguments, and the site is not
  inside `f`'s own initialiser (`active_decls`); (f) whether the body assigns
  a parameter (`immutable_param_mask`).
- **Writes.** The callee's body in place of the `return`, with each
  unassigned parameter renamed to its argument variable or replaced by a
  substitutable constant (and conditionals on such a constant pruned,
  `substituted_truth`), the other parameters declared as `let p = arg`. The
  declaration of `f` becomes `DeadPure`. Every declaration gets its status
  (`DeadPure`, `DeadNonPure`, `OncePure`, `Used`, `Exported`), which rounds J3
  and J4 and the printer read.
- **When the information first exists.** (e) and (f) when the site is
  lowered. (a) only when the scope that declares `f` is completely lowered:
  the count is of JavaScript occurrences, and the J normalising rules drop
  occurrences that level L still has.
- **Smallest example where deciding earlier differs** (tested):

  ```rescript
  @val external big: (int, int) => int = "big"
  let f = (a, b) => {
    let g = x => big(big(x, a), big(a, big(x, big(a, x))))
    if Array.length([1, 2]) > 1 { g(b) } else { g(a) }
  }
  ```

  emits `function f(a, b) { return big(big(b, a), big(a, big(b, big(a, b)))); }`.
  Level L has two uses of `g`. The length of the literal and the comparison
  are folded by the J constructors (rows J-E2 and J-E4 of BACKEND_LOWERING 6,
  `build::exp::length` and `fold_int_comparison`; level L has no rule for
  `Array.length`), rule 1 of J-S3 keeps one branch, the JavaScript count of
  `g` is one, and the pass inlines it. With `if c { g(b) } else { g(a) }` the
  output keeps `let g = ...` and two `return g(...)`. A decision on level L
  counts would keep `g` in the first program too.
- **Verdict: yes, with this condition.** The decision is made by the lowering
  at the close of the scope that declares `f`, not at the `return`. What the
  lowering maintains: a JavaScript use count per variable (incremented when a
  `Var` node is built, decremented when a normalising rule or the sequencing
  of arguments releases one; `Bir`'s `uses` already works this way at level
  L), and per function scope a list of candidate sites (statement-stack slot
  of a final `return f(args)`, with `f`). At scope close a candidate whose
  callee has count one is spliced. The splice substitutes parameters in the
  callee's built body, which is a rewrite of built JavaScript bounded by the
  inlined bodies (each function body is inlined at most once, so the total is
  linear). It needs no pass over the unit and no tree beside the statement
  stack. If the Check gate shows that the level L count decides the same on
  every corpus unit, the simpler form (lower the callee's body at the site
  with parameters bound to the arguments, no rewrite at all) replaces it; that
  count is not measured (section 12).

### 1.2 J2: record rest

- **Code.** `apply_js_record_rest_pass`, `RecordRest::block_items`,
  `materialize_fields`, `replace_source_fields`, `map_statement`
  (`lambda/js_pass_record_rest.rs`). Skipped unless the program contains a
  `RecordRest` expression (`RecordRestFinder`).
- **Reads.** A declaration `let rest = <record rest of source>` or a `return`
  of one, and the statements after it in the same block: every `source.label`
  for an excluded label, found only through the statement kinds block,
  declaration, expression and return and through the expression kinds
  `map_statement` descends into (not into `if`, loops or function bodies).
- **Writes.** The destructuring pattern. A following `let x = source.label`
  is deleted and `x` becomes the pattern's binder; other reads become a fresh
  identifier named by `field_ident_name`; labels never read get `__unused<i>`.
- **When the information first exists.** When the rest of the block is
  lowered: the pattern depends on statements written after it.
- **Smallest example:** `let {a, ...rest} = r; use(r.a)` emits one pattern
  `{a: a, ...rest}` whose binder is the identifier of the later read. Writing
  the pattern when the declaration is lowered would bind `__unused0` and keep
  the read.
- **Verdict: yes, with this condition.** It is decided at the close of the
  block. The lowering reserves the declaration's slot on the statement stack
  (`StatementStack::reserve` and `fill` exist, `bir/lower/out.rs`), and at
  block close runs `replace_source_fields` over the slice of the stack after
  the slot, then fills it. Structure needed: the slice of the statement
  stack. It runs only in blocks that have a record rest.

### 1.3 J3: block-field substitution and dead marks

- **Code.** `Substitute::{statement, expression,
  try_substitute_caml_block_projection, substituted_caml_block_item}`,
  `should_materialize_block_binding_items`, `mark_dead_code`,
  `collect_mark_dead_states_*`, `apply_mark_dead_states_*`
  (`lambda/js_pass_flatten_and_mark_dead.rs`).
- **Reads.** A lexical declaration whose value is an immutable block literal
  with two or more fields; the status J1 gave it (a dead one is dropped or
  becomes an expression statement and is not materialised); whether each
  field is "simple" (`is_simple_block_binding_item`); later `x[i]` and
  `x.field` reads of that variable. Then, for the dead marks, one more count:
  a declaration is used when an occurrence follows it or precedes it
  (`MarkDeadInfo::Recursive`), where occurrences inside declarations already
  dead do not count. One level: there is no cascade.
- **Writes.** Non-simple fields hoisted into fresh locals `x_0`, `x_1`
  (`block_substitution_name`) declared before `x`; a field read replaced by
  the field's value when that is simple; statuses, which the printer uses to
  omit a declaration (`statement_desc_prints_anything`, `js_ir/printer.rs`).
- **When the information first exists.** The shape of the literal and the
  hoisting: when the declaration is lowered. The substitution: when the read
  is lowered, which is after the declaration in statement order (the pass
  fills its map in statement order too, `Substitute.substitution`). Whether
  the declaration survives: at scope close.
- **Smallest example** (tested): `let h = a => { let p = (ext(a), ext(a +
  1)); let (x, y) = p; x + y }` emits `let p_0 = ext(a); let p_1 = ext(a + 1
  | 0); return p_0 + p_1 | 0;`. The declaration of `p` is gone because every
  read was substituted. The hoisting is decided at the declaration, the
  removal only after the last read.
- **Verdict: yes, with this condition.** Hoisting and substitution happen
  while lowering (`Cont::Declare` with a block literal records the fields as a
  fact of the variable; lowering a field read of a variable with that fact
  returns the field). Removal of declarations with no remaining use happens
  when the scope's statements are copied from the stack to their list, which
  is the one copy BACKEND_LOWERING 7.2 already allows. The condition is the
  same count as J1: the pass decides "materialise or not" from the count
  before substitution and "dead or not" from the count after it, so the
  lowering keeps both (occurrences built, occurrences remaining).

### 1.4 J4: removal of unused top-level declarations

- **Code.** `shake_program`, `flatten_toplevel_block`, `live_idents`,
  `free_variables_of_expression`, `js_statement_no_side_effects`
  (`lambda/js_shake.rs`); the export tail moves in the same file
  (`move_same_name_export_alias_to_export_tail` and helpers) run earlier,
  from export coercion.
- **Reads.** The flattened top-level statement list; the export set; for each
  top-level declaration the free variables of its initialiser and whether it
  is strictly pure; for other statements whether they have an effect and
  their free variables. Liveness is reachability from the exports and from
  effectful statements through initialisers, by a worklist.
- **When the information first exists.** At the end of the unit: a
  declaration is needed by statements written after it.
- **Smallest example:** `let rec f = () => g() and g = () => f()`, neither
  exported nor called. Both are removed. A use count never reaches zero for
  them, so "`uses == 0`, cascade through `release`" (BACKEND_REDESIGN C.3,
  row J4) would keep both; the code disagrees with that row (section 13).
- **Verdict: no, it stays, as a filter.** Minimal structure: the vector of
  top-level statements (the lowering builds it anyway, it becomes the body of
  oxc's `Program`), and one row per top-level declaration: variable, strictly
  pure or not, and the list of top-level variables its initialiser refers to.
  The lowering appends to that list whenever it builds a `Var` node of a
  top-level variable while it is inside top-level statement `i`. At the end:
  the worklist of `live_idents` over the rows, then the statements that are
  not live are not pushed. No statement is walked.

### 1.5 What the lowering must keep to write final statements

| Structure | Size | Used by |
| --- | --- | --- |
| JavaScript use count per variable: built and remaining | two `u32` per variable | J1, J3, dead declarations |
| Block-literal fact per variable | one handle | J3 |
| Candidate `return f(args)` sites per function scope | one slot index and a variable each | J1 |
| Reserved slot of a record-rest declaration | one slot index per block that has one | J2 |
| Top-level rows: purity, references | one row per top-level statement | J4 |

The statement stack is the only place where already written statements are
revisited, at the close of the scope that owns them.

## 2. Q2: names

- **Code.** The legacy rule is `NameScope`, `add_ident`, `ident_name`,
  `with_reserved_ident_scope`, `function_reserved_idents`,
  `reserve_idents_in_current_scope`, `reserve_js_names`, `fresh_scoped_name`
  (`js_ir/printer.rs`). `emit/naming.rs` (`Names`, `Scope`, `Group`) is the
  same rule as a pass over the JS IR; its header states the rule in full and
  is the reference for what follows.
- **What the rule reads.** (1) Print order: an identifier is named the first
  time it is printed in a scope; the first with a base name gets the base,
  later ones `base$1`, `base$2`, skipping names used in the scope and, for
  suffixed names, raw JavaScript names of the program. (2) Scopes are the
  program and functions only; blocks, loops and catch clauses continue their
  scope. (3) At a function: its free identifiers plus its own binder, sorted
  by `Ident`'s order (stamp, then name), are named in the enclosing scope if
  they have no name yet; the new scope then inherits the suffix tables of
  exactly those bases, so a local may take the name of an outer variable the
  function does not capture. (4) Declarations and branches that are not
  printed assign no name, but their identifiers still count as free
  variables. (5) At the top: imports, then the reservations of export
  coercion, then statements, then exports.
- **Why names cannot be chosen when the scope is created.** Point (3) needs
  the function's free variables in the final JavaScript, and point (4) needs
  to know which declarations survive. Both are known when the function's body
  is lowered and its scope is closed (1.1, 1.3), and for the program when the
  unit is done (1.4).
- **Hardest example** (tested for the first two functions):

  ```rescript
  let y = ext(2)
  let k = a => { let y = ext(a); y + 1 }
  let k2 = a => { let y = ext(a) + y; y + 1 }
  ```

  emits `let y = ext(a)` in `k` and `let y$1 = ext(a) + y | 0` in `k2`. The
  local's name depends on whether the outer `y` is free in the function. Make
  the capture conditional on a branch that the J constructors fold away (the
  shape of 1.1) and the name depends on JavaScript-level folding inside the
  body. The second hard case is a top-level `let x = ...` that J4 removes
  followed by another `x`: the survivor prints as `x`, not `x$1` (read, from
  `statement_desc_prints_anything` and `flatten_toplevel_block`; all
  top-level values of a module without an interface are exported, so this
  needs an interface or a declaration the lowering created). The third is
  point (3): two identifiers with one base that are both first named by one
  function's reservation get `base` and `base$1` in stamp order
  (BACKEND_REDESIGN A.7 point (c)); in `Bir` the key is the variable's
  `order`.
- **What the lowering has to maintain.** Per function scope, in the order the
  statements end up in the final list:
  1. a log of naming events: `Declare(var)` (binder before initialiser, and
     for a function declaration that is not eta-reduced after the
     reservation), `Params(vars)`, `Enter(function)`, `Leave`, and for loops
     and catch clauses their binders before their bodies. A statement that is
     removed at scope close takes its events with it (events carry the
     statement-stack slot);
  2. the set of free variables of the function (outer variables with a
     remaining occurrence, including occurrences in statements that are not
     printed), kept as a list on the scope with one membership bit per
     variable;
  3. for the program: the import order and the reservations of export
     coercion.

  Order inside one expression matters only between `Enter` events (two
  function literals in one expression); it is the order of the final tree,
  which the builder knows when it attaches the literals to their parent.
- **Verdict: no for "while lowering creates scopes"; yes for "not in a pass
  over the finished tree".** Names are assigned at scope close by replaying
  the scope's log through the group and suffix tables of `emit/naming.rs`.
  Identifier nodes are written with a variable id and no final text:
  `oxc_codegen` already prints an identifier's name from a table when the
  node carries a symbol or reference id (`Codegen::with_scoping`,
  `get_binding_identifier_name`, `get_identifier_reference_name`), so the
  name table is filled at scope close and read by the printer. Pull request
  #175 measured naming as a separate pass at 56 M to 68 M instructions on
  `tests/tests`; the replay touches one event per declaration and function
  instead of every node. Its cost is not measured.

## 3. Q3: writing oxc nodes directly

What in the lowering re-reads or rewrites JavaScript it has already built:

| Site | Code | What it does to built nodes |
| --- | --- | --- |
| Expression constructors | `js_ir::build::exp::{string_append, length, is_null_or_undefined, bin, js_and, js_or, cond, not, simplify_and_, simplify_or_}`, rows J-E1 to J-E10 of BACKEND_LOWERING 6 | reads the kind of the operands and of their operands (`x && (x && r)`, `c2 ? a : b` under a `cond`), compares operands structurally (`ocaml_eq_expression`), reads purity, returns an operand or rebuilds a parent from parts |
| Statement constructors | `build::stmt::{exp, block, simplify_if, normalize, unnest_block}`, rows J-S1 to J-S5 | reads the last statement of a branch, compares blocks (`ocaml_eq_block`), merges two branches into one conditional expression |
| Integer and comparison helpers | `lambda/js_exp_make.rs`, rows J-M0 to J-M13 | reads literals and `>>> 0`, `\| 0` wrappers of operands and drops them; projects a field out of a pure literal |
| Argument sequencing | `State::evaluate_now` in `bir/lower/args.rs` (legacy `lam_compile_arguments.rs`) | detaches the two sides of a sequence, detaches the elements of a literal and rebuilds it, wraps a value in `let tmp = value` |
| Probing | `StatementStack::{probe, realize}` (`bir/lower/out.rs`) | holds an output that is not yet committed |
| Effect statements | `push_effect_expression`, `push_s_exp` (`lambda/lam_coercion.rs`) | splits a sequence into statements, drops pure parts |
| The rounds of section 1 | | substitute parameters in an inlined body (J1), replace field reads in the tail of a block (J2) |

What oxc's tree supports (read from `oxc_ast` and `oxc_allocator` 0.158):

- `Expression<'a>` is a 16-byte enum of arena boxes. Inspecting a child or a
  grandchild is a `match` by reference. Detaching a child is a move of those
  16 bytes; `Box::unbox` moves a node out of its box; a parent is rebuilt by
  one bump allocation. Nodes can be changed in place through `&mut` (the
  operator of a comparison for J-E8). Nothing is reference counted and nothing
  is dropped.
- Structural equality exists as a generated trait (`ContentEq`), but
  `ocaml_eq_expression` is deliberately partial (false for kinds outside a
  fixed set), so the builder needs its own.
- What oxc nodes do not carry: the flags `PURE`, `STRICT`, `DELAY_SAFE`,
  `J_SUBEXPR` (BACKEND_LOWERING 7.1, where `runs_no_code` is a predicate, not
  a flag), and the J-level meaning the printer
  turns into a shape: a block's tag and mutability, a record's field names, a
  call's arity information, `undefined` that is a unit, comments. The rules
  and the rounds read these (J3 needs "immutable block with these fields",
  J-M11 needs the field of a record literal by position).
- Every oxc node has a `node_id: Cell<NodeId>` that the printer does not read
  (read: `oxc_codegen` has no use of it). It can index a dense table.

**Verdict: yes, with this condition:** a thin builder of our own with oxc
nodes as its storage.

- A value in flight is a handle: the oxc `Expression` by value, its flags,
  and a small tag for its J-level kind. That is what constructors take and
  return, so operand flags cost nothing.
- Facts of nodes that are already inside a parent (read when a rule takes a
  node apart) are in a table indexed by `node_id`: flags and kind, 2 bytes a
  node, written when the handle is attached. Block shapes and call
  information are in a side pool the table points to, written only for
  blocks, calls and `undefined`.
- The printer decisions of BACKEND_REDESIGN A.7 that depend only on the node
  (`x == null` for the two strict tests, `-x`, property access with a dot,
  number spelling, block shapes) are made when the builder attaches the node.
  The decisions that depend on the finished function (a unit function drops
  its final `return`, eta reduction, arrow or `function`) are made when the
  function's scope closes.
- Garbage: a node a rule drops stays in the bump arena until the module is
  done. `tests/tests` built through oxc measured "AST construction / oxc
  arena" at 2.2 M to 2.3 M instructions (pull request #175), so this is
  bounded by a small number; it is not measured for the builder.

This removes the JS-level dialect of `Bir` and the adapter that pull request
#175 measured at 65 M instructions of "other emitter" work plus 298 M of
import on `tests/tests`.

## 4. Q4: who reads the typed tree

The typed tree is `types/typedtree.rs` stored in `TypedArena`
(`types/tast_arena.rs`): `Expression` and `Pattern` are 72 bytes each, with
the type (`exp_type`), an environment handle (`exp_env`, an `EnvRef`), a
location and a 56-byte description that holds resolved paths and shared
descriptions (`Arc<ValueDescription>`, `Arc<ConstructorDescription>`, label
descriptions).

| Reader | Code | Fields it reads | Can tables keyed by syntax node serve it | What is needed |
| --- | --- | --- | --- | --- |
| Translation to raw Lambda | `RawLambdaConverter::convert_structure_with_coercion` and the `convert_*` functions (`raw_lambda/convert.rs`, `convert/jsx.rs`), `raw_lambda/typeopt.rs` | every `ExpressionDesc` variant; `exp_type` and `exp_env` to expand types (13 environment uses); the resolved value description of an identifier (primitive or not); constructor and label descriptions; `Partial`; `fp_has_default`; module coercions | yes | per expression: type, environment handle, and one resolved-description handle (value, constructor or label, by node kind); per function parameter the default flag; per match the `Partial` flag; coercions per module expression. The shape comes from the syntax node |
| Match compilation | `raw_lambda/matching.rs`, `switch.rs` | typed patterns and their types and environments (27 environment uses), constructor descriptions, constants; it builds patterns of its own (`TPatIdx::overlay`, `PatArena::store_overlay`) | yes with a condition | patterns the checker normalises (or-patterns, records completed with their labels, aliases) and patterns that have no syntax node. Keep a pattern pool, or a view over syntax pattern plus table plus overlay (slice T10) |
| Exhaustiveness and unused cases | `types/parmatch.rs`, `typecore::parmatch_check_partial` | the same typed patterns | same as above | same pool or view |
| Unit reads for incremental builds | `unit_reads::{structure_reads, signature_reads}` through `TastIterator` | every resolved path and every type the tree carries | yes | the tables hold exactly those paths and types; or the checker logs a read where it resolves a path |
| genType | `gentype/translate_structure.rs`, `translate_signature.rs`, `translate_core_type.rs`, `annotation.rs`, `translate_type_declarations.rs` | structure and signature items, value bindings (pattern name, attributes, type), type declarations with their typed core types (resolved paths), module bindings, one environment use | yes | per core-type node the resolved path; per binding the type; the items come from the syntax tree, the signature from the published one |
| Unused-value and other late warnings | `types/usage.rs` (`UsedCell`, the delayed checks), `binary_ast::ppx::UnusedAttributeSweep` | none of the typed tree: usage flags are set at lookup, the sweep reads the parse tree | not a reader | nothing |
| Diagnostics | `types/printtyp.rs`, `driver/type_clash.rs` | types and environments, not tree nodes | not a reader | nothing |
| Dumps | `types/sexp_typedtree.rs` (`-dtypedtree`, the playground) | everything | yes | a dump of syntax node plus table row replaces it; it is a debugging aid, not compared with anything |
| Editor tooling | `analysis/process_cmt.rs`, `process_extra.rs`, `hover.rs` over `driver::ToolingTypedModule` (`typecheck_structure_for_tooling`, `typecheck_signature_for_tooling`), called from `rewatch/src/build/tooling.rs` | expressions, patterns, core types, module expressions with locations, types and resolved paths (65 match arms on typed nodes) | yes, later | it is a table walk by location in the end state. Until it is ported, a tooling session asks the checker for the tree as today |
| Dead-code analysis | `analysis/reanalyze` (OCaml), reads `.cmt` files | | no reader in `compiler-rust` | see below |

**The `.cmt` artifact.** Code and documents disagree. AGENTS.md says builds
write `.cmi`, `.cmt` and `.cmti` files. The code says they do not:
`rewatch/src/build/tooling.rs` ("Builds write no `.cmi`/`.cmt`/`.cmti`
files") and `rewatch/src/build/plan.rs`; `clean.rs` only removes such files.
Editor tooling runs inside the watch session and type-checks the named file
on demand. So the contract's "artifacts stay usable" is met today by checking
on demand, and the typed tree is built in a batch build for the Lambda
conversion, the unit reads and genType only. Nothing has to be written to
keep a `.cmt` usable, because none is written. If a file artifact is wanted
again (for the OCaml dead-code analysis), it is written lazily by the same
on-demand path, from the tables; that is outside this plan.

**Verdict: yes, with this condition.** Every reader of a batch build can be
served by the syntax tree plus dense tables. The conditions are the pattern
pool (kept until T10) and editor tooling (keeps the typed tree until T12).

The tables (one row per syntax node of the kind, indexed by the node's
handle, written by the checker where it writes the node today):

| Table | Row | Written by |
| --- | --- | --- |
| expression | type (`TypeExprRef`, 4 bytes), environment (`EnvRef`, 4 bytes), resolved description handle (4 bytes), flags (partial application, JSX, default) | `type_expect` and the functions it dispatches to |
| pattern | type, environment, resolved constructor or label handle | `type_pattern` |
| core type | type, resolved path handle | `transl_type` |
| module expression | module type handle, coercion handle | `type_module_expr` |
| cold | extras and attributes, sparse (today's `ExpCold`, `PatCold`) | as today |

That is 12 to 16 bytes a node against 72.

## 5. Q6: the built-in rewrites

Read first: where the "rewritten copy" is. (This paragraph describes the
mapper before T2; since #193 the expression mapper rebuilds no ancestor and
`rewrite_child` and `rewrite_expression_generic` are gone.) The mapper
(`ppx::rewrite_structure_with_warnings`, `rewrite_signature_with_warnings`)
takes `arena: &mut ParseArena` and appends to the same arena. The nodes as
parsed stay; what is new is every rewritten construct **and every ancestor of
one**, because a parent whose child handle changed is rebuilt
(`rewrite_child`, `rewrite_expression_generic`). FRONTEND_REWRITES counts
37,703 rebuilt nodes in 90,179 mapper entries on `tests/tests` after subtree
skipping. So the copy is a rebuilt spine in the same pool, not a second
arena; the task's wording and the code differ in that.

Destinations:

- **Parser: none.** The syntax tree is the one the formatter and editor
  tooling read. A rewrite at node completion (an integer without its `l`, an
  application instead of a pipe) would be printed back. FRONTEND_REWRITES
  lists the parser as a candidate for nine rows; with one tree for all
  readers that is withdrawn.
- **Direct:** the checker types the node as written by calling the rule of
  the construct it stands for, and the core IR builder converts it the same
  way. No node is created.
- **Expansion:** the desugared form is a few new nodes appended to the pool,
  referring to the original children by their handles, and one entry
  `original -> expanded` in a sparse table. A consumer looks the entry up
  only in the arm of a kind that can have one (one bit per expression in the
  packed table that already holds the two certificate bits,
  `ParseArena::expr_needs_no_rewrite`). No ancestor is rebuilt.
- **Declaration table:** the result is not a tree (an encoded primitive); it
  is stored per declaration.

| Rewrite (row of FRONTEND_REWRITES) | Destination | Notes |
| --- | --- | --- |
| External declarations: `@val`, `@module`, `@send`, ..., and argument and result annotations, `@obj` | declaration table, at the checker's declaration entry | `encode_external`, `build_external_decl`, `build_arg_type_specs`, `process_obj_type` keep their code and return a value instead of a rewritten declaration |
| Relative-path module external | expansion (structure item) | a constrained include |
| `@inline` constant binding, `@inline(value)` signature value | declaration table | the binding becomes an inline primitive |
| Integer with `l` suffix, expression and pattern | direct | checker and builder read the digits through one accessor |
| Pipe `a -> f` | expansion | needs a temporary binding in some shapes (`pipe_bound`, `fresh_bound_name`) |
| Single record or dictionary pattern `let` | direct | typed by the rule of a one-case match |
| `let?` | expansion | match with early return |
| Tuple binding with tuple right-hand side | expansion (binding group) | changes the number of bindings |
| Record pattern binding to a packed module | expansion | |
| Two unguarded `true`/`false` cases | direct | typed by the rule of `if`, arms in boolean order; diagnostics then use the `if` wording as today |
| `async` function, `await e` | direct | the checker applies the promise type; the builder emits the two primitives |
| Awaited module alias, local awaited module | expansion at the structure item | hoisted module type declarations, per-structure deduplication |
| `@this` function, `@this` on braces, `@this` arrow type | direct for the type; expansion for the function | |
| Object type field attributes | direct | the checker reads the attributes |
| `%raw`, `%ffi`, regexp literal, `%%raw` | expansion | a local external application; the JavaScript classification runs once, there |
| `%todo` | expansion | |
| Consecutive `%%private` items | expansion at the structure | local module and open |
| `@deriving(accessors)`, Spice derives | expansion at the type group | generated declarations are new items |
| JSX elements, fragments, components (`parser/jsx_ppx.rs`) | expansion | the same functions, called per element |
| Attribute and extension payloads | follows the construct inside | |

Core IR is the destination of nothing on its own: every rewrite has a typing
consequence, so the checker has to see it. "Direct" rows need a matching arm
in the builder.

What stays: the three validation walks (`check::Checker`, `NestedExternals`,
`UnusedAttributeSweep`). They decide which frontend diagnostics appear before
any type error, and FRONTEND_REWRITES argues why they are not merged. They
are read-only. The sweep runs on the rewritten tree today; it needs a
predicate "this attribute is consumed by a built-in" computed from the tree
as written, which is the same list `filter_ffi_attributes` and
`process_attributes_rev` apply.

**Verdict: yes, with this condition:** the mapper becomes an expansion pass
that appends only desugared constructs and records them; the validation walks
stay; the sweep gets the consumed predicate. The order of diagnostics is the
gate (`scripts/test_error_output_parity.sh`, the `super_errors` fixtures).

## 6. Q5: what typed-tree construction costs

**Method.** x86-64 Linux, 8 cores. Trunk `aa6ea01f5`. `rescript` built with
the release profile (fat LTO) and line tables
(`CARGO_PROFILE_RELEASE_DEBUG=1`), not the profile-guided build. One clean
build of `tests/tests` (725 modules) under `valgrind --tool=callgrind
--dump-instr=yes`, `RAYON_NUM_THREADS=1`, the runtime built first: 4,310.7 M
instructions. Attribution is per instruction address, as in CHECKER_REDESIGN
K.1: every address of the executable is resolved to its stack of inlined
frames (`llvm-symbolizer --inlines`); an address belongs to the first
mechanism any of its frames matches; an out-of-line call into the allocator
or `memcpy` is charged to the mechanism of the calling address. The three
scripts are under
[prototypes/typed-tree-attribution](prototypes/typed-tree-attribution)
(measurement prototypes, not reviewed code). One run; callgrind's count of
one executable moves by about 0.1% between runs.

**Phases, inclusive, same profile.**

| Phase | Function | Instructions | Share |
| --- | --- | ---: | ---: |
| Parsing | `parser::module::parse_structure` | 501.1 M | 11.62% |
| Built-in rewrites, implementations | `ppx::rewrite_structure_with_warnings` | 168.1 M | 3.90% |
| Built-in rewrites, interfaces | `ppx::rewrite_signature_with_warnings` | 9.8 M | 0.23% |
| Unused-attribute sweep | `ppx::collect_unused_attribute_warnings_structure` | 17.0 M | 0.39% |
| Type checking, implementations | `typemod::type_structure` | 1,474.4 M | 34.20% |
| of which exhaustiveness | `typecore::parmatch_check_partial` | 68.5 M | 1.59% |
| Type checking, interfaces | `driver::typecheck_preprocessed_signature_in_process` | 79.7 M | 1.85% |
| Publishing the signature | `driver::publish_signature` | 128.7 M | 2.99% |
| Unit reads, a walk of the typed tree | `unit_reads::structure_reads` | 49.9 M | 1.16% |
| Typed tree to raw Lambda, with match compilation | `RawLambdaConverter::convert_structure_with_coercion` | 239.0 M | 5.55% |
| Raw Lambda to Lambda | `raw_lambda/lower.rs` | 30.8 M | 0.72% |
| Lambda passes | `lam_compile_main::simplify_in_arena` | 243.3 M | 5.65% |
| Lowering and the six JS passes | the second closure of `compile_deps_program_with_lower_check` | 321.1 M | 7.45% |
| Printing | `driver::render_js_program` | 112.3 M | 2.60% |
| Freeing the typed tree | drop glue of `TypedArena` | 12.2 M | 0.28% |
| Freeing the parse tree | drop glue of `ParseArena` | 22.3 M | 0.52% |

**Typed-tree mechanisms.**

| Mechanism | Symbols | Instructions | Share of build |
| --- | --- | ---: | ---: |
| Pushing nodes and lists into the pools, with growth | `TypedArena::push_*`, `with_exp_attributes`, `with_pat_attributes`, `ListPool::push_iter`, the handle constructors; allocator 0.85 M and `memcpy` 0.66 M called from them | 13.3 M | 0.31% |
| Moving owned typed-tree values through generic code | library code instantiated over `typedtree` and `tast_arena` types by value: `Result<Expression, _>` branches, `ptr::write`, vectors and iterators of nodes | 28.4 M | 0.66% |
| Freeing the tree | drop glue of `TypedArena`, inclusive | 12.2 M | 0.28% |
| Cloning nodes | `Clone` of typed-tree types | 1.2 M | 0.03% |
| **Construction and destruction, sum** | | **55.0 M** | **1.28%** |
| Reading through the accessors | `TypedArena::{expr, pattern, expr_list, ...}`, `ListPool::get`, handle indexing | 5.35 M | 0.12% |
| Reader working sets | library code instantiated over references to typed-tree types (the match compiler's rows, 6.7 M of it in `matching.rs`) | 14.2 M | 0.33% |

Reads by owner: `unit_reads.rs` 1.58 M, `raw_lambda/convert.rs` 1.46 M, the
checker 0.86 M, `matching.rs` 0.64 M. So the conversion to raw Lambda spends
2.1 M of its 239 M (0.9%) on reaching typed-tree nodes; the rest is the
conversion itself, match compilation (`matching.rs` and `switch.rs`, 53.9 M
self) and type queries (`typeopt::is_base_type`, 26.2 M inclusive).

The construction sum is 3.7% of type checking. CHECKER_REDESIGN K.2 has
allocation and copying at about a third of the walk; typed-tree nodes are
about an eighth of that.

**What the method does not see.** Filling the 72 bytes of a node inside a
checker function (the fields are written by code that belongs to
`typecore.rs` and has no frame of a typed-tree mechanism), the reference
count of a shared description stored in a node, and the cache effect of
writing 72 bytes instead of 12. The 1.28% is therefore a floor for
construction, and not an estimate of what removing the tree saves: the tables
have to be written too.

## 7. The target pipeline

| # | Tree or table | Written by | Read by | Freed |
| --- | --- | --- | --- | --- |
| 1 | **Syntax tree** (`ParseArena`), with expansions appended and the sparse expansion table | the parser; the expansion pass appends | validation walks, the checker, the core IR builder, genType, the formatter and editor tooling (which ignore expansions) | when the module's core IR is built; kept by a tooling session |
| | Type graph (`TypeContext`, the shared world of CHECKER_REDESIGN J) | the checker | the checker, the core IR builder (through `typeopt`), diagnostics, genType, publication | local nodes with the module; published nodes live in the world |
| | Checker result tables (section 4), and the pattern pool until T10 | the checker | the core IR builder, match compilation, unit reads, genType | when the module's core IR is built |
| 2 | **Core IR** (`Bir`, level L) | the builder, straight from 1 and the tables, match compilation included | the level L rounds (in place), the lowering, the per-module summary | when the module's JavaScript tree is complete |
| | Statement stack, use counts, scope logs, top-level rows (1.5, section 2) | the lowering | the lowering, at scope close | per scope; with the module |
| 3 | **JavaScript tree** (oxc `Program` in a per-worker allocator) | the lowering, through the builder of section 3 | `oxc_codegen`, the source map builder | allocator reset after the module is printed |

**Three trees.** Not five: the typed tree's readers in a batch build are
served by tables (section 4), and the JS-level dialect's only purposes were
the four rounds and a place to hang flags, which the lowering's own
structures and the builder cover (sections 1 and 3). Not two: the syntax tree
cannot be the core IR, because the level L rounds restructure bindings and
exits (BACKEND_REDESIGN C.3) and the formatter needs the source as written;
and the core IR cannot be the oxc tree, because the output-visible decisions
of level L are made on language-level nodes (BACKEND_REDESIGN 0.2 item 2).

It is four in a tooling session until T12 (the typed tree is built on demand
for the file being inspected), and it is four in a batch build until T11.

## 8. Where the instructions are today

For orientation, from section 6: parse 11.6%, rewrites and sweep 4.5%, type
checking 36.1%, publication 3.0%, unit reads 1.2%, conversion to Lambda 6.3%,
Lambda passes 5.7%, lowering and JS passes 7.5%, printing 2.6%. The rest is
the build system, reading dependencies and writing files.

## 9. The saving

Percent of a clean build of `tests/tests` (4,310.7 M instructions), against
today's default build (legacy printer).

| Item | Today's cost | Saving | Kind |
| --- | --- | --- | --- |
| **New in this document** | | | |
| No rebuilt parse spine: expansion table instead of the mapper's rebuild | 4.13% in the two mapper entry paths (measured, section 6); validation is about 0.6% of the build inside that (FRONTEND_REWRITES) and stays | 1.5% to 3.0% | extrapolated |
| No typed tree in a batch build | 1.28% construction and destruction (measured floor), minus writing the tables | 0.5% to 1.3% | extrapolated |
| Unit reads collected while checking | 1.16% (measured) | 0.6% to 1.0% | extrapolated |
| Printing: oxc nodes written by the lowering, names at scope close | 2.60% (measured). Target: code generation 0.53% and tree construction 0.05% (measured, pull request #175), plus the name replay and program assembly (not measured) | 1.3% to 1.6% | extrapolated from measured parts |
| Sum of the new items | | **3.9% to 6.9%** | |
| **Already planned, unchanged by this document** | | | |
| Level L rounds (S4) | 5.65% (measured) | 3.0% to 4.0% | extrapolated from BACKEND_REDESIGN's budget |
| Conversion and match compilation into the core IR (S5) | 6.27% (measured) | 3.0% to 3.9% | extrapolated from the budget |
| Lowering with its decisions (S3) | 7.45% with the six JS passes (measured) | 2.5% to 4.0% | extrapolated from the budget |
| Sum of the planned items | | 8.5% to 11.9% | |
| **Whole pipeline against today** | | **12.4% to 18.8%** | extrapolated |

Against the five-tree plan as measured, not against today: pull request #175
measured the naming pass at 56 M to 68 M (1.3% to 1.6%) and the adapter over
J-level `Bir` at 65 M (1.5%) on `tests/tests`, which made printing from
J-level `Bir` cost 260 M where the legacy printer costs 112 M. This plan has
neither, so it avoids 2.8% to 3.1% of measured cost that the five-tree plan
would have had to win back. That figure is not added to the table: it is a
cost avoided, not a saving against today.

The four JS rounds cost 2.5% of the build today as self time of their files
and visitors (section 1). Deciding them at scope close is how the "lowering"
row reaches its budget; it is not a separate row.

No row is measured as a saving: every one is a measured cost of today and a
target. On the 3,735-module application the backend's share is larger (27.3%
of the build, BACKEND_REDESIGN 0.1) and the frontend's smaller; nothing here
was measured on it.

## 10. Re-cut of the work in flight

| Work | State | Verdict |
| --- | --- | --- |
| Level L rounds S4.1 to S4.4 (`bir/engine.rs`, `bir/l/{norm,flatten,exits,alias,beta,arity}.rs`) | merged | **stay as they are.** Level L is the core IR |
| S4.5 to S4.9 | planned | **stay as they are** |
| Lowering S3.3 (`bir/lower/*`, pull requests #170 and #182) | merged | **stays.** It writes J-level `Bir` nodes through `bir::j` and `View`; the two-text gate of BACKEND_LOWERING 8.1 does not depend on the storage |
| Lowering S3.4 to S3.9 (BACKEND_LOWERING 8.3) | merged, except loops and `LetRec` with value members (S3.7) | **stay as they are**, written against the same `bir::j` interface. The storage is swapped under them once, in T6 |
| J normalising rules (pull request #183, `bir/j/norm.rs`) | merged | **stays**: the rules are the specification of the builder's constructors. In T6 their pattern matches move from `View::J*` to oxc nodes plus the facts table; the rule tests carry over |
| Rounds J1 to J4 as passes over J-level `Bir` (S3.2: `bir/j/{inline_return,rest,subst,shake}.rs`) | not built | **change target**: decisions of the lowering at scope close (T1, T4), not passes |
| Export extraction and coercion on J-level `Bir` (S3.9b) | not built | **changes target**: on the lowering's top-level rows (T4) |
| Emitter under `emit/`: `literal.rs`, `raw.rs`, `sourcemap.rs`, `program.rs`, the node construction of `build.rs` | merged | **stay.** They are how oxc nodes are built; the builder of T6 calls them |
| `emit/naming.rs` | merged | **changes target**: its group and suffix tables stay, its walk (`walk.rs`, the `Visitor` over the JS IR) is replaced by the replay of T5 |
| Emit from J-level `Bir` (pull request #175: the view adapter, `bridge_j::import_js`) | not merged; #175 merged its measurement only | **dropped as a product path.** Its measurement is the evidence for this document, and its parity suites stay as the check of the oxc printer on the JS IR until T6 |
| `bir/bridge_j.rs` (`export_js`) | merged | **stays until T6** as the gate's bridge, then deleted |
| S5.1 builder trait, S5.2 `Bir` builder | planned | **change target**: the builder reads the syntax tree and the tables (T9) instead of the typed tree; the trait of S5.1 gets an input side |
| S5.3 to S5.5 match compiler work | done or planned | **stay** |
| Checker slices W1 to W11, K.6 (CHECKER_REDESIGN) | in flight | **stay**; independent |
| Subtree skipping of FRONTEND_REWRITES | merged | **stays**: the certificate bits become the expansion bit's neighbours (T2) |

Nothing that is merged is discarded. The only pull request whose product
goal is dropped is #175, which merged as the record of its measurement.

## 11. The new slices

Gates for every slice: `cargo build` and `cargo test` for
`compiler-rust/Cargo.toml` and `rewatch/Cargo.toml`; CI (JavaScript,
diagnostics, stdlib and genType parity; the instruction count). "Less capable
model" says whether the slice can be handed to one with this document.

| Slice | Change | Files | Deletes in the same pull request | End state (`rg` in `compiler-rust/src`) | Extra gate | Lines | Less capable model |
| --- | --- | --- | --- | --- | --- | ---: | --- |
| T1 | JavaScript use counts (built, remaining) in dense VarId tables, checked against the legacy UseCounts visitor; remove unused tail-position analysis. Block facts and transformations move to T4 (boundary finding below) | `bir/lower/{scope,mod,oracle_tests}.rs`, `bir/{edit,node,pools,validate}.rs` and validator callers | `Bir::mark_tail_positions`, `tail_child`, `NodeFlags::TAIL`, `FuncHeader::SELF_TAILCALL` | `rg 'mark_tail_positions\|SELF_TAILCALL' bir` is empty | both existing lower texts remain identical; fallback counts do not grow; 10,000-occurrence accounting test | 200 | yes: counters only |
| T2 | Expansion table: the mapper appends desugared constructs and records `original -> expanded`; no ancestor is rebuilt; readers resolve | `parse_arena.rs`, `binary_ast/ppx.rs`, `binary_ast/deps.rs`, `binary_ast/ast_iter.rs`, `types/typecore.rs`, `types/typemod.rs` | the rebuild arms of `rewrite_expression_generic` and `rewrite_child` and its `Rewritten::New` path for expressions | `rg 'fn rewrite_child' binary_ast/ppx.rs` is empty; `rg 'fn expanded' parse_arena.rs` has one hit | `scripts/test_error_output_parity.sh`, the `super_errors` fixtures, `make test-syntax`; instruction count falls by at least 1% | 1,500 | no: order of diagnostics |
| T3 | Unit reads without the typed-tree walk: the checker logs a read where it resolves a path | `types/unit_reads.rs`, `types/env.rs`, `types/typecore.rs`, `types/typemod.rs`, `driver.rs` | `unit_reads::Collector` and its `TastIterator` implementation | `rg 'TastIterator' types/unit_reads.rs` is empty | the read sets of old and new equal on the runtime library and `tests/tests` before the old one is deleted; `scripts/test_stored_interface_determinism.py`; rewatch incremental tests | 600 | yes, with the prompt below |
| T4 | Tail-call inlining at scope close (1.1); top-level rows, the shake filter and export coercion on them (1.4, S3.9b). Also owns original T1 items 3–6: block facts/substitution, dead declarations, record rest and the gate split. New side runs without legacy passes 3–6 | `bir/lower/{scope,tail,export}.rs`, `bir/shadow.rs` | the planned `bir/j/{inline_return,shake}.rs` are never created | `rg 'apply_js_tailcall_inline_pass\|apply_js_shake_pass' bir/shadow.rs` shows the legacy side only | the two-text gate; a counter of inlines where the level L count is not one | 1,500 | no: strong reviewer |
| T5 | Naming events logged by the lowering; names assigned at scope close by the tables of `emit/naming.rs`; compared with the names the pass computes | `bir/lower/scope.rs`, `emit/naming.rs`, `bir/shadow.rs` | nothing yet (the pass is the oracle) | `rg 'fn replay' emit/naming.rs` has one hit | name tables equal on every supported unit of the corpora | 900 | no |
| T6 | The builder over oxc nodes (section 3): `bir::j` reimplemented on oxc storage and the facts table; `RESCRIPT_BACKEND=new` prints from it | new `emit/builder.rs`, `bir/j/*`, `bir/lower/*` (types only), `driver.rs` | `bir/bridge_j.rs`, the J opcodes of `bir/node.rs`, the `Bir` view of `emit/walk.rs` | `rg 'JSeq\|JBlockLit' bir/node.rs` is empty; `rg bridge_j .` is empty | reformat-and-compare suites; instruction count of `new` below legacy | 3,000 | no |
| T7 | Direct typing for the node-local rows of section 5 (`l` integers, boolean match, single record `let`, `async`/`await`) | `types/typecore.rs`, `binary_ast/ppx.rs`, the core IR builder | their arms in the mapper | `rg 'fn transform_await' binary_ast/ppx.rs` is empty (as built: one hit, kept for the awaited-module rewrite; section 13) | diagnostics parity | 800 | yes, one row per commit |
| T8 | Checker result tables written beside the typed tree; a debug check that table and tree agree | `types/typecore.rs`, `types/typemod.rs`, new `types/tables.rs` | nothing | `rg 'struct ExprRow' types/tables.rs` has one hit | the agreement check on all corpora | 1,200 | yes |
| T9 | The core IR builder reads the syntax tree and the tables (replaces the input of S5.2) | `raw_lambda/convert.rs`, `convert/jsx.rs`, `typeopt.rs`, the `Bir` builder | reads of `Expression` in `raw_lambda/convert.rs` | `rg 'typedtree::Expression' raw_lambda` is empty | JavaScript parity; `Check` from the tables | 3,500 | no |
| T10 | Patterns: `parmatch.rs` and `matching.rs` read a view over syntax pattern, table row and overlay | `types/parmatch.rs`, `raw_lambda/matching.rs`, `types/dict_pattern.rs` | `TypedArena`'s pattern pools | `rg 'push_pattern' types` is empty | diagnostics and JavaScript parity; the exhaustiveness fixtures | 4,000 | no |
| T11 | genType from the tables; the batch build stops building typed expressions | `gentype/*`, `driver.rs` | `tctx.typed` in the batch path | `rg 'tctx.typed' driver.rs` hits only the tooling functions | genType parity | 2,000 | yes for genType |
| T12 | Editor analysis on the tables; delete the typed tree | `analysis/*`, `types/{typedtree,tast_arena,tast_iterator,sexp_typedtree}.rs` | those four files | `rg 'TypedArena' .` is empty | analysis tests | 3,000 | yes, arm by arm |

### T1/T4 boundary finding

**T1 ends at items 1 and 2 of the original worker prompt below. Items 3–6
move into T4**, together with tail-call inlining; they cannot independently
move ahead of the legacy tail-call pass while preserving final JavaScript.

The test `bir/lower/oracle_tests.rs::
block_substitution_and_dead_removal_do_not_commute_with_tailcall_inlining`
constructs this smallest Lambda-level shape (shown as JavaScript, bypassing
source simplification):

```js
const pair = [x => x, 1];
const run = () => pair[0](2);
// export run
```

In legacy order, tail-call inlining sees a field call. Later substitution
hoists `pair_0` and replaces that field read; final output retains
`function pair_0(x) { return x; }` and
`function run() { return pair_0(2); }`. If substitution and physical removal
of the dead `pair` declaration happen first, the retained tail-call pass
counts only one use of `pair_0` and inlines it: the final output is instead
`function run() { return 2; }`. The test asserts both outputs, without
changing the byte-exact gate.

T4 must preserve the original inlining decisions while coordinating these
transformations. T1 keeps both existing comparison points and all six legacy
passes on both sides; its counters add no intended default-backend saving.

Order: T1, T2 and T3 can start now and in parallel (they share no file except
`typecore.rs` between T2 and T3, in different functions). T4 and T5 follow
T1. T6 follows T4, T5 and S3.9. T7 follows T2. T8, T9,
T10, T11, T12 in sequence; T9 needs S4.9. Stop after T9 if T10's reader port
does not pay: the count is then three trees and a pattern pool.

### 11.1 Worker prompt for T1

```text
Task T1: decide dead declarations, block-field substitution and record rest
in the Bir lowering, so that the new side of the `lower` gate needs neither
legacy pass 4 nor 5. Repository: compiler-rust/. Read first:
docs/THREE_TREES.md sections 1.2, 1.3, 1.5; docs/BACKEND_LOWERING.md 1.3,
7.2, 8.1; src/lambda/js_pass_flatten_and_mark_dead.rs (Substitute,
should_materialize_block_binding_items, mark_dead_code and the
collect_mark_dead_states_* functions); src/lambda/js_pass_record_rest.rs
(RecordRest::block_items, materialize_fields, replace_source_fields).

Do exactly this, one commit each, in this order:
1. Delete Bir::mark_tail_positions and tail_child (src/bir/edit.rs),
   NodeFlags::TAIL (src/bir/node.rs) and FuncHeader::SELF_TAILCALL
   (src/bir/pools.rs) with their validator arm (src/bir/validate.rs) and
   tests. Nothing in src/bir/lower reads them.
2. Add src/bir/lower/scope.rs: per variable two counters, `built` and
   `remaining`, updated where a J `Var` node is created and where one is
   released (State::evaluate_now in args.rs, the rules of bir/j/norm.rs, the
   statement stack's remove paths). Add a test that, for every unit of
   oracle_tests.rs, `built` equals the count of the legacy UseCounts visitor
   (js_pass_tailcall_inline.rs) on the exported JsArena.
3. In Cont::Declare with an immutable block literal of two or more fields
   and a lexical let kind: apply should_materialize_block_binding_items and
   the hoisting of Substitute::statement (fresh variables named by
   block_substitution_name, created with State::fresh_variable), and record
   the fields as a fact of the variable. When lowering a field read of a
   variable with that fact, return the field when
   is_simple_substituted_index_value holds.
4. When a scope's statements are copied from the stack to their list
   (StatementStack::take_list in out.rs): drop a declaration whose
   `remaining` is zero and whose value is strictly pure; turn one whose value
   is not pure into an expression statement. Reproduce
   MarkDeadInfo::Recursive: a use that precedes the declaration counts.
5. Record rest: reserve the declaration's slot (StatementStack::reserve), and
   at block close run the logic of replace_source_fields over the stack slice
   after it, then fill the slot.
6. In src/bir/shadow.rs (check_lower and prepare_lower): the new side skips
   apply_js_record_rest_pass and apply_js_flatten_and_mark_dead_pass; the
   legacy side keeps all six passes.

Do not: change which JavaScript the default mode emits; touch
src/lambda/*.rs except to make a function pub(crate); port tail-call
inlining or the shake (that is T4); weaken the gate or add a new
Unsupported reason to make a unit pass. If a unit differs and you cannot
explain it from the two documents, stop and report the unit and the first
differing line.

Checks to paste in the pull request: cargo test --manifest-path
compiler-rust/Cargo.toml; the `lower` and `lower+passes` texts identical on
the runtime library, tests/tests and the parity fixtures
(scripts/test_backend_coverage.py), with no fallback count higher than on
trunk; `rg 'mark_tail_positions|SELF_TAILCALL' compiler-rust/src/bir` empty;
`rg 'apply_js_record_rest_pass|apply_js_flatten_and_mark_dead_pass'
compiler-rust/src/bir/shadow.rs` showing the legacy side only; the CI
instruction count (the code is dormant in the default mode).
```

### 11.2 Worker prompt for T2

```text
Task T2: the built-in rewrites stop rebuilding the parse tree. A rewritten
construct is appended as an expansion and recorded in a table; its ancestors
keep their nodes. Repository: compiler-rust/. Read first:
docs/THREE_TREES.md section 5; docs/FRONTEND_REWRITES.md (all of it, the
order of the validation walks is the contract); src/binary_ast/ppx.rs
(rewrite_child, rewrite_expression, rewrite_expression_generic, desugar_pipe,
rewrite_structure_impl, UnusedAttributeSweep); src/parse_arena.rs
(push_expr, expr_needs_no_rewrite, invalidate_rewrite_free_exprs).

Do exactly this, one commit each, in this order:
1. Measurement only, not committed: count, on tests/tests, the expressions
   the mapper rebuilds whose own construct is not rewritten. Put the number
   in the pull request.
2. ParseArena: a sparse table `expansions` from ExprIdx to ExprIdx and one
   more bit per expression in the packed table that holds the certificate
   bits; `set_expansion(original, expanded)` and
   `expanded(idx) -> ExprIdx` (the bit test, then the lookup). The original
   node is never overwritten. Unit tests for both.
3. Readers resolve through `expanded` in their expression entry: type_expect
   and type_exp (src/types/typecore.rs), the expression arms of
   src/binary_ast/deps.rs, AstIter::expr as used by UnusedAttributeSweep, and
   the v0 mapper (src/binary_ast/mapper_to0.rs). After this commit nothing is
   recorded yet, so every output is unchanged.
4. rewrite_expression_generic: for each rewritten kind (the pipe, the record
   and unwrap bindings, the boolean match, async functions, await, awaited
   local modules, @this, raw, ffi, regexp, todo), build the same expansion as
   today from the ORIGINAL child handles and call set_expansion. A kind that
   reads the rewritten shape of a child (rewrite_pipe_rhs does) reads it
   through `expanded`.
5. Delete what no longer runs: the arms that rebuild a parent because a child
   handle changed, and rewrite_child. Patterns, core types, module
   expressions and structure items keep today's code in this slice.
6. UnusedAttributeSweep reads the original node for attributes the expansion
   consumed: add the predicate and its test.

Do not: move any rewrite into the parser; change the three validation walks'
order or merge them; change mapper_from0; touch the typed tree. If a
diagnostic's text, location or order changes, that is a defect of this
change, not of the fixture.

Checks to paste: cargo test for compiler-rust and rewatch; make test-syntax;
./scripts/test_rust_parity.sh --skip-js; ./scripts/test_js_output_parity.sh;
./scripts/test_error_output_parity.sh; the super_errors build tests;
`rg 'fn rewrite_child' compiler-rust/src/binary_ast/ppx.rs` empty; the CI
instruction count, which must fall (state by how much; below 1% means the
rebuild was not the cost and the pull request says so).
```

### 11.3 Worker prompt for T3

```text
Task T3: collect a module's unit reads while it is type-checked, instead of
walking the typed tree afterwards. Repository: compiler-rust/. Read first:
docs/THREE_TREES.md sections 4 and 6; src/types/unit_reads.rs (Collector,
structure_reads, signature_reads, SeenTypes); src/cmi/item_deps.rs (UnitRead,
Kind, read_of_path, resolve_reads); the call sites in src/driver.rs
(options.collect_unit_reads).

Do exactly this, one commit each, in this order:
1. A `ReadLog` owned by TypeCheckContext, enabled only when
   collect_unit_reads is set: a set of (Kind, path) and a set of type nodes,
   with the same deduplication as Collector (`paths`, SeenTypes).
2. Log at the points where the checker stores what Collector later reads
   back: every place typecore.rs and typemod.rs build a node that carries a
   Path, a constructor description, a label description or a type
   (Texp_ident, Texp_construct, Texp_field, Texp_record, Tpat_construct,
   Tpat_record, Ttyp_constr, module paths, opens, and exp_type, pat_type,
   ctyp_type). List the sites in the pull request, one line each, next to the
   Collector method they replace.
3. A check mode (debug assertions and a test over the runtime library and
   tests/tests): both collections run; the two results are compared as sets.
   They must be equal. If the log has a read the walk does not, find why
   (a node that is built and then discarded) and remove it at the source.
4. Switch structure_reads and signature_reads to return the log's result.
5. Delete Collector and its TastIterator implementation. Keep
   src/types/tast_iterator.rs: src/analysis/process_extra.rs uses it.

Do not: change item_deps.rs or the format of stored reads; log in
Env::lookup_* (a lookup that fails or is retried is not a read of the typed
tree); make the sets equal by sorting away a real difference. If equality
cannot be reached for a unit, stop after commit 3 and report the unit, the
read and the node.

Checks to paste: cargo test for compiler-rust and rewatch; the set
comparison of commit 3 on both corpora (count of units, count of reads,
zero differences); scripts/test_stored_interface_determinism.py; the rewatch
integration tests (make test-rewatch); `rg 'TastIterator'
compiler-rust/src/types/unit_reads.rs` empty; the CI instruction count, which
must fall by about 1% of tests/tests (structure_reads is 1.16% today).
```

### 11.4 T4 design

Status: design and findings. No decision is implemented yet; the tests named
below pin the legacy behaviour each finding rests on
(`bir/lower/oracle_tests.rs`). "P1" to "P6" are the six legacy passes in
order (flatten, external shadow, tail-call inlining, record rest,
substitution with dead marks, shake); "C0" is the count of `Var` occurrences
in the program P3 receives.

#### Findings: what row T4 and section 1 did not account for

1. **P3 reads the tree P1 wrote, not the tree the lowering wrote.** The
   lowering merges two returning branches into `return c ? f(1) : 2`; P1
   splits it into an `if` again, and only then does a block end in `return
   f(1)`. Test `a_tail_call_site_inside_a_returned_conditional_exists_only_
   after_the_flatten_pass`: with P1 first, `f` is inlined; with P3 first it
   is kept. So a tail-call site is "a call that P1 leaves as the last
   statement of a block": through the branches of a returned conditional and
   the last operand of a returned sequence. P1 can also drop occurrences (a
   pure branch of a conditional in statement position), so `built` is C0 only
   if the lowering never leaves such a statement; that is not verified.
2. **The top level cannot be decided before export coercion.** P3 and P5
   give a declaration the status `Exported` from the export set, and C0 of a
   top-level variable is counted after coercion consumed the export tuple,
   added the rebound declarations and substituted moved aliases
   (`coerce_toplevel_exports_with_name_reservations` in `lam_compile.rs`,
   `move_same_name_export_alias_to_export_tail` and `substitute_after` in
   `js_shake.rs`). Both sides of the gate run that code on the JS IR after
   the lowering. So export extraction and coercion in the lowering (S3.9b) is
   a precondition of every top-level decision, not the sixth commit. It is
   about 1,500 lines of legacy code whose helpers scan the block
   (`statement_mentions_ident_anywhere`,
   `statement_uses_ident_only_in_tail_move_safe_positions`); on rows they
   need, per reference, the statement it is in and whether its position is
   safe for a moved alias.
3. **A dead mark is not final when its scope closes.** Test
   `inlining_from_an_outer_scope_takes_the_last_use_of_a_variable_of_a_
   closed_scope`: `f` is declared outside a function whose body is `let y =
   ext(); return f(y)`. When that body is complete `y` has one use (the test
   reads `built` and `remaining`, both one). The outer scope then inlines
   `f`, whose parameter is renamed to `y` and never read; P5, which runs
   after all of P3, prints `ext();`. Pruning a branch of an inlined body does
   the same to variables of the body.
4. **Scope-close edits make `built` drift after a later release.** The
   lowering can release a subtree after scopes inside it closed (a discarded
   tail after a finished output, a folded branch, a pure effect). The release
   subtracts the occurrences that are there now, not the ones C0 had. Read,
   not tested.
5. **P3 removes a dead block binding before P5 can materialise it.** Test
   `a_declaration_the_tail_call_pass_finds_dead_is_not_materialised`: an
   unused `let x = (ext(1), ext(2))` prints as the expression statement
   `[ext(1), ext(2)];`. Hoisting where the declaration is lowered prints `let
   x_0 = ext(1); let x_1 = ext(2);`. Whether `x` is dead is C0, known at the
   close.
6. **P4 reads a field read that P5 would replace.** `replace_source_fields`
   looks for `source.label`; when the source is bound to a record literal,
   P5 replaces that read by the field. Replacing where the read is lowered
   hides it from the record rest. Read, not tested.
7. **The inlined callee has no status if a decision created it.** The
   boundary shape: `pair_0` exists only after P5, so P3 never inlines it.

Consequences for 1.1 to 1.5: hoisting and substitution cannot happen "while
lowering" (1.3); they happen at the close, after the P3 and P4 decisions of
the same run. "Removal when the statements are copied" (1.3) holds only for
a variable no pending inline site can reach; the rest is marked in place.
1.4's rows need the position facts of finding 2.

#### The design

**Two counts** (`bir/lower/scope.rs`, `Uses`). `built` is C0: it changes
only where the lowering itself builds or releases a `Var`. `remaining` is
what the dead marks of P5 count. A scope-close decision writes `remaining`
only.

**A late mark** on every node a scope-close decision creates (a substituted
field value, a renamed parameter, the occurrence of a hoisted variable). P3
treats a late node as absent from C0: a late `Var` is no callee, and a late
argument is neither a variable nor a constant for parameter substitution,
because P3 saw the field read it replaced. `NodeFlags` has no free bit; the
mark is a bit of the leaf's `aux`.

**Where a scope closes.** `StatementStack::take_list`: every use of a
variable is lowered before the run that holds its declaration is copied (a
use is in the body of the `let`; a deferred value travels with the run). The
close visits the slots of the run, never a statement's body.

**Order at the close of a run**, with the count each step reads:

| Step | Decision | Reads | Writes |
| --- | --- | --- | --- |
| A (P3) | Status of each declaration, in slot order: `built == 0` is dead (dropped when strictly pure, an expression statement otherwise); `built == 1`, strictly pure, lexical kind, a function literal that is not a method, not `async`, without directive: inline candidate | `built` | `remaining` of the variables in a dropped value |
| A (P3) | The site recorded for a candidate is spliced when the arity matches | `built` of the callee; the late marks of the arguments | the site becomes the callee's statements; parameters renamed, replaced or declared; `remaining` |
| B (P4) | Record rest, only in a run that has one, last declaration first | the slots after the declaration, as A left them | the pattern; the reads of the source |
| C (P5) | Substitution, in slot order: a surviving lexical declaration of an immutable block literal with two or more fields is materialised, then each recorded read is replaced when the field is simple | field facts; the read sites of the variable | late nodes; `remaining` |
| D (P5) | Dead marks while the slots are copied | `remaining` after A to C | dropped, or an expression statement |

For an inner run, C and D have run before the A of an outer run; the late
mark keeps that A on the C0 shape (finding 7).

**Facts recorded while lowering**, dense by `VarId`: `Uses` (8 bytes);
`VarFacts` (16 bytes): the declaration's statement node, the head of the
variable's read sites (`x[i]`, `x.f` with a constant index), its single
tail-call site (recorded while `built` is one and the site is not inside the
variable's own initialiser; a second occurrence clears it), and state bits.
Read sites are `(node, next)` pairs in a pool, 8 bytes each.

**Late zero** (finding 3). A decrement that brings `remaining` of a variable
whose run is closed to zero marks its declaration in place, through
`VarFacts`. Marks are one level, as in P5: the occurrences inside a
declaration that D drops stay counted.

**Graves** (finding 4). Where a decision removes occurrences C0 counted, they
are logged against the variable whose declaration anchors them (the dead
variable, the inlined function); the anchor stays in its list as a dead
declaration without value, and a release that reaches it subtracts the log
from `built`.

**A site in a closed list.** The splice rewrites the `return` node in place
into a block of the callee's statements. P1's `block_items` splices a nested
block into its list; whether every later reader treats the two alike is to
be shown by the gate of T4c.

**The boundary shape.** `return pair[0](2)` is no site (the callee is a field
read) and is recorded as a read site of `pair`. At the top-level close A
finds no candidate; C hoists `pair_0` and replaces the read by a late `Var
pair_0`; `pair_0` has no P3 status; D drops `pair`: the legacy output.

**The counter.** Sites spliced, and of those the number whose callee has a
level L use count other than one, in the check report.

#### T4b experiment: RESULT B (copied-branch reader)

Copy-time R1–R8 were tested and removed. The first printed-text difference
was `Primitive_object.res`, `lower` line 75: a following `if` became an
`else if`. The reduced Lambda is a one-case string switch:

```text
function (x, y) => stringswitch x {
  "a": if y then 1 else 2;
  default: sequence(initMod(), 3)
}
```

`State::if_statement` (`bir/lower/cond.rs`) copies both branches with
`StatementStack::take_list`, then calls `js3_simplify_if`. Its
`simplify_if_head` reader tests the last statement syntactically. Before
R5 the case is `Return(Cond(y, 1, 2))`, so the default is moved after the
guard. Copy-time R5 makes that last statement an `If`, so the default stays
inside `else`. This is not an incorrect implementation of R5: the rule's
printed-text oracle agrees with legacy Flatten. The test
`flattening_a_copied_return_branch_changes_the_simplify_if_head_reader`
pins both complete final texts and recreates this one copied-branch
boundary using the legacy rule oracle; no alternate production path remains.

The count trial initially included export-tuple references. These belong to
finding 2/T4a, not to a flattening failure: the test
`export_tuple_occurrences_are_not_the_tailcall_pass_input_counts` pinned
built=1 versus post-coercion C0=0 with identical final text. (T4a closed
that drift: the lowering's own export coercion releases the reference, and
the test, now `export_coercion_consumes_the_export_tuple_occurrence`,
asserts built=0, equal to C0.) Repeating the
experiment subtracted exactly the references in that sentinel tuple from
the comparison (not from `built`); the printed-text difference remained.
The trial observed 331 excluded occurrences in 331 variable rows across 73
runtime units, each row excluding one reference. The application attempt
observed 209 such rows across 61 runtime units before failure; these are
partial observations, not whole-corpus counts. The tests and fixtures
corpora were not reached by the failed runtime-first experiment.

The count comparison is not retained: generated variables also need an
identity correspondence between lowerings (`_list/1024` and `_list/1027`
both have two references), and raw Ident lookup is not that correspondence.
The printed-text counterexample alone establishes RESULT B. No inference
about count parity or commutation with T4c–T4e follows from this experiment.

T4b is done in the counterexample form: pass 1 stays until T6. T4c must read
its sites through P1's reshaping (finding 1), without moving that reshaping
ahead of the lowering's copied-list readers. R1–R8, their copy-time call,
the skipped pass and the experimental count comparison have been deleted.

#### T4c design: RESULT (the inlining cannot leave before P1 and P2)

With step A in the lowering, the new side's order is A, P1, P2, P4, P5, P6
against P1, P2, P3, P4, P5, P6. Three things must hold for the two printed
texts to stay equal. (a) holds. (b) holds only with two additions that are
not facts of a statement. (c) fails, twice, each with a test that asserts
both complete texts. So P3 stays on the new side, as P1 does.

**(a) The sites.** P3 inlines at the last statement of a statement list when
it is `return f(args)` (`TailcallInlineState::block_items`,
`try_inline_single_return_statement`). Read through P1, as a function of the
returned expression `e` of a `return` the lowering wrote:

```text
sites(e) = sites(a) + sites(b)   e = c ? a : b    (P1: Return(Cond) becomes If(c, [return a], [return b]))
         = sites(b)              e = (a, b)       (P1: Return(Seq) becomes a; return b)
         = { e }                 e = f(args), f a variable
         = {}                    otherwise
```

P1 applies its `return` rules to the `return`s it creates, so the function is
recursive in the same places. A `return` that P1 creates inside the `if` of a
returned conditional is the only statement of its list, so a site below a
conditional is a site wherever the `return` stands. A site reached without
passing a conditional is one only if the `return` is the last statement of
its list after P1 spliced nested blocks; the lowering knows that where the
run is copied (`StatementStack::take_list`: the last slot). The predicate `c`
and the heads `a` hold no site: P1 leaves `c` in the predicate of the `if`
and makes each head an expression statement. No other P1 rule creates a
`return`. `try_inline_single_return_statement` also inlines a function
literal called in place (`return (function (p) {...})(x)`), with the arity
rule and without a status; `sites` has the same case with `e` a call of a
function literal.

**(b) The count.** P3's `UseCounts` counts `Var` nodes by identifier in the
program after P1 and P2.

- P2 replaces a reference to a JavaScript global by `globalThis.name`. A
  global is never declared, so no count of a declared variable changes.
- P1 moves nodes in every rule but one: an expression statement that is a
  conditional loses a branch that has no side effect, and the whole
  statement when both branches and the predicate have none (`Flatten::
  statement`, `Exp(Cond)`). Every variable read in such a branch has one
  occurrence less in C0 than in `built`. The lowering leaves such
  statements (`jm14_push_effect_expression` drops a strictly pure value, not
  a pure branch). Which variables lose an occurrence is a property of the
  branch's contents, not of the statement: recording it where the statement
  is built means visiting the branch there, which is P1's rule applied at
  that point. It is the rule T4b could not move.
- Identity. P3 counts by identifier. The lowering gives a copied function
  literal (`copy_j` in `bir/j/logic.rs`: a repeated pure function) binders of
  its own that print as the originals (`vars.j_origin`); the legacy arena
  shares the one function. A variable declared inside a function that is
  copied has C0 equal to the sum of `built` over its copies, and the copy is
  made after the runs inside the function closed. A status read from `built`
  at the close is wrong for it: `built` is one per copy, C0 is two, P3 does
  not inline.

So `built` at the close is C0 for a variable that is read in no dropped
branch and declared in no function that is copied later. The second
condition is not known at the close. Commit 2 of T4c measures both: the
lowering computes the status of each declaration of a run from `built` where
the run is copied, records the site, and check mode compares them with what
P3 computes on the same program after P1 and P2 (the same identifiers, so
the comparison is by declaration; the caution about generated identifiers of
the T4b experiment concerns comparisons between the two lowerings).

**(c) P1 and P2 after the splice.** Two counterexamples
(`bir/lower/oracle_tests.rs`).

1. *P2 reads the bindings around a reference.*
   `inlining_before_the_external_shadow_pass_hides_the_binding_that_shadows_
   a_global`: `run = a => { let g = location => ext(location, location')
   ; return g(a) }`, where `location'` is the JavaScript global. P2 qualifies
   a global when a binding of an enclosing list, a parameter, a loop
   variable or a catch variable prints with its name. In legacy order the
   parameter `location` is around the reference when P2 runs:
   `return ext(a, globalThis.location)`. With the splice first, the parameter
   was renamed to `a` and the function is gone: `return ext(a, location)`.
   The reverse happens too: the declarations of the callee's body land in the
   caller's list and shadow globals read anywhere in that list. A grave (a
   dead declaration kept without value) keeps a removed declaration visible
   to P2; nothing keeps a parameter visible, and nothing hides a spliced
   declaration from the rest of the caller's list.
2. *P1 maps the predicate of an `if` it did not create.*
   `flattening_after_a_site_in_a_returned_conditional_was_spliced_maps_its_
   predicate`: `run = c => { let f = p => ext(p, p); return ext(z => z ? 1 :
   2) ? f(c) : 3 }`. The callee's statements can only stand in a branch of an
   `if`, so step A has to write the `if` that P1's `Return(Cond)` rule would
   write. That rule leaves the predicate unmapped: in legacy order the
   callback prints `z => z ? 1 : 2`. P1 run afterwards meets an `if`
   statement and maps its predicate (`map_statement_children`): the callback
   prints as `if (z) { return 1; } else { return 2; }`. No expression P1
   passes over can stand for the callee's statements, so the `if` cannot be
   left for P1 to write.

The remaining parts of (c) hold as read: P1 flattens a spliced body as it
flattens the function body in place (`block_items` splices the block the
site becomes; a block of one statement is unwrapped), and the substitution
of a parameter by a variable or a constant does not change which branches
P1's purity tests drop (a variable and a substitutable constant are both
pure).

**What has to move first.** P3's decisions can leave the new side only when
neither P1 nor P2 runs after the lowering:

- with P1's `return` and expression-statement rules (T6), which removes
  counterexample 2 and the dropped-branch term of (b): the lowering then
  writes the `if` itself, once, and releases the dropped branch through the
  path that maintains `built`;
- with the names decided in the lowering (T5), which removes
  counterexample 1: P2 is a naming decision (which printed names are bound
  around a reference), and after a splice the binding structure P2 would
  read no longer exists;
- with a count by origin, or with copies made before the runs inside the
  copied function close.

Until then step A's *decisions* are computed and compared (commit 2 of T4c),
and the splice is not performed. T4d and T4e read the tree P3 wrote (finding
5 and 6), so they stay behind P3 as well: the next legacy step that can
leave the new side is the shake (T4f needs the dead marks of P5, so it waits
too) or, in legacy order from the other end, P1 at T6.

**As built and measured** (`bir/lower/close.rs`, `scope::return_sites`,
`shadow::compare_decisions`). Where a run is copied, last statement first:
a `return` records the calls `sites` gives as the site of their callee
(`VarFacts`, 8 bytes, dense by variable: the site and the exported bit), and
a declaration gets a `Decision` (8 bytes: the status from `built`, whether it
is an inline candidate with a site, `built`). The top level is decided after
the coercion, with the export set marked through each export's origin. One
step per statement and per operand on the way to a call; 3 steps per
declaration at 10,000 (`ten_thousand_declarations_close_in_three_steps_
each`). Check mode runs P1 and P2 on a copy of the new side's program and
compares, per declared identifier, with `js_pass_tailcall_inline::decisions`.

| Corpus | Units | Declarations | Inline candidates (lowering / P3) | Count, status, site differences | Extra, missing, copied | Decisions replaced |
| --- | --- | --- | --- | --- | --- | --- |
| runtime | 113 | 878 | 22 / 22 | 0, 0, 0 | 0, 0, 0 | 116 |
| tests/tests | 854 | 8,429 | 109 / 109 | 0, 0, 0 | 0, 0, 0 | 960 |
| the application | 3,848 | 144,584 | 2,279 / 2,279 | 0, 0, 0 | 0, 0, 0 | 31,158 |

(The fixtures corpus was not run: it needs the reference compiler's
executable.) So (b) holds on these corpora only. Both hazards are pinned as
differences between `built` and the count P3 reads:
`a_pure_branch_the_flatten_pass_drops_takes_an_occurrence_built_still_
counts` (`ignore(c ? x : ext())` leaves the statement `c ? x : ext();`;
`built` of `x` is one, P3 counts zero and makes `let x = ext()` an expression
statement) and `a_copied_function_doubles_the_legacy_count_of_the_variables_
declared_inside_it` (the function is copied with `copy_j` after its run
closed: `built` is one per copy and the decision is "inline candidate", P3
counts two and keeps the function). No unit of the corpora has either shape.
The counter 11.4 asked for (sites spliced) is the inline-candidate column:
nothing is spliced.

Instructions of a clean build of `tests/tests` (cachegrind, one worker
thread, release binary, one run each; run-to-run noise is about 0.1%),
before (the head of the export slice) and after: with `RESCRIPT_BACKEND=
check` 20,616,262,185 and 20,759,677,746 (+0.70%: the close, and P1 and P2
run once more on a copy of the new side's program for the comparison); the
default build 4,072,030,942 and 4,074,346,809 (+0.06%, within noise: the
default build does not run the lowering).

Two places where the code is not what "The design" says:

- *A run is not closed once.* A statement the lowering moves out of a copied
  list (`simplify_if_head` moving a branch after its guard, a held run) is
  copied again, and its declaration is decided again: about one decision in
  five on the application. The last decision is the one that stands; a
  splice at the first close would be done on a list that is read again.
- *`take_list` is not the only place a statement list is made.*
  `simplify_if_head` (`bir/j/norm.rs`) builds `if (!c) { return n }` with a
  list of its own, and `n` can come from a run that was never copied. Its
  site was missed until `return_sites` was called there (one declaration in
  tests/tests). `cond.rs` and `external.rs` build lists directly as well;
  none of them holds a `return`.

#### Re-cut: one legacy step leaves the new side per slice

The commit order of the T4 prompt (block facts, dead declarations, record
rest, inlining, rows, gate) cannot be gated step by step: a decision moved
ahead of a legacy pass that still runs changes that pass's input (the
boundary finding; findings 1, 2, 5, 6). In legacy order every step can: the
new side drops exactly the pass whose decisions moved, and the two printed
texts stay equal.

| Slice | Moves into the lowering | New side stops running | Needs |
| --- | --- | --- | --- |
| T4a (done) | Export extraction and coercion on top-level rows (`bir/lower/export.rs`, S3.9b), with the position facts of finding 2 as sites ("T4a as built") | `extract_toplevel_exports`, `coerce_lowered_output` | - |
| T4b (done, RESULT B) | Counterexample: R5 changes the `simplify_if_head` reader of a copied branch; read sites through P1 instead | Nothing; P1 stays until T6 | - |
| T4c (done, counterexamples) | The statuses and the site of step A, computed and compared in check mode; no splice ("T4c design") | Nothing; P3 stays until P1 (T6) and P2 (T5) have left | T4a, T4b |
| T5b (done; check mode only) | The naming log: scope rows and free lists recorded by the lowering, replayed over the final statement lists ("T5 part B as redesigned", "T5 part B as built") | Nothing yet; the naming pass stays the oracle until T6 prints the replay's names | T1 |
| T4g | The splice of step A, late marks, late zero, graves, the counter (11.6) | `apply_js_tailcall_inline_pass` | T5, T6 |
| T4d | Step B | `apply_js_record_rest_pass` | T4g |
| T4e | Steps C and D | `apply_js_flatten_and_mark_dead_pass` | T4d |
| T4f | The shake as a filter over the rows | `apply_js_shake_pass` | T4a, T4e |

**The order as read after T4c**: for each legacy pass still on the new side,
the passes that must have left it first, and what shows the dependency. A
pass leaves when its decisions are taken in the lowering; "not tested" means
the dependency is read from the code and no test asserts two texts for it.

| Legacy pass | Leaves at | Must have left first | Shown by |
| --- | --- | --- | --- |
| P1 flatten | T6 | none; but its rules cannot be applied where a run is copied, so it leaves with the lowering's list readers | `flattening_a_copied_return_branch_changes_the_simplify_if_head_reader` |
| P2 external shadow | T5 (left: "T5 as built") | none: it is before P3 in legacy order; the decision is taken once at the unit root, on the lists P1 receives | the rule tests of "T5 as built"; the four corpora |
| P3 tail-call inlining | T4g | P1 | `flattening_after_a_site_in_a_returned_conditional_was_spliced_maps_its_predicate`; for the count, `a_pure_branch_the_flatten_pass_drops_takes_an_occurrence_built_still_counts` |
| | | P2 | `inlining_before_the_external_shadow_pass_hides_the_binding_that_shadows_a_global` |
| | | (also: a count by origin, or no copy after a close) | `a_copied_function_doubles_the_legacy_count_of_the_variables_declared_inside_it` |
| P4 record rest | T4d | P3: it reads the slots after the declaration as P3 left them | not tested |
| P5 substitution and dead marks | T4e | P3 | `a_declaration_the_tail_call_pass_finds_dead_is_not_materialised`, `block_substitution_and_dead_removal_do_not_commute_with_tailcall_inlining`, `inlining_from_an_outer_scope_takes_the_last_use_of_a_variable_of_a_closed_scope` |
| | | P4: it reads the field reads P5 replaces (finding 6) | not tested |
| P6 shake | T4f | P5: it reads the dead marks (`used_stats` in `js_shake.rs`) | not tested |

`apply_external_shadow_pass` (P2) rewrites references to JavaScript globals
that a binding shadows. It changes no count of a declared variable, but it
reads which bindings exist, so it has to see the parameters and declarations
P3 removes and must not see the ones P3 moves into another list.

**What T5 must deliver for P3 to leave.** P2's decision for a reference to a
JavaScript global is: some binding around the reference prints with the
global's name (`printed_binding_name`, `convert_ident_name`). The bindings
are the declarations of every enclosing statement list (all of the list, not
only those before the reference; the cases of one `switch` share a scope),
the parameters of every enclosing function, loop variables, catch variables,
and the imported modules of the unit. T5 delivers that decision as a fact of
the reference node, taken on the binding structure the lowering wrote and
not changed by a later scope-close decision: a reference that P2 would
qualify is built as `globalThis.name` (or carries a bit the printer reads),
and one P2 would leave stays plain even when a splice later puts a
declaration of that name into its list. The check a worker can run: with T5
in, `rg -n 'apply_external_shadow_pass' src/lambda/lam_compile.rs` shows the
legacy side only, and the Lambda of
`inlining_before_the_external_shadow_pass_hides_the_binding_that_shadows_a_
global` lowered by the new side and run through P1, P3, P4, P5, P6 (no P2)
prints `return ext(a, globalThis.location);`. The reverse case needs its own
test in T5: a callee whose body declares `let location = ...`, inlined into
a caller that reads the global `location`, prints the global unqualified,
as the legacy order does.

#### T4a as built

Done. The new side of the `lower` gate runs neither `extract_toplevel_exports`
nor `coerce_lowered_output`: it goes from `bridge_j::export_js` to the six
passes. The legacy side and the default build keep both. Code:
`bir/lower/export.rs`, entered from `State::complete_unit`.

**What a row is.** `Row`, 8 bytes: the node of one top-level statement and a
word of bits (declaration; has an initialiser; the initialiser is a function
literal; a top-level block statement; a statement directly inside one;
moved to the export tail; a rebound export was inserted before it; inserted;
declared after the top level). The rows are the top-level run of the
statement stack in output order, written when the unit's last value is
complete (`build_rows`): one step per statement of the run and per statement
directly inside a top-level block. The bits come from the statement node and
the operation of its initialiser; no statement body is read. A row keeps its
index for the whole fold: a moved declaration is marked, a declaration the
fold adds is a new row with a bit that says where it is written, so "before"
and "after" are comparisons of indices. `coerced_list` writes the final list
from the rows, one step per row.

**What an export is.** No record: the values of the exports, detached, in a
vector by export index, and the variable each export names. The importer
gives every identifier of an export block a `VarId` where it imports the
block (one lookup per export in the identifier table it already has, for the
lowering only), so the fold compares variables, never identifiers. A
variable the lowering copied compares through its origin (`vars.j_origin`),
which is the identity the legacy identifiers have.

**Step 1, extraction** (`extract_exports`). The unit no longer ends in a
sentinel statement that carries `Out::value`. The value is read as
`extract_toplevel_exports` reads it: an export block gives the exports and
their values; a comma whose right spine ends in an export block gives its
heads as effect statements (`jm14_push_effect_expression`) and then the
block; `undefined` gives nothing; anything else is one effect. A finished
unit replaces every value by `undefined`. The sentinel remains in a
test-only `State::complete`, for the rule tests of single constructs.

**Step 2, the fold** (`coerce_exports`), one export at a time in export
order, the arms in the legacy order. What each arm reads:

| Legacy helper | Reads on rows |
| --- | --- |
| `collect_declared_idents` | the first declaration row of the variable (dense by variable); for a declaration below the top level, the parents of its node up to the top level: declared when only `SIf` and `SBlock` lie between |
| `find_declaration`, `same_name_export_alias_binding`, `block_declares_*` | the first declaration row of the variable |
| `resolve_tail_move_replacement_expression`, `tail_move_materialized_root_ident`, `resolve_tail_move_initializer_kind` | the initialiser of each declaration on the alias chain; a chain visits a variable once (a mark dense by variable, cleared from a trail) |
| `statement_mentions_ident_anywhere` (uses before, uses after), `later_toplevel_initializer_mentions_ident`, `later_toplevel_function_mentions_ident`, `tail_move_uses_are_safe_to_inline`, `replacement_resolves_to_recursive_function` | the sites of the variable, one pass (`mentions`, below) |
| `has_later_toplevel_function_binding`, `later_toplevel_effect_allows_tail_move`, `can_reuse_existing_undefined_export_binding` | the index of the last row with the function bit, of the last row that is no declaration, and of the last row with a top-level effect (read once per unit, from the last row backwards, from the strict-purity flag of each row's expression); none changes during the fold, because a moved declaration and its replacement are strictly pure |
| `direct_reused_same_name_export_alias_binding`, `reusable_same_name_export_binding`, `count_materialized_same_name_binding_roots` | the declaration rows that carry the export's name, chained in row order |
| `insert_rebound_export_before_equivalent_later_binding` | the rows from the last one backwards while they are such bindings |
| `substitute_after` | the references the `mentions` pass kept: each is replaced by a copy of the replacement |

**The position fact.** `Site`, 8 bytes (`bir/lower/scope.rs`): the node of
one reference and the next site of the same variable; the head is dense by
`VarId`. A site is written where the reference is lowered, in the one place
a node is allocated (`Bir::allocate`); the `Var` leaf keeps its site index
in its unused second word, so the site follows the node when a replacement
moves the node's content into another slot, and is cleared where the node is
released.

11.4 asked for two facts per reference at that point: the statement it is in
and whether its position is safe for a moved alias. Neither exists there. A
reference is built before its parent, and the statement that will hold it is
not on the stack yet; a reserved slot is filled and a held run is moved to an
earlier slot after later statements were pushed (`fill`, `hold_run`), so
neither the slot count nor the order of creation gives the row. Both facts
are therefore read from the site's node when the top level is complete:

- safe position: the parent's operation and the operand the reference
  fills (callee of a call, of a flat call or of a tagged template; target of
  `new`), one read;
- the statement, and whether a function literal lies between: the row
  reached through the parent links (`row_of`). A table dense by node
  remembers the row and the function bit of every ancestor a walk has
  passed, so a walk stops at the first ancestor another walk reached, and
  each node above a queried reference is entered once per unit. A reference
  whose root is no row (an export value) is in no statement.

A variable is asked about by at most one export: every arm that reads sites
reads those of a variable carrying the export's name, and export names are
distinct. One pass over the variable's sites answers all the questions of
that export and keeps the references in later rows for the substitution, so
a reference is read from its chain once. The chain holds one site per `Var`
node ever built for the variable, released ones included.

**Names.** The rows that declare a variable with an export's name are found
by name: one table from the export names to the export index, one lookup per
top-level declaration with an initialiser. A name is a process-wide interned
string, not a handle of the unit, so no dense index exists for it. It is the
only hash table of the slice.

**Step 3** (`resolve_exports`). The declaration of exports a finished top
level left undeclared, then `resolve_export_aliases` (its four arms in
order: a kept function alias, the self-alias target, a reusable same-name
binding, the alias chain), on the rows of the final block: the declarations
the fold added are statements of it. The lowering returns the final
statement list, the exported identifiers and the reserved names
(`Lowered::coerced`).

**Cost**, asserted at 10,000 in `export.rs`: 2 steps per row and 8 per
export for 10,000 exports of their own declarations (100,000 steps, no site
read); 10,000 references to one moved alias are read once each, in at most 3
steps per reference and 3 per row; rows and references are read again
without a heap allocation once the tables have their capacity.

**Read in the legacy code, not changed.** In
`move_same_name_export_alias_to_export_tail` a binding whose initialiser
resolves to a literal never moves: `blocked_by_literal_binding` (the kind is
not `Alias`) and `blocked_by_literal_alias_preserved_in_block` (the kind is
`Alias`) cover every kind. `blocked_by_direct_literal_reuse`,
`blocked_by_literal_alias_without_materialized_root` and the literal arm of
`later_toplevel_effect_allows_tail_move` are unreachable from it. The rows
implement the reachable behaviour: a literal stays.

#### T5 design

Status: design, written before any code. Part A moves P2's decision into the
lowering; part B is the naming log of section 2. "Read" marks a claim from
the cited code that no test asserts yet.

**(a) Where P2's decision is taken: once, when the unit's root block
exists** (`State::finish` in `bir/lower/mod.rs`, after the export coercion).
Not at the close of a run, for three reasons read from the code:

- P2 reads all declarations of a list, also those after the reference. A
  run is copied each time the lowering moves its statements ("T4c design",
  as built: one decision in five replaced), so at the close of a run the
  list a reference ends up in is not known. At the root every list is the
  one P1 receives.
- A statement's list is a node (`SBlock`, `aux` 0 for a body, 1 for an
  explicit block statement) and every node has its parent
  (`Bir::parents`, maintained by every constructor and edit). So "the
  bindings around a reference" is its ancestor chain: no position has to be
  recorded while lowering, and nothing is keyed by a list.
- Every binding has one binder node (`VarTable::binder`, written by
  `Bir::bind` where the node is built: `SDecl`, `SRest`, `JFun` for
  parameters, `SForRange`/`SForOf`/`SForAwaitOf`, `STry` for the catch
  variable), and every reference is a site (`Scope::sites`, written by
  `Bir::allocate`, chained per variable, cleared on release; T4a). Both are
  recorded where the lowering writes them, already.

*What P1 does to the lists P2 reads* (`Flatten` in
`js_pass_flatten_and_mark_dead.rs`; P2 runs after it). `block_items`
splices a block statement into the list it stands in, so the declarations
of an explicit block become declarations of the enclosing list and shadow
references of that whole list: `{ let location = 1; f(location) }
g(location')` has the global `location'` qualified only after P1. The
lowering writes explicit blocks (`explicit_block_from_list` in
`bir/j/norm.rs` and `bir/lower/cond.rs`). So the scope of a declaration is
its nearest enclosing block that is not an explicit block statement. P1's
other rules move no declaration: `Return(Cond)` and `Exp(Cond)` build lists
of `return`s and expression statements, the sequence rules build blocks of
expression statements. P1 drops references (a pure branch of a conditional
in statement position): a dropped reference needs no decision, and a
dropped function takes its sites with it. One input of P2 does depend on
what P1 drops: an imported module is a binding of the program only while a
`Qualified` reference to it is in the tree (`ReferencedNames`). The lowering
counts the references it built and released (a count per import, kept like
the counts of T1); a module whose last reference stands in a branch that
only P1 drops is counted as a binding by the lowering and not by P2. That
is the hazard of "T4c design" (b) again, it leaves with P1 at T6, and it
needs a module and a global of one printed name. Read, not tested.

*The decision.* A reference to a JavaScript global `g` (P2's `is_js_global`
on the identifier the variable prints as) is qualified when a binding that
prints as `g` (c) is: a declaration whose scope block is an ancestor of the
reference; a parameter of an enclosing function; the variable of an
enclosing `for` statement (the whole statement, bounds included); the catch
variable of a `try` whose handler block is an ancestor; a declaration in
any case of an enclosing `switch` whose case block, not its discriminant,
is on the path (the cases share a scope: P2's `add_switch_declarations`);
or an imported module with a live reference that is not a dynamic import.
`SForRangeExisting` binds no variable of its own: its target is declared in
an enclosing block, which covers the loop (read).

*Algorithm* (`bir/lower/globals.rs`), per name, with an epoch per name and
one mark per node (`u32`, dense by node, allocated the first time a unit
has a binding that prints as a referenced global):

1. One read per variable: those whose identifier is a JavaScript global and
   that have a site are the referenced globals. None: done. This is the
   only cost for a unit without such a reference.
2. One read per variable with a binder: its printed name looked up among
   the referenced globals' names. The key is an interned name: P2 relates
   a binding to a global through the spelling only, and a `Name` is a
   process-wide pointer without a per-unit index, so this is one table
   keyed by `Name` (its hash is stored in the name), built per unit that
   reaches step 2. No match and no matching import: done.
3. Per matching binding, one mark on its scope node: the block (through
   explicit blocks), the `switch` statement when the block is a case, the
   function, the loop, the handler block.
4. Per site of the name, its ancestors are read up to the first marked one
   (or the root), then the nodes passed are marked with the result, so a
   node is read at most twice per name whatever the number of sites below
   it. At a marked `switch` the walk continues when it arrived from the
   discriminant.

No statement body and no finished tree is walked to find a reference or a
binding; the walk is from a recorded site towards the root.

**(b) A copied or moved statement.** The decision is taken after every
copy and move of the lowering (`take_list`, `hold_run`,
`simplify_if_head`, `copy_j`), on the tree as it is then: a moved
statement has the parent it ended with, and the references of a copied
function are sites of their own, decided in the place the copy stands.
Nothing is decided per copy, and nothing is re-taken. For T4g: a splice
must run after this point (the decision is on the binding structure the
lowering wrote; P3 in legacy order runs after P2 on the whole program), or
call it first. The bit stays with the node when a splice moves it.

**(c) `printed_binding_name`** is `convert_ident_name` of the identifier's
name, and nothing for an identifier with the JavaScript flag. It reads the
name only (not the suffix the naming pass gives), so it is known when the
variable is created; it is read at the decision, through the variable's
origin (`vars.j_origin`: a copied binder prints as its original).

**The fact, not the qualified form.** The reference stays a `Var` node and
gets one bit (`aux`). Why not build `globalThis.name`: (1) the name is
decided after the node has been read by the lowering's own rules, which
must see what the legacy lowering sees, a variable (purity, delay safety,
`return_sites`); (2) the first comparison point of check mode prints the
program before any pass, where the legacy side has no qualified
reference. The reader of the bit is whoever turns `Bir` into JavaScript:
`bridge_j` today (it returns the handles of the marked references, and the
new side rewrites exactly those to `globalThis.name` before P1: one write
per marked reference, no walk), the builder of T6 afterwards. P1 reads a
qualified reference as it reads a variable (`expression_has_no_side_effects`
is true for a static index of a variable; no rule of `Flatten` matches
either); read, and the gate asserts it on the corpora.

**(d) The T4c comparison without P2.** `compare_decisions` needs the
program P3 receives. Legacy: P1, P2. New side: the marked references
rewritten, then P1: the same program, built by the path the new side takes
anyway, so the extra P1 and P2 on a copy that T4c added are gone. P2
changes no count of a declared variable ("T4c design" (b)), so the
comparison itself is unchanged. The report gains the number of qualified
references and the steps of the decision.

**(e) Part B: the naming log.** The oracle is `emit/naming.rs` run on the
program the lowering wrote (exported, before the passes); the log
describes that same tree.

| Event | Logged where | Answers |
| --- | --- | --- |
| `Declare(var)` | where an `SDecl` is written (binder before initialiser; after the reservation for a function declaration that is not eta-reduced) | hard example 2: the event carries its statement, and an event whose statement is not in the final list is skipped |
| `Params(function)` | where the `JFun` is built | - |
| `Enter(function)`, `Leave` | around the function's events: `Enter` carries the function's free-variable list | hard examples 1 and 3: the list is final at the close and is sorted by `order` there |
| `Binder(var)` | loop and catch variables, before their bodies | - |
| `Use(var)` | no event: a use names nothing unless it is the first print of a free variable, which `Enter` reserves | hard example 1 |

The free variables of a function: every site built between the function's
entry and its close whose variable has no binder inside, with one
membership bit per variable (dense, cleared through the list at the
close). A function's list is added to its parent's at the close (the
oracle's `used.extend(free[f])`). Replay (`fn replay` in
`emit/naming.rs`) reads the events of one scope in final statement order
through the existing `Group` and `Scope` tables and writes a name per
variable; check mode compares that table with `Names::printed`.

Open before code, to be settled by the first comparison run and written
into "T5 as built": the oracle skips statements and branches the printer
omits (`walk::prints_declaration`, `omitted_expression`, `else_omitted`,
`tail_effect`, the eta form of `function_form`); each is a shape test on
the finished statement that the log has to carry as a bit of the event or
decide at replay.

#### T5 as built: part A (part B is a skeleton, 11.7)

`bir/lower/globals.rs` (`decide`, called from `State::finish`), the bit
(`Bir::qualify_global`, `Node::var_qualified`), the count of live
references per import (`Scope::import_reference`, from
`Bir::register_kind`), `bridge_j::export_lowered` and `bridge_j::qualify`,
and the gate (`lam_compile.rs`: the new side qualifies, flattens, compares
the step A decisions on that program and continues with
`finish_flattened_output`; `apply_external_shadow_pass` is called by the
legacy side only). As designed, with one addition: the printed text of a
qualified reference drops the reference's comment and location, as the
legacy pass does (`JsArena::overwrite_expr`).

Check mode, zero text differences at both comparison points:

| Corpus | Units | References qualified (units) | Steps of the decision | Step A differences |
| --- | --- | --- | --- | --- |
| runtime | 113 | 0 | 2,734 | 0 |
| tests/tests | 855 (736 in the ratchet's count) | 29 (6) | 23,992 | 0 |
| fixtures | 609 | 0 | 22,542 | 0 |
| the application | 3,848 | 29 (16) | 478,518 | 0 |

`scripts/test_backend_coverage.py` passes with the ratchet unchanged.
Tests: the two inlining cases and one rule per kind of binding in the
oracle form (`bir/lower/oracle_tests.rs`, from
`the_lowering_decides_the_shadowed_global_the_tail_call_pass_would_hide`
on: the new side without pass 2 prints what the legacy side prints with
it); steps at 10,000 references, at 10,000 bindings and at depth 10,000,
zero allocations on a second decision, sizes (`globals.rs`).

Not done in part A: the instruction counts, the test of the hazard of (a)
and a rule test for `SForRangeExisting`; all three are done in "T5 as
built: part B".

#### T5 as built: part B (stopped at step 4: two design gaps)

Built, at the skeleton's signatures, costs, sizes and tests (11.7 steps 1
to 3): `Log::declare`, `binder`, `reference`, `enter` and `leave`
(`bir/lower/names.rs`); `emit::naming::replay` through the pass's `Names`
tables; `emit::naming::compare_with_pass`. The eight tests of the log and
the comparison test pass. To meet the signatures of `enter` and `replay`,
which read a function's parameters from `&VarTable`, the function headers
and the tail-call rewrite's indirect parameter runs moved from `Pools` to
`VarTable` (one owner; `Bir::function` reads the same storage). The warm
replay is allocation-free for declarations: `Names::reset` empties the
program scope's groups in place (a group is a persistent map, so dropping
and recreating one allocates).

Not built: step 4 (the lowering logs) and step 5 (check mode), because of
the two gaps below; the module, `replay` and `compare_with_pass` are still
compiled for tests only, and no corpus was compared. The printer shape tests
of step 5 (`prints_declaration`, `omitted_expression`, `else_omitted`,
`tail_effect`, the eta form) were not placed for the same reason.

**Gap 1: one membership bit and one bound bit per variable do not give the
free variables of a function nested in a function.** The bits are set by
the innermost open scope and cleared through its run at its close, so the
bits an enclosing *function* set are still set while an inner function is
open. A reference in the inner function to a variable the enclosing
function referenced or declared finds its membership bit set and is not
added to the inner run; a reference to a parameter of the enclosing
function finds the bound bit `enter` set and is read as bound at the inner
close. Either way the variable is missing from the inner free list, which
`Names::analyze_fun` has. The shared bound bit also errs the other way
(read from the code, not tested): in `let f = () => { let rec g = () => g(); g() }`
the bit `declare` sets for `g` in `f` is cleared by `g`'s own close, because
`g` referenced itself, so `f`'s later reference to `g` reads `g` as free in
`f`. The redesign must cover both directions. The program scope is not affected (it keeps no
run), so every skeleton test passes: they nest functions in the program or
capture program-level variables only. Reproduction, the events the
lowering would log for

```rescript
let f = p => { let v = ext(p); let g = () => { let v = ext(v); ext(v) }; g }
```

`enter(f)` (bound: `p`), `declare(f)` (the binder), `declare(v)` (member,
bound), `reference(p)` (member), `enter(g)`, `declare(g)` (the binder),
`reference(v)` (the outer `v`, in the initialiser: its member bit is set by
`f`, so it is not recorded), `declare(v')` (member, bound),
`reference(v')`, `leave(g)`: `free_variables(g)` is empty, the pass gives
`[v]`. The replay then reserves nothing at `g`'s `Enter`, `g`'s scope does
not inherit the group of `v`, and the inner declaration is named `v`
(`let v = ext(v)`, a reference before its own declaration) where the pass
names it `v$1`. With the costs of the skeleton (`reference`: one bit test
and one push the first time; `enter`: two pushes and one bit write per
parameter) there is no way to tell "in the innermost run" from "in an
enclosing run"; telling them apart in constant time needs, per variable,
the scope that last recorded it and the scope that binds it (two dense
`u32` rows by `VarId`, scopes numbered in stack order), which is not "one
membership bit per variable". The example is the ignored test
`a_function_nested_in_a_function_captures_a_local_of_the_outer_one`
(`bir/lower/names.rs`), which asserts the correct result (`[v]`, and
`v$1` for the inner declaration).

**Gap 2: the lowering has no statement when a function's scope opens.**
`Log::enter(function, statement, vars)` has to be called before the
body's references are built, so that `reference` puts them in its run, and
the binder's `Declare` has to be the event two after `Enter` (the replay's
rule and the tests). Three construction sites contradict that:

1. The body before the `JFun` before its statement: `State::enter`
   (`bir/lower/mod.rs`, `View::Fun`) returns `Resume::Fun`, the body is
   lowered as its child (`expression_children`, `bir/lower/expr.rs`),
   `finish_expression` (`bir/lower/expr.rs`, `Resume::Fun`) then takes the
   body's list and builds the `JFun`, and only after that does
   `State::leaf` (`bir/lower/mod.rs`, `Cont::Declare`) write the `SDecl`
   (or an expression statement holds it). No node of the statement exists
   at `enter`, and a `Declare` logged where the `SDecl` is written follows
   the body's events.
2. The `one_unit_arg` header replacement: `finish_expression`
   (`bir/lower/expr.rs`, `Resume::Fun`) allocates a new header without
   the unit parameter after the body, so the `FuncId` logged at `Enter` is
   not the printed function's and its `Params` include the unit argument.
3. The tail-call aliases: `loop_function_body` (`bir/lower/tail.rs`)
   declares `let x = _x` after the body was lowered, while the aliases
   print before it.

Closing this needs a mechanism the design does not have, for example
events logged with a provisional statement that the write of the statement
fills in, and `Params` logged at the close. Finding 2 has no test: an
assertion about the log of a lowered Lambda needs step 4 to exist.

Open, read from the code and not tested:

- A warm replay of a log with functions still allocates (`replay` in
  `emit/naming.rs`, through `Names::enter`: a new `Scope` table per
  function, and an assignment in an inherited group copies its persistent
  node).
- Raw JavaScript names are not passed to the replay (`ProgramNames`,
  `replay`): the pass skips them when it picks a suffix (`Names::raw`, read
  in `Names::assign`).
- The `this` of a method is named by the pass only when the body uses it
  (`Names::method_this_used`, read in `Names::function`); the replay's
  `Params` arm names every parameter, and the log keeps no record of that
  use after the close.

Part A leftovers, done: the hazard of (a) is pinned
(`a_module_whose_only_reference_the_flatten_pass_drops_still_shadows_the_global_of_its_name`
in `bir/lower/oracle_tests.rs`: the new side prints
`ext(globalThis.Other)`, the legacy side `ext(Other)`, so the hazard is
real, not only read), and `SForRangeExisting` has a rule test
(`a_loop_over_an_existing_variable_binds_nothing_and_the_declaration_of_its_target_covers_it`
in `globals.rs`; the lowering never builds that statement, only the import
of JavaScript into `Bir` does, so the test builds `Bir` directly).

Instruction counts of a clean build of `tests/tests` (743 modules), release
binaries (fat LTO, `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1`), one worker
thread, cachegrind, the smallest of the runs; each line is one run of
`scripts/compare_build_instructions.py --base A --head B --runs N`, both
sides in worktrees at paths of equal length ("this head" is d2da40cff, the
last commit that changes code):

| Mode | Compared | Runs | First | Second | Change |
| --- | --- | ---: | ---: | ---: | ---: |
| default | `be1b3a482e` / this head | 3 | 4,042,502,066 | 4,044,423,272 | +0.048% |
| default | skeleton head `1da0feb06` / this head | 3 | 4,045,205,646 | 4,045,800,056 | +0.015% |
| `RESCRIPT_BACKEND=check` | `be1b3a482e` / this head | 2 | 20,614,165,045 | 20,572,095,782 | -0.204% |
| `RESCRIPT_BACKEND=check` | skeleton head `1da0feb06` / this head | 2 | 20,574,784,559 | 20,570,457,316 | -0.021% |

Runs of one binary spread by up to 5.4 M (0.13%) in the default build, so
both default differences are noise: nothing part B adds runs by default
(the log, the replay and the comparison are compiled for tests only, and
`Bir` is built in check mode only). Part A saves 0.2% of the check build
(the external-shadow pass and the extra flatten and shadow passes on a copy
are gone from the new side). The application was not measured: no code it
runs by default changed.

#### T5 part B as redesigned

Status: built ("T5 part B as built", after this section). This section is
the design the three slices were built from; where the build changed it, the
statement here is corrected and the reason is in "as built". Reviewed once:
see "Decided in review" at the end of this section. "Verified" below means
read in the code at the cited place or pinned by a test; "read" means read
only. The three gaps of "T5 as built: part B"
were checked against the code and are as described:

- G1 (a): `Log::reference` joined a run only when the variable's one
  membership bit was clear, and `Log::leave` cleared the bits of the
  innermost run only, so a bit an enclosing function set hid the reference
  (the deleted `names.rs`, `join` and `leave`). G1 (b): `declare` set the one
  bound bit for `g` in `f`, and the close of `g`, which had `g` in its own
  run, cleared it.
- G2: `State::enter` returns `Resume::Fun` before the body
  (`bir/lower/mod.rs`); `finish_expression` (`bir/lower/expr.rs`,
  `Resume::Fun`) takes the body's list, calls `loop_function_body`
  (`bir/lower/tail.rs`: the header's parameters become copies and `let x =
  _x` is written in front of the lowered body), allocates a new header when
  `one_unit_arg` is set, and only then builds the `JFun`; the `SDecl` is
  written after that (`State::leaf`, `Cont::Declare`).
- G3: `replay` went through `Names::enter` (a new `Scope` with a hash map
  per function, persistent maps copied on assignment); it was given no raw
  names; its `Params` arm named every parameter.

Found while verifying, not in the list:

- G4. **A stored event has no stable place.** A run is copied again each
  time the lowering moves its statements (one decision in five replaced,
  "T4c design"), lists are built outside `take_list` (`simplify_if_head`,
  `cond.rs`, `external.rs`, `coerced_list`, `loop_function_body`), a branch
  moved after its guard changes the order of two lists, and `copy_j` copies a
  closed function with fresh binders. Events in construction order would
  need a splice at each of these.
- G5. **Imported modules are free variables.** The pass counts a
  `Qualified` reference as a use (`analyze_expr`), so a function that reads
  module `M` inherits the names of `M`'s base. The log had variables only.
- G6. **The cached bound of a range loop takes a name** (`Names::finishes`,
  `base_finish` under the suffix rule). The log had no event for it. Pinned:
  `the_cached_bound_of_a_range_loop_takes_a_name_in_its_scope`.
- G7. **A reference released before the close.** The membership bit stayed
  set when the constructors folded the read away; the pass, which runs on
  the finished tree, does not see it (section 2, the conditional capture).
- G8. **Two function literals in one statement.** When both first name a
  variable they capture (declared after them, the same base), the one
  printed first gets the base. Pinned:
  `two_function_literals_of_one_statement_name_what_they_capture_in_print_order`.
- G9. **Functions the lowering builds itself** (`call.rs`, `ffi_args.rs`,
  `import.rs`: a `JFun` not lowered from a source `Fun`) had no `enter`.
- G10 (found in review). **An expression built before the scope opened
  moves into the function.** Two of the three sites of G9 build a function
  around expressions the caller lowered earlier: `apply_with_arity`
  (`bir/lower/call.rs`, the eta-expansion of a strictly pure partial
  application) returns `param => callee(remaining..., param)` with `callee`
  and `remaining` already built; `external_dispatch`
  (`bir/lower/ffi_args.rs`) makes its argument the scrutinee of the `switch`
  inside `(() => { switch (arg) ... })()`. The sites of those expressions
  were recorded before any `open`, between the sites of statements the
  argument lowering hoisted (which stay outside), so no site range holds
  them: the close finds no reference, the free list is empty, and a fresh
  `param` can take the name of a local the moved argument reads. Pinned on
  the pass:
  `a_function_inherits_the_names_of_what_an_expression_moved_into_it_reads`
  (`param$1`). `wrap_then_path` (`bir/lower/import.rs`) is not affected:
  its body is built from its own parameter, and `import` stays outside.

**(a) The data.** The idea on record (a scope row per variable, provisional
statement slots, parameters at the close) is adopted for the row and the
parameters and replaced for the slots: **no event is stored**, so there is
no slot to fill. The reason is G2 and G4 together: every stored event needs
a statement, the statement is written after the event's time, and it is
then moved, copied or dropped. What an event would say is already in the
tree: a declaration statement holds its variable, a loop its variable, a
function literal its header. The replay reads it there.

| Name | What it is | Bytes | Written where |
| --- | --- | ---: | --- |
| naming event | Not stored. `Declare`, `Binder`, the cached bound: read from the statement the replay reaches. `Enter`, `Params`, `Leave`: a scope row | 0 | - |
| `ScopeRow` | One function literal: the printed header, its free list as a run of `Log::free`, flags (`CLOSED`, `ETA`, `FIRST_READ`, `COPY`) | 16 | `names::open` pushes it (`State::enter`, `View::Fun`; the three sites of G9); `names::close` fills it (`finish_expression`, after the `JFun` is built) |
| `FreeRef` | One entry of a free list: a variable or an import | 4 | `names::close` |
| `Place`, per variable | Home: the row whose scope was innermost when the binder was written, for a parameter the row that closed with it. Seen: the row that last put the variable in its run (deduplication) | 8 | `Log::bind` from `Bir::bind`; parameters and seen in `names::close` |
| seen, per import | The row that last put the import in its run | 4 | `names::close`, `names::adopt` |
| `Child` | A closed direct child of an open scope: its site range and its row | 12 | `names::close` |
| row of a header | Dense by `FuncId` | 4 | `names::close`, `Log::copied` |
| `Open` | An open scope: its row and where its sites, run and children start | 16 | `names::open` |
| reference | To a variable: the site `Scope::site` already records (T4a). To an imported module: a site of the same kind (`Scope::import_site`), 8 bytes a reference | 0 and 8 | `Bir::allocate` |
| adopted expression | Nothing stored: `names::adopt` puts what a moved expression reads in the open scope's run; `Log::adopted_nodes` counts the nodes read | 0 | `names::adopt`, at the two sites of G10 |
| `Subject` | An identifier handed to the tables: slot, stamp, name | 16 | built by the replay per call |
| `GroupRow`, `Saved`, `Level` | The suffix table of a base, a saved row (with the `born` mark of its group), a scope's undo marks | 16, 24, 12 | `emit::naming::Tables` |
| `Frame` | One level of the replay's walk over statement lists | 12 | `names::replay` |

Every size is pinned (`row_sizes`, `replay_sizes`). The value passed down
the replay's walk is a `Frame` (12 bytes); the value passed to a table call
is a `Subject` (16).

*No body is walked for a name.* The free variables and imports of a
function are read from the sites built while its scope was open: at the
close, the sites since the scope opened, without the ranges of its closed
children, one step each; a closed child that is still live gives its free
list. A site is read at one close. Where a reference is built, its site is
pushed and nothing else is done, with one exception: an expression that was built before its
function's scope opened is read once where it moves in (`names::adopt`,
G10). The first pass cannot record that fact: when the argument is lowered
nobody knows it will end inside a function, and a site range over it would
include the statements hoisted out of it. This is one of two places where
an expression is read for a reference, and `adopted_nodes` reports what it
costs; the second is the JSX rule of "T5 part B as built", item 4 (in a
unit that preserves JSX only). The replay reads statement lists and scope rows, never an
expression: a function literal inside an expression is reached from its
row, by reading the ancestors of its node up to its statement (the form of
`globals::decide`: from a recorded place towards the root, a node read at
most twice).

*What the replay does read: one step per statement of the final lists.*
The rule: this is not a second pass for a fact the first pass could record,
because the fact is the final statement order, which no construction step
has (G4):
`close::decide` already pays one step per statement per copy for the same
reason. The alternative that avoids the spine (an event chain per
statement, relinked wherever a list is built) costs one step per statement
per copy, more than one step per final statement, and breaks at every list
built outside `take_list`. Section 2's "one event per declaration and
function" becomes "one step per statement and per function"; the naming
pass reads every node.

*The tables.* The pass's `Names` keeps persistent maps per scope. The
replay gets tables of its own (`emit::naming::Tables`): one `GroupRow` per
base with the depth of the scope that has it, and an undo stack. A group
exists in the current scope when its depth tag is the current depth;
entering a function re-tags the groups of its environment (saving the row
before); a group not inherited keeps its tag and so reads as empty; leaving
restores. "Name `base$k` is taken" is `k < next` and not skipped, so no set
of names is kept. Two hash structures remain, each with its reason in the
code: base spelling to group (read once per variable, the answer kept
dense by slot) and the raw names (read per suffixed candidate). `Names` is
not touched: it is the oracle.

**(b) The gaps.**

| Gap | Mechanism | Test (ignored until built unless marked) | Cost |
| --- | --- | --- | --- |
| G1 (a) | The references of a scope are its own sites, read at its close; an enclosing scope's state is not consulted. Free means: home is not this row | `a_function_nested_in_a_function_captures_a_local_of_the_outer_one`; names: `..._inherits_the_names_of_the_outer_local_it_captures`. Runs today on the pass: the test of the same name in `emit/naming.rs` | one step per site, once |
| G1 (b) | The home of `g` is written when its declaration is written, after `g`'s own close, in the scope open then (`f`); `g`'s close found no home and so lists `g` as free | `a_recursive_inner_function_is_free_in_itself_and_bound_where_it_is_declared`, `..._reserves_nothing_in_the_program`. Today: `a_recursive_inner_function_is_not_free_in_the_function_that_declares_it` | one write per binder |
| G2 header | `close` takes the header of the built `JFun`; the row is found by that header | `a_header_replaced_after_the_body_is_the_header_of_the_row`; `the_naming_log_agrees_on_a_function_whose_unit_parameter_is_dropped` | none |
| G2 aliases | The alias declaration is written before `close`, so its binder's home is the function; the copies are parameters at the close | `the_aliases_of_a_tail_call_loop_are_bound_in_their_function`; `the_naming_log_agrees_on_the_aliases_of_a_tail_call_loop` | one write per parameter |
| G2 statement after its events | No event: the replay reads the final lists | `a_statement_is_named_where_it_stands_at_the_end` | one step per final statement |
| G3 warm replay | `Tables` (above) | `a_warm_replay_of_a_unit_with_functions_allocates_nothing`, `warm_tables_allocate_nothing` | an undo push per assignment |
| G3 raw names | `Program::raw`, filled where `globals::decide` already reads every variable once (its step 1) | `a_suffix_skips_a_raw_javascript_name_of_the_program`, `the_tables_skip_other_bases_and_raw_names`. Today: the test of the first name in `emit/naming.rs` | one read per variable, already paid |
| G3 `this` | `FIRST_READ`: at the close, the first parameter of the function is in the run (recorded for every function: one becomes a method after its close) | `the_this_of_a_method_is_recorded_as_read_only_when_the_body_reads_it`, `..._is_named_only_when_the_body_reads_it`. Today: the test of the second name in `emit/naming.rs` | one comparison per run entry |
| G5 | `FreeRef` holds an import; a module reference has a site, read at the close like a variable's | `an_imported_module_is_free_in_every_function_around_its_reference`, `a_module_reference_released_before_the_close_is_not_free` | one push per module reference built, one write per release, one step at the close |
| G6 | `Tables::synthetic`, called by the replay at a range loop whose bound is cached | `a_synthetic_name_takes_a_suffix_in_its_scope`. Today: the pass test of G6 | as a new name |
| G7 | A released site has no node; `close` skips it | `a_reference_released_before_the_close_is_not_free` | none |
| G8 | The replay reads the literals of a statement in closing order and counts every reservation that first names a variable in a statement with more than one literal (`ambiguous_orders`); the gate requires zero | `two_function_literals_of_one_statement_are_replayed_in_closing_order_and_counted` | one counter |
| G9 | `open` and `close` at the three sites | the oracle tests, through `names_agree` | - |
| G10 | `names::adopt(bir, node)`, once per moved expression between `open` and `close`: the subtree is read once; a `Var` or a module reference joins the open scope's run; a closed function literal is not entered, the free entries of its row join the run | `an_expression_built_before_the_scope_opened_is_adopted`, `the_fresh_parameter_of_a_partial_application_does_not_take_the_name_of_an_adopted_local`, `an_adopted_function_literal_gives_its_free_entries_and_is_not_entered`, `a_function_literal_inside_an_adopted_expression_is_replayed_where_it_stands`, `the_scrutinee_of_a_dispatch_function_is_adopted`, `a_module_reference_in_an_adopted_expression_is_free_in_the_function`, `ten_thousand_adopted_nodes_cost_one_step_each_and_a_literal_its_free_entries`; through the lowering: `the_naming_log_agrees_on_a_partial_application_whose_argument_reads_a_local`, `..._on_a_dispatch_function_whose_scrutinee_reads_a_local`. Today: the pass test of G10 | one step per node of the moved expression outside function literals, one per literal and per free entry of it; adopted nodes <= nodes of the moved expressions; the corpus total is reported, not bounded |

Limits, stated and counted, not solved ("as built" has the list that holds
now):

- A reference or a statement released inside a function after its close
  leaves the free list as it was. Nothing in the lowering does that today
  (the four corpora are at zero); the splice of T4g will. Visible as
  `free_differences`.
- A use names nothing in the replay. The pass names a variable at a use
  when it is not visible yet; that is a use before the declaration in the
  same scope outside a closure, which the lowering does not write (read).
  Counted: `unnamed_references`.
- G8's order. In `Bir` the print order of two literals of one statement is
  not recorded; the count says whether it ever matters.

**(c) Copies and moves.**

- *A statement run copied into a list, again or elsewhere*
  (`take_list`, `hold_run`, `simplify_if_head`): nothing. The log holds
  nothing per statement.
- *A statement dropped*: nothing; it is in no final list. A function
  literal released with it has no owner node, and its row is skipped. When
  it is released before the function around it closes, it gives that
  function nothing (a closed child gives its free list at the enclosing
  close, and only when it is live). Released after that close, its free
  variables stay in the lists of the functions around it (the limit above).
- *A closed function copied* (`copy_j` through `Bir::copy_subtree`): the
  copy has a new header; `Log::copied` gives it a row that shares the
  source's free run. The copy's binders print as their origins, so the
  shared list names the right identifiers. The copy's binders are bound
  while another scope is open and get that scope as home: harmless, they
  are referenced in the copy only, and the copy's rows are final.
  `a_copied_function_gets_a_row_that_shares_the_free_list_of_its_source`.
- *Tail-call inlining decided per copy* (`close::decide`): reads counts,
  writes decisions; it does not touch the log. When T4g performs the
  splice, the callee's row is released with its literal and its body's
  statements stand in the caller: the replay names them there. The free
  lists of functions inside the spliced body are unchanged (their free
  variables are the callee's parameters, now declared or substituted in the
  caller: T4g must check substitution, see (g)).
- *A body imported from another module* (`inline_external_function`): the
  fragment is imported into the source arena and lowered by the normal path
  in the scope that is open, so its functions open and close like any
  other. The log's dense rows grow with the variables and headers made
  during the import (`Log::variable`; rows by header grow on demand).
  `the_naming_log_agrees_on_a_body_imported_from_another_module`.

- *An expression built before a scope opened, moved into its function*
  (G10): `names::adopt`. What each party sees afterwards:
  - the new function: the moved references in its run, so free unless it
    binds them (it binds only its fresh parameters);
  - the enclosing scope: nothing more. It reads the moved references as its
    own sites at its close, and takes the new function's free entries
    there; both put the same variables in its run, which is what the
    pass computes (`analyze_expr`, `ExprKind::Fun`:
    `used.extend(free[f])`). A variable put in a run twice is written once:
    the free list is written without duplicates after the sort;
  - a closed literal inside the moved expression: its row and free list are
    final and unchanged. Its site range stays among the enclosing scope's
    closed children (those sites were read at the literal's own close). No
    row has a parent, so nothing is re-parented: the replay's prelude finds
    the literal by its node's ancestors, and the first statement above it
    is now the `return` inside the new function, so it is entered inside
    the new function's scope and inherits from it.

**(d) The oracle.** Both sides print the same tree, the lowering's own
program before the JS passes with its module list filled in (`new_before`),
from a table of names by identifier. So "every printed identifier of every
binder and reference, in order" is equal exactly when, per unit:

1. every variable and module the replay names has the pass's name for its
   identifier (a variable through its origin), and every identifier the pass
   names, stamp zero aside, is named by the replay (`name_differences`);
2. the cached bounds have the same spellings (`finish_differences`);
3. `ambiguous_orders` and `unnamed_references` are zero.

`free_differences` (the free lists as multisets of identifier sequences,
live copies included on both sides) is required to be zero as well: a wrong free list changes a
name only when a local of the same base exists, so the names alone would
hide it. A unit the pass does not support is not compared and is counted.

Zero on all of: the runtime library (113 units), tests/tests, the fixtures
corpus, and a 3,735-module application. Run, with the replay changing no
output (its names are compared and dropped; `new_before` is printed by the
pass as today):

```sh
python3 scripts/test_backend_coverage.py     # runtime, tests/tests, fixtures
RESCRIPT_BACKEND=check RESCRIPT_BACKEND_STATS=$DIR <a build of the corpus>
find $DIR -name '*.json' | xargs cat | jq -s '[.[] | .. | objects | (.name_differences? // 0) + (.finish_differences? // 0) + (.free_differences? // 0) + (.ambiguous_orders? // 0) + (.unnamed_references? // 0)] | add'
```

The last line prints 0. The first passes with the ratchet unchanged.
`adopted_nodes` is reported per corpus beside it (the sum over units); it
has no bound.

**(e) The slices.**

| Slice | Builds | Un-ignores | Lines | Needs |
| --- | --- | --- | ---: | --- |
| T5b-1 | The log: `Log`, `open`, `close`, `adopt`, `eta_shape`, the hooks in `Bir` (`new_var_id`, `bind`, `register_kind`, `copy_subtree`) | the 17 tests marked `T5b-1 build` | 400 | - |
| T5b-2 | `emit::naming::Tables` and `names::replay` | the 20 tests marked `T5b-2 build` | 550 | T5b-1 for the replay's tests; the tables alone need nothing |
| T5b-3 | The wiring: `open`/`close`/`adopt` in the lowering, the replay at `State::finish`, `free_lists`, `compare_with_pass`, check mode, `names_of`, the gate on four corpora, the measurements | the 7 tests marked `T5b-3 build`; `names_agree` in `compare_oracle` | 400 | T5b-1, T5b-2 |

T5b-1 and the `Tables` half of T5b-2 run in parallel (different files:
`bir/lower/names.rs` and `bir/edit.rs` against `emit/naming.rs`). The
replay half of T5b-2 follows T5b-1. T5b-3 is last.

**(f) Build prompts.** Each was issued verbatim and is kept as issued; the
names in them (`Log::import_reference`, `THIS_USED`, `Log::new`) are those
of the skeleton.

Common to the three (part of each prompt):

> Repository: `compiler-rust/`. Read first: AGENTS.md; THREE_TREES section
> 2 and 11.4 "T5 part B as redesigned"; the header of `emit/naming.rs`;
> `bir/lower/names.rs` whole. You change no signature, no doc-comment cost,
> no pinned size and no test. If one cannot be met, stop: commit what
> passes, and report the function, the test, and the smallest input that
> shows it. Moving code, splitting a function, adding a private helper or a
> private field is yours to do; say what you moved in the commit message.
> The intent is stated in each doc comment; the layout of the code is
> yours. Counts failure: an `allow` attribute; a hash map or set other than
> the two in `Tables`; an allocation per reference, per statement or per
> scope once the vectors are warm; a walk over an expression to find a
> reference, a binder or a function, with one named exception:
> `names::adopt` reads an expression that was built before its function's
> scope opened, once, and nothing else may; an ignored test other than
> those of a later slice; a number you did not measure. A step-count
> constant in a test was derived on paper: if the body that meets the doc
> comment's cost gives a count that differs from a test's by a fixed
> amount, do not adjust the body or the test: report the two measured
> counts and the relation between them, and stop. Every commit:
> `cargo check --all-targets --manifest-path compiler-rust/Cargo.toml`
> prints no warning; `cargo test --manifest-path compiler-rust/Cargo.toml
> --lib bir::lower::names emit::naming` passes.

T5b-1:

> Task: build the naming log. First edit: `Scope::new` in
> `bir/lower/scope.rs` builds `names` with `Log::new(variables)`. Then the
> bodies marked `todo!("T5b-1")` in `bir/lower/names.rs`, and four calls in
> `bir/`, each inside the existing `if let Some(scope) = &mut self.js_scope`
> of its function or a new one of that form: `Log::variable` beside
> `Scope::push` (`Bir::new_var_id`); `Log::bind` in `Bir::bind` for every
> binder of a node that is not a function literal; `Log::import_reference`
> in `Bir::register_kind` for a `JQualified` that is added; `Log::copied` in
> `Bir::copy_subtree_recording` where a function header is copied. Remove
> `#[ignore = "T5b-1 build"]` from the 17 tests in `bir/lower/names.rs`.
> Criteria: those 17 pass; `rg -n 'T5b-1' compiler-rust/src` is empty;
> `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::` passes
> (the hooks run in every lowering test). `Log::steps` is asserted as
> relations between two sizes by the tests; do not add a constant to make
> one pass.

T5b-2:

> Task: build the naming tables and the replay. First edit:
> `Tables::begin` in `emit/naming.rs`. Then the other bodies marked
> `todo!("T5b-2")` there (commit 1: remove the ignore from the 7 tests of
> `emit::naming::replay_tests` marked `T5b-2 build`), then `names::replay`
> in `bir/lower/names.rs` (commit 2: remove it from the 13 tests there).
> The rule of each `Tables` method is the method of `Names` its doc comment
> names: the two must give the same names; `Names` is not changed.
> Criteria: the 20 tests pass; `rg -n 'T5b-2' compiler-rust/src` is empty;
> `rg -n 'im_rc' compiler-rust/src/emit/naming.rs` shows `Group` only.

T5b-3:

> Task: wire the naming log into check mode. First edit: remove
> `#[cfg(test)]` from `mod names` in `bir/lower/mod.rs`, from the `names`
> field of `Scope`, and from `Subject`, `Tables`, `Printed`, `FreeLists`,
> `NameStats`, `compare_with_pass` and their helpers in `emit/naming.rs`.
> Then, one commit each: (1) `names::open` in `State::enter` (`View::Fun`)
> and `names::close` in `finish_expression` (`Resume::Fun`) after the
> `JFun` is built; the same pair around the three functions the lowering
> builds itself: `wrap_then_path` (`import.rs`), `open` before
> `fresh_variable("m")`; `apply_with_arity` (`call.rs`), `open` before the
> first `fresh_variable("param")`, then `names::adopt` of `callee` and of
> each node of `remaining`, in that order, before the call node is built;
> `external_dispatch` (`ffi_args.rs`), `open` before the first `return` of
> a case is built, then `names::adopt` of `arg`. `close` after the `JFun`
> in each. These are the only two places that call `adopt`. If you find
> another place where a node built before `open` ends inside a function
> (search: every `View::JFun {` construction and every edit that attaches
> a node below a `JFun` after its `close`), do not add a call: stop and
> report the site and a Lambda that reaches it. (2) `Program::raw` collected in
> step 1 of `globals::decide`; `names::replay` at `State::finish` after
> `globals::decide`; its `Printed` and `Replayed` carried in `Lowered`.
> (3) `free_lists`, `compare_with_pass`, `names_of` in
> `bir/lower/oracle_tests.rs`; remove the 7 ignores; call `names_agree` from
> `compare_oracle` for the unit context. (4) Check mode
> (`lam_compile.rs`, where `new_before` is built): `compare_with_pass` on
> `new_before`; the fields of `NameStats` and `Replayed` and
> `Log::adopted_nodes` flat in the `lower` report; a unit the pass does not support counted as
> `names_uncompared`. The replay's names are not used for output. (5)
> Measurements and "T5 part B as built" in THREE_TREES 11.4.
> Criteria: `cargo test --manifest-path compiler-rust/Cargo.toml` passes;
> `rg -n 'T5b-' compiler-rust/src` is empty; `rg -n 'cfg\(test\)'
> compiler-rust/src/bir/lower/names.rs` shows the test module only;
> `python3 scripts/test_backend_coverage.py` passes with the ratchet
> unchanged; the `jq` sum of (d) is 0 on the runtime library, tests/tests,
> the fixtures and the application, with compared and uncompared units per
> corpus reported, and `adopted_nodes` summed per corpus (reported, no
> bound); instructions of a clean build of tests/tests
> (`scripts/compare_build_instructions.py --base <trunk> --head <yours>`):
> the default build within 0.1%; with `RESCRIPT_BACKEND=check` reported as
> measured, with the share of `names::` functions from the cachegrind
> output. When the sum is not 0: reduce one unit to the smallest Lambda,
> add it to `oracle_tests.rs` through `names_agree`, and decide only
> between "a body of T5b-1 or T5b-2 is wrong" (fix it) and "the design
> does not cover it" (commit the test ignored with the reason, report,
> stop).

**(g) What T6 needs, and 11.8.** T6's builder writes oxc nodes, which have
no parent link. From the naming log it needs:

1. `open` and `close` unchanged: they read sites and headers, not nodes.
   The site of a reference must stay the place a release clears.
2. The replay's two reads of the tree behind one interface: the statements
   of a list in order with, per statement, its kind, its binders and its
   child lists; and the statement a function literal stands in. In `Bir`
   the second is the walk over ancestors. With oxc nodes the builder knows
   it when a statement constructor receives its expressions: the handle of
   an expression carries the first and last literal inside it (two row
   numbers, chained in the order the builder attaches them), which also
   gives the print order G8 lacks, so `ambiguous_orders` goes away.
3. `Printed` as the table `oxc_codegen` reads: a symbol id per binder and
   per reference equal to the variable's index, so that
   `get_binding_identifier_name` reads `Printed::names`. The cached bound of
   a range loop needs a symbol of its own per loop.
4. The replay after the last decision that removes or moves a statement
   (T4g's splice, T4d, T4e, the shake): names are assigned once, on the
   final lists. Each of those slices must say what it does to free lists
   (a spliced callee's parameters are substituted or declared in the
   caller; a dead declaration's last capture goes).
5. Exactly one statement-level naming walk: the replay over the builder's
   lists. T6 adds no other walk for names, and no walk over expressions
   besides `adopt` (which it may drop if an expression's handle carries
   what the expression reads; that is T6's design to decide).

11.8 as written, paragraph by paragraph:

| Paragraph of 11.8 | Verdict |
| --- | --- |
| Opening ("To be issued when T5 is complete ... two design gaps") | Corrected: issued when T5b-3 is merged; the gaps are closed by this section |
| Task and preconditions | Corrected: the precondition on names is "the `jq` sum of (d) is 0 on the four corpora and `rg -n 'T5b-' src` is empty"; `name_differences` alone is not the gate |
| Read first | Corrected: add "T5 part B as redesigned", (g); "both T5 as built parts" stays |
| Step 1 (a) to (c), (e) | Kept |
| Step 1 (d), identifiers | Corrected: not open. The symbol id is the variable's index; names come from `names::Printed`; the design has to answer only how a statement constructor hands the log the literals of its expressions (point 2 above) and the symbol of a cached bound |
| Steps 2 and 3 | Kept |
| Step 4 | Corrected: add "the replay reads the builder's statement lists; the ancestor walk and `Scratch::marks` are deleted" |
| Step 5 | Kept |
| Step 6 | Corrected: add the naming tests of this section run against the builder's lists |
| Step 7 | Kept |
| End state | Corrected: add "`rg -n 'ambiguous_orders' src` is empty" and "the naming pass (`Names::collect`) is called by the legacy side and by check mode only" |
| Shortcuts | Kept; add "a second naming rule beside `Tables`" |
| When a unit differs | Kept |

**Decided in review** (first round, on the head with the three slices as
first cut):

1. The replay's one step per statement of the final lists is accepted. It
   is not a second pass for a fact the first pass could record: the fact is
   the final statement order, which no construction step has. T6 keeps
   exactly this one statement-level naming walk ((g) point 5).
2. Two function literals in one statement: closing order, with
   `ambiguous_orders` gated at zero; gone at T6.
3. An import released before the close stays in the free list: a counted
   limit (`free_differences`). Superseded: the gate requires zero, so a
   module reference has a site ("as built", change 1).
4. The functions the lowering builds itself were not as assumed: two of the
   three move pre-built expressions into the function. G10 and
   `names::adopt` are the answer. What was searched for further sites, on
   the tree this section was written against: every construction of
   `View::JFun` outside tests is `finish_expression` (`bir/lower/expr.rs`:
   the body is lowered after `open`), the three sites of G9, and
   `bridge_j.rs` (the import of JavaScript into `Bir`, not the lowering);
   `bir/j/` builds no function; `Bir::copy_subtree` copies one
   (`Log::copied`). An edit that attaches a node below a closed `JFun` was
   not found in the lowering (read; the splice of T4g will be one).
5. A use names nothing in the replay: accepted as the counter
   `unnamed_references`, gated at zero.

Known holes in the acceptance tests when the slices were issued (all closed:
"as built", the tests of the replay's arms):

- no tree-level test names a loop variable, a catch variable or a rest
  field through the replay; they are first exercised when T5b-3 calls
  `names_agree` from `compare_oracle`. The T5b-2 builder writes the arms
  from the replay's doc comment and says in its report that they are
  untested; a difference found in T5b-3 is reduced to a Lambda there;
- no tree-level test has a function in the eta form (`ScopeRow::ETA` set);
  the same applies;
- the step-count constants (the `<=` bounds and the exact deltas) were
  derived on paper and have never run. A builder that finds one off by a
  fixed amount reports the measured relation and stops (the common part of
  the prompts).

#### T5 part B as built

Built in three slices and one finishing pass; check mode only. The lowering
records the log in every mode in which it runs (it runs in check mode only);
the replay runs at `State::finish`; check mode compares its names with the
naming pass and drops them. No output changes.

**The log** (`bir/lower/names.rs`, on the arena's `Scope`).

- One `ScopeRow` per function literal (16 bytes), pushed by `names::open`
  and written by `names::close` once the `JFun` exists: the printed header,
  the free list as a run of `Log::free`, and `CLOSED`, `ETA`, `FIRST_READ`,
  `COPY`.
- One `Place` per variable (8 bytes): its home and the row that last put it
  in a run.
- One site per reference, to a variable or to an imported module, pushed
  where the node is built, cleared where it is released, moved with the
  content by `Bir::replace`.
- `names::close`: the parameters get the row as home; the scope's own sites
  (outside its closed children) are read, one step each; each closed direct
  child that is still live gives its free list; the entries whose home is
  not the row are sorted by `Ident::cmp` and written, one per identifier.
- `names::adopt`: the first of two named reads of an expression (G10), at
  `apply_with_arity` and `external_dispatch`; the second is the JSX rule
  (item 4 below).
- `Log::copied` and `Log::bind` from `Bir::copy_subtree` and `Bir::bind`.

**The tables** (`emit::naming::Tables`): the pass's rule on dense rows with
an undo stack, as designed. `Saved` holds the `born` mark of its group (in
its padding); `Tables::size` gives every vector its length once per unit.

**The replay** (`names::replay`, `names::Storage` in the lowering state): a
prelude that attaches each live row to the statement its literal stands in
(the literal's ancestors, each read at most twice), then one walk over the
final statement lists: the program's imports, the reservations, the
statements, the exports. A declaration is read as the printer writes it
(omitted, as its value, or with its binder). The names of the variables are
written in the arena's `Vars::printed`; the names of the modules and the
cached bounds in `emit::naming::Printed`.

**Changes to the design, each with its reason.** The numbers are those of
the comparison with the pass before the change.

1. *A module reference is a site* (was: a count, with the import pushed in
   the open scope's run where the reference is built, and a released
   reference left in the free list as a counted limit). A reference built
   in an open function and released before its close
   (`(l, r) => Primitive_int.compare(l, r) == 0` prints `l === r`) stayed
   free; the gate does not allow it, and a wrongly free import changes a
   name when a local has the module's base. Considered: decrementing a
   per-scope count of the import at the release (needs the scope the
   reference was built in: a word per reference, and a search for the open
   scope that owns it), and removing the entry from the run at the release
   (a search of the run). Chosen: the mechanism variables already have. A
   `JQualified` keeps the index of its site in its unused third word;
   `Bir::allocate` pushes the site, `Bir::register_kind` clears it at a
   release, `Bir::replace` moves it, and the close reads it with the
   variable sites. So the free list of a closed scope holds exactly the
   imports a live node of the function references when it closes. Cost: one
   push (8 bytes) per module reference built, one write per reference
   released, one step per reference at the one close that reads it; nothing
   is read below a node. `Log::import_reference` and its hook are deleted.
   Runtime library: `free_differences` 32 to 0.
2. *The free list is sorted by the identifiers, one entry per identifier*
   (was: by `vars.order` of the origin, one entry per variable or import).
   A variable's order is not its identifier's stamp for a variable the
   lowering makes for a JavaScript name (stamp zero) or a hidden identifier
   (stamp -1), and the pass sorts and deduplicates identifiers: a module
   the unit reads and the runtime module of that name are two imports with
   one identifier. `names::close` takes the identifier table. Cost
   unchanged.
3. *`FIRST_READ` for every function; the method flag is read by the replay*
   (was: `THIS_USED`, computed at the close for a method). `PjsFnMethod`
   makes a function a method after its close. The comparison of the run
   entries with the first parameter is paid for every function (one
   comparison per entry, already a step); the replay reads the header's
   flag for the parameter and for the eta form (a method is not
   eta-reduced). tests/tests: `name_differences` 11 and
   `unnamed_references` 11 to 0.
4. *An operand the printer does not print is not a reference.* In a unit
   that preserves JSX (`-bs-jsx-preserve`) the printer writes an element as
   `<tag ...>`: the runtime callee is not printed, nor the tag of an empty
   fragment, and the pass does not count them. The lowering takes the
   option (`lower_with_resolver`, `Log::jsx_preserve`); at the close and in
   `adopt`, a live reference whose chain of members ends as the callee or
   the fragment tag of a JSX node is skipped when `jsx::printed_form` (the
   printer's `jsx_printable`, read from the finished node) says element or
   fragment. This is the second named place where an expression is read
   for a reference, beside `adopt`: `Log::unprinted` reads up from a
   reference through member nodes to a JSX node, and `jsx::printed_form` /
   `jsx_tag` then read the element's property keys and down the tag's
   chain of members, to decide whether the reference is printed. Cost,
   only in such a unit: one step per member above the reference, one per
   property key, one per member of the tag's chain (and its base), counted
   in `Log::steps`; `printed_form` runs once per reference that is the
   callee or the tag of an element. A tag that is a chain of n members
   costs 3n + 13 steps for the element with two keys (the tag's reference
   walks up n members, and `printed_form` reads the chain down for the
   callee's site and for the tag's): 3,013 steps at n = 1,000 and 30,013
   at n = 10,000
   (`a_jsx_tag_chain_of_ten_thousand_members_costs_three_steps_a_member`).
   The application:
   `free_differences` 4,889 in 988 units to 4.
5. *A closed child gives its free list at the enclosing close, when it is
   live* (was: at its own close, into the enclosing run). A closure in a
   statement the lowering drops afterwards (a pure effect, a dropped
   branch) left its captures in the function around it. The steps are the
   same, at a later time; `Child` (12 bytes) keeps the row beside the site
   range. The application: `free_differences` 4 to 0.
6. *The replay reads a declaration as the printer writes it*
   (`walk::prints_declaration`): a dead and pure declaration names nothing
   and its function is not entered; a dead declaration with an effect names
   no binder. The lowering writes every declaration as used, so no corpus
   reaches this; the tree-level tests do, and T4g will.
7. *The replay's storage is the lowering's.* `names::Storage` is a field of
   the lowering state; `Storage::reserve`, `Tables::size` and
   `Log::with_capacity` give every vector whose length the unit bounds that
   length once. A unit costs 17 allocations for the log and the replay,
   the same at width 1,000 and 10,000 (pins 85, 102, 85, 155; each vector
   is named in LOWERING_ALLOCATION_SCALING.md); a second replay with the
   same storage allocates none. Shared instead of added: `Vars::printed`
   for the names, the export selection for the exported variables, one
   reservation list, `born` in `Saved`, one per-variable column.
8. *The comparison* (`compare_with_pass`) compares the free lists as
   multisets of identifier sequences, live copies included on both sides
   (was: sorted and deduplicated sets, with the copies left out on the
   replay's side only, so two equal lists counted as one and two swapped
   lists cancelled). `free_lists` gives the list of every closed row whose
   literal is live, a copy's included, as the pass keeps one list per
   function literal, a copy included. Zero on all four corpora in this
   form (the gate below). `compare_oracle` compares each rule test in both ways of
   printing JSX.

**Kept from the wiring slice, with the reason.**

- A rule-test root is closed over its free variables (`unit_of`): a unit
  binds every variable it reads, and the pass names an unbound variable
  where it is used, which no unit has.
- Every module of a test unit gets a path: a built unit resolves every
  module it reads; the pass names an unresolved module where it is used.
- A unit the pass does not support is not compared and is counted
  (`names_uncompared`): there is no oracle for it.
- The parameters of a function the printer eta-reduces are not unnamed
  references (neither side names them).
- Only `ApplyStatus::Na` reaches `apply_with_arity`; the other two build
  the call directly, so only `Na` reaches the adoption (pinned by
  `a_partial_application_whose_argument_reads_a_local_reaches_the_adoption`).
- `Log::reserve_repeat` stays as a test helper, as every pool of the
  lowering has one for the warmed tests; production sizing is
  `Log::with_capacity`.

**The gate.** `name_differences`, `finish_differences`, `free_differences`,
`ambiguous_orders` and `unnamed_references`, summed per corpus:

| Corpus | Units compared | Not compared | `adopted_nodes` | Names (pass = replay) | Sum |
| --- | ---: | ---: | ---: | ---: | ---: |
| Runtime library | 112 | 1 | 0 | 1,570 | 0 |
| tests/tests | 735 | 1 | 52 | 12,525 | 0 |
| Fixtures | 608 | 1 | 0 | 13,821 | 0 |
| A 3,735-module application (with the runtime, Belt and its dependencies: 3,848 units) | 3,847 | 1 | 0 | 249,300 | 0 |

`scripts/test_backend_coverage.py` prints the first three lines and fails
when a sum is not zero (the `Backend bridge coverage` job). The uncompared
units are those the naming pass rejects, for its own reasons; their number
per corpus is recorded in `compiler-rust/tests/backend_coverage.txt`
(`names-uncompared`) and the script fails when it rises (`--record`
writes the current numbers). One per corpus, found by printing the pass's
`Unsupported` reason in a check build of each corpus:

- runtime library: `Stdlib_Dict.res`, "delete call syntax";
- tests/tests: `src/jsx_preserve_cases.res`, "JSX sequence container";
- fixtures: the runtime's `Stdlib_Dict.res` again (the fixtures script
  builds the runtime with the fixtures), "delete call syntax";
- the application: the runtime's `Stdlib_Dict.res` (its stats name the
  unit; the reason is that of the same source in the runtime library).

**What the replay costs**, from the counters of the same builds (steps are
unit operations of `names.rs`; the calls into `Tables` come on top):

| Corpus | Statements | Function rows | Replay steps per statement | Ancestors per literal | Reserved per literal | Log steps per literal |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Runtime library | 1,934 | 336 | 1.65 | 1.03 | 1.74 | 12.2 |
| tests/tests | 20,698 | 4,253 | 1.98 | 1.85 | 1.91 | 10.3 |
| Fixtures | 16,284 | 3,544 | 1.86 | 1.38 | 1.59 | 8.5 |
| The application | 317,336 | 67,617 | 2.40 | 2.67 | 2.90 | 24.1 |

A statement costs one step. A function literal costs one step for its row,
the ancestors between it and its statement (each read at most twice) and
one step per entry of its reservation; these three are the "replay steps"
beyond one per statement. The log's steps are those of `close` and `adopt`:
the sites, the run entries, the comparisons of the sort.

**Measurements.** Fat LTO, one codegen unit, one worker, cachegrind
(`scripts/compare_build_instructions.py`, sequential, one checkout for both
sides), a clean build of tests/tests (743 modules), this head against trunk
`8ca6c42db`:

| Mode | Trunk | Head | Change |
| --- | ---: | ---: | ---: |
| Default (5 runs each, the smallest) | 4,023,215,553 | 4,023,088,119 | -127,434 (-0.003%) |
| `RESCRIPT_BACKEND=check` (3 runs each, the smallest) | 20,019,716,959 | 20,191,557,982 | +171,841,023 (+0.858%) |

The default build saves nothing and costs nothing: the lowering does not
run in it. Of the check build's 20,191,557,982 instructions, by the
function cachegrind attributes them to: `bir::lower::names` 5,998,607
(0.030%: `close` 2.4 M, `read_sites` 1.4 M, `Replay::reserve` 0.7 M),
`emit::naming::Tables` 5,065,311 (0.025%), and the rest of `emit::naming`
51,017,442 (0.253%), which is the naming pass and the comparison, run as
the oracle and gone with check mode. The replay's walk is inlined in
`State::finish` (+8,932,469 against trunk). `Bir::bind` (+5.0 M, the home
of a binder) and `Bir::allocate` (+2.4 M, the site of a module reference)
are the log's cost where nodes are built. The remaining increase is the
oracle's maps and the copies check mode makes for the comparison. Taken
together the log and the replay are about 27 M instructions of the check
build (0.14%) for 20,698 statements and 4,253 function rows in 736 units:
about 37,000 a unit, which includes sizing and clearing the per-node marks
and 17 allocations.

**What T6 takes over.** The replay's names become the printer's:

1. `Vars::printed` and `Printed::modules` are the table `oxc_codegen` reads
   (a symbol per variable index; a symbol per cached bound). The naming
   pass is then called by the legacy side and by check mode only.
2. The prelude and `Scratch::marks` go: a statement constructor knows the
   literals of its expressions, in print order, so `ambiguous_orders` goes
   too.
3. The module list. The program names the imports with a live reference;
   in a unit that preserves JSX, a module whose only references are
   unprinted callees is still imported by the legacy passes. T6 decides the
   module list from the same facts the free lists use.
4. Each slice that removes or moves a statement before the replay (T4g's
   splice, T4d, T4e, the shake) says what it does to the free lists: see
   the limit below.

**Still a limit**, each counted by the gate:

- A reference, a statement or a function literal released inside a function
  after that function closed leaves its free list as it was
  (`free_differences`). Zero on the four corpora; T4g's splice is the
  first edit of that kind.
- Two function literals of one statement are replayed in closing order
  (`ambiguous_orders`, G8). Zero on the four corpora; gone at T6.
- A use names nothing in the replay (`unnamed_references`). Zero on the
  four corpora.
- The tag of an empty fragment is skipped when it is a variable, a module
  or a chain of members over one (what an external gives). Another
  expression as the tag would be counted as read (`free_differences`).
- A module that does not resolve is named by the pass where it is used and
  by the replay never (`name_differences`). No built unit has one.

#### T6 design

Status: design. No slice is built. Skeleton and acceptance tests of the
first two slices are in `emit/builder.rs` and `emit/builder_tests.rs`; the
build prompts are in 11.9, which supersedes 11.8. "Prototype" below means
bodies written during this design turn, run against the tests and the
profiler, and taken out again before the commit; "read" means read in the
code and not run.

**Findings: what 11.8 and section 3 did not account for.**

1. **11.6 and 11.8 contradict each other on what runs after T6.** 11.8's end
   state deletes `bir/bridge_j.rs`. 11.6 (T4g) and the re-cut table keep the
   legacy passes P3 to P6 on the new side after T6, and those passes read a
   `JsArena`, which the new side only has through `bridge_j::export_lowered`.
   No pass can run on oxc nodes. Decided below ("The gate"): the passes do
   not run on the builder's program; the comparison point of check mode
   moves to the legacy program after the passes that have left.
2. **"`bir/lower` changes types only" (11.8, step 4) does not hold.** Read:
   the lowering outside its tests is about 18,000 lines with about 900
   places that build, match, detach, release or copy a J node through a
   `NodeId` (`rg -c 'View::J|Op::J|View::S[A-Z]|\.view\(|\.release\(|\.detach\(|\.replace\(|copy_subtree'`
   per file; `prim.rs` 83, `ffi_args.rs` 66, `names.rs` 66, `cond.rs` 57).
   A `NodeId` is `Copy`, has a parent and is its own identity. A handle that
   owns an oxc node is none of the three.
3. **A function body's final form is not known when the function closes.**
   The flatten pass leaves the test of a conditional it splits untouched
   (`Flatten::statement`, `Return(Cond)` and `Exp(Cond)`: OCaml
   `js_pass_flatten.ml` 54-61 and 79-86), so a function literal inside such
   a test keeps the body the lowering wrote (`z => z ? 1 : 2`), and the same
   literal anywhere else gets `if (z) { return 1; } else { return 2; }`
   ("T4c design", counterexample 2). Which of the two is decided where the
   statement around the literal ends up, after the literal's node exists.
4. **An oxc node inside a parent can only be reached from above.** There is
   no parent link and no pointer from a table to a node, and safe Rust gives
   no second owner. A fact can be recorded at construction (the table); an
   edit of a node that is already attached needs a path from a node one
   owns.
5. **The form the rules read is not the form the printer needs.** The legacy
   printer writes right-nested `&&`, `||` and `|` chains without
   parentheses and a nested sequence flat; `oxc_codegen` prints the tree it
   is given, so `a && (b && c)` keeps its parentheses. The emitter of trunk
   rebuilds the chain left-nested (`Build::bin`, `chain_tasks`; `sequence`).
   The rules need the nesting the lowering built (J-E5 reads `x && (x &&
   r)`; J-E9 descends ten levels through `&&` and `||`; `equal` is false
   for two different nestings).
6. **A statement's print form depends on where it stands.** `Build::stmt`
   takes `top` (a top-level function is a declaration) and `tail` (a unit
   function drops its final `return` and an `else` that only returns
   `undefined`); a `while` is followed by an empty statement (found by the
   prototype: the legacy text is `while (c) {...}` and a line `;`); an
   expression statement that is a variable, a module or a string is not
   printed (`walk::omitted_expression`).
7. **There is no "Bir view of `emit/walk.rs`" on trunk** (11.8, step 5): the
   experiment that had one was not merged (PRINTER_INSTRUCTIONS,
   "Historical experiment"). `emit/` reads the JS IR only.
8. **A 2-byte table entry cannot point to a side pool** (section 3, "2 bytes
   a node ... a side pool the table points to").
9. **B:164 reads a fact of an identifier that section 3 does not list**: a
   call is pure only as `Array.isArray(x)` on a JavaScript identifier
   (`is_array_is_array_callee`: the `JS` flag, or a global of stamp zero).
   Found by the prototype: the purity oracle failed without it.
10. **JSX in preserve mode and `%raw` take the indentation of what is
    around them** (`Build::jsx_indent`, `call_argument_needs_extra_group_
    indent`): a value known going down, not when the node is built.

**(a) The handle and the table.**

| Type | What it is | Bytes | Where |
| --- | --- | ---: | --- |
| `Row` | The facts of one node: `flags` (16 bits), `kind` (the J-level kind, 8 bits), `aux` (8 bits: the `BinOp`, a boolean's value, the unit bit, the number class, the `LetKind`), `payload` (32 bits: a variable's index, an integer literal's value, a field position, the lowering's id of a call's information or of a block's shape, a function's scope row) | 8 | one per node in `Builder::rows`, dense by `node_id`; written where the node is created |
| `J` | An expression in flight: the oxc `Expression` by value and its `Row` | 24 | what an expression constructor takes and returns |
| `S` | A statement in flight: the oxc `Statement` by value and its `Row` | 24 | what a statement constructor returns |
| `List` | A statement list in flight: a run of the builder's statement pool | 8 | what a compound statement constructor takes |
| `Mark` | Where the operands (or staged statements) of the next list constructor start | 4 | `Builder::mark`, `Builder::stage_mark` |
| `Kind` | 31 kinds in the first two slices, numbered densely (`Kind::ALL`) | 1 | `Row::kind` |

All pinned (`sizes`, `statements::sizes`). `Option<S>` is 24 bytes (the
pool's slot).

*Why the handle is 24 bytes.* `Expression` is 16 (a tag and an arena box).
Every rule reads flags or the kind of its operands; with a 16-byte handle
that is the node's `node_id` (a load through the box, at an offset that
depends on the variant) and then the table row, for every operand. The row
beside the node makes it a register read. A handle is not `Copy`: the
constructor that attaches an operand consumes it, which is the invariant
`Bir` checks at run time today (a node attached twice).

*Why the row is written at creation and is 8 bytes* (changes section 3: "2
bytes a node, written when the handle is attached"). Finding 8: the pointer
to the side data has to be in the entry, so the entry is 8 bytes: 2 of
flags, 1 of kind, 1 of `aux`, 4 of payload. Writing it where the node is
created costs the same store as writing it at the attachment and makes
attaching free; `Builder::row` gives the row of an attached node in one
indexed read.

*The side pools are the lowering's own.* A payload is an id in a pool the
lowering already has (`pools.javascript` for call information, object keys
and templates; the constant pool; the text pool; `FuncId`). The builder
adds one pool in T6c: `Shape` (16 bytes, blocks only: the lowering's id of
the tag information, the element count, the number of leading properties
the print form adds and where the bits of the omitted optional fields
start).

*Flags.* `PURE` (B:102), `STRICT` (E:15), `DELAY_SAFE` (A:28), `SUBEXPR`
(E:146), `DUPLICABLE` (X:60), each computed from the operands' rows in
O(arity) as `bir/j/facts.rs` does today; `HAS_FUN` (a function literal at
or below) and `SEAL` (the seal has work at or below: (e)), both the "or" of
the operands. T4g adds the late mark.

*Operand lists* (arguments, elements, statements) go through a stack the
builder owns: the caller takes a `Mark`, pushes handles, and the list
constructor drains them into an arena vector of exactly that length. No
`Vec` per call.

*Identity.* `node_id` is the node's index in `Builder::rows`, from 1
(`NodeId::DUMMY` is 0). It replaces the `NodeId` of `Bir` wherever a table
is keyed by a node (sites, the scope row of a function literal).

**(b) Per row: what it reads of a child, and from where.** "Handle": the
`Row` in the operand's handle. "Node": the oxc node of the operand, matched
by reference or taken apart by `Box::unbox` (the operand is owned).
"Table": `Builder::row` of a node inside the operand. "Pool": the
lowering's pool the payload names.

| Row | Reads | From |
| --- | --- | --- |
| J-E1 `string_append` | an operand is a string literal; its text | handle (`Kind::Str`); pool (the payload is the text's id: the node's string is decoded for printing and two decoded halves do not concatenate to the decoded whole) |
| | `(a ^ "b")`, `("c" ^ d)`: the inner operands | handle (`Kind::StrAppend`); node (left, right, by `unbox`); table (their kinds) |
| J-E2 `length` | pure array or block literal and its element count; string literal; function literal | handle (`PURE`, kind); node (`elements.len()`) for an array, `Shape` for a block; pool (UTF-16 length of the text); the function's header through the payload |
| J-E3 `is_null_or_undefined` | the kind | handle |
| J-E4 `bin` | integer literals; `len` of a pure target against 0; `null`/`undefined`; optional block | handle (`Row::int`, kind, `PURE`); for the length's target: node, table |
| J-E5, J-E6 | `x && x`: two variables are the same; `x && (x && r)`: the right operand's operands | handle (`Kind::Var`, payload); node of the right operand (left, right); table (their rows) |
| | `v !== undefined && v === literal` | node (both comparisons), table |
| J-E7 `cond` | the test is a literal, `!c`; both branches `(effect, undefined)`; a branch is `c2 ? a : b` | handle (kind, `Row::int`, `PURE`); node (the parts, by `unbox`); table |
| | the branches are equal | `equal`: both nodes read in parallel with an explicit pair stack, each pair's rows from the table; stops at the first difference (the cost of `bir/j/equal.rs`) |
| J-E8 `not` | literal; `!x`; a comparison; `&&`/`\|\|` whose operands can be negated | handle (kind, `aux` is the `BinOp`); for a comparison the operator is rewritten in place through the owned node, and `aux` in the handle and in the table; for De Morgan: node, table, explicit stack |
| J-E9, J-E10 | operands pure; `typeof x === "..."`, `Array.isArray(x)`, `x === literal`, to depth 10 | handle (`PURE`); node and table below it. A part used twice is copied (`Builder::copy`: one step per node copied, each copy gets its own row) |
| J-S1 `exp` | `(a, b)` with a number or `undefined` side; a number or `undefined` | handle (`Kind::Seq`); node (the two parts); table |
| J-S2 `block`, J-S5 `unnest_block` | the list has no statement, one, one block | `List::len`, `Builder::row_at` (kind) |
| J-S3 `simplify_if` | test is a boolean, `!c`; a branch is empty, exactly one `return`, one assignment to the same target, one expression statement; then ends in `return`/`throw`/`continue`/`break`; a branch is exactly one `if` | handle (test); `List::len`, `Builder::last_row`, `Builder::row_at` (the statements' kinds); `Builder::take` and the statement's node for the parts; `equal` on lists for rules 9 and 10 |
| J-S4 `normalize` | a switch on a literal | handle (`Row::int`, or the text through the pool); the clause keys, scanned once |
| J-M0 `remove_pure_subexpression` | `SUBEXPR` | handle |
| J-M1 `js_seq` | a side is a number or `undefined`; the left operand is a variable | handle; for an inner sequence: node, table |
| J-M2 | `null`/`undefined`; strictly pure and cannot be nullish; two literals | handle (kind, `STRICT`, `Row::int`); node for a float literal's value |
| J-M3 to J-M8, J-M10 | integer literals; an operand is `x >>> n`, `x \| 0` | handle (`Row::int`; `Kind::Bin` with `aux`); node (its right operand), table (`Row::int`) |
| J-M9 `typeof` | number, length, string, array, boolean | handle (kind) |
| J-M11 projection | a strictly pure array or block literal; element `i` | handle (`STRICT`, kind); node by `unbox`; for a block, `Shape` gives the print position of field `i` (the leading properties plus `i` minus the omitted optional fields before it: one popcount), an omitted field is a new `undefined` |
| J-M12 template | a value is a string or template literal | handle (kind); pool |
| J-M13 div, mod | `len / 2`; a nonzero integer divisor; two literals | handle (`Kind::Length`, `Row::int`) |
| J-M14 effects | a sequence; strictly pure parts; numbers and `undefined` | handle (`Kind::Seq`, `STRICT`, kind); node (the parts, by `unbox`) |

A rule that keeps a part of an operand and drops the rest calls
`Builder::release` on the rest: one step per node released, with the
reference bookkeeping `Bir::release` does today (a `Var` row clears its
site and its count; a function literal's row dies). A dropped node stays in
the arena until the unit is printed.

**(c) Where each printer decision of BACKEND_REDESIGN A.7 is taken.**

| Decision | Taken | By |
| --- | --- | --- |
| `x === null \|\| x === undefined` prints `x == null`; `0 - x` prints `-x`; property access with `.` or `[...]`; number spelling; string decoding; a call whose only argument is the unit value prints `f()`; the nullish test | when the node is built | T6a (`Builder::bin`, `dot`, `number`, `string`, `call`, `is_nullish`) |
| Runtime shape of blocks; `Some` as itself or through `Primitive_option.some`; templates; JSON; method `this` | when the node is built | T6c (with `Shape`), T6d |
| Parentheses by precedence | never: `oxc_codegen` | - |
| No parentheses for right-nested `&&`, `\|\|`, `\|`; a nested sequence flat | at the seal (finding 5) | T6e |
| A dead pure declaration is not printed, a dead impure one prints its value; `let x = undefined` prints `let x`; an expression statement that is a name or a string is not printed; `else { if }` prints `else if`; an `else` that is omitted; the `;` after a `while`; a block's statements spliced into its list | at the seal (finding 6) | T6e |
| Function declaration or `let`; a unit function drops its final `return`; an `else` that only returns `undefined` | at the seal: `top` and `tail` are known going down | T6e |
| Eta reduction; arrow or `function`; expression body or block; `{}` | at the seal, where the body is final (finding 3) | T6e |
| `for` upper bound bound to `i_finish` | when the loop is built (the bound is simple or not); its name at the replay | T6d (the loop), (d) |
| Raw JavaScript verbatim; JSX syntax or a call | when the node is built, with the indentation limit of finding 10 | T6d |
| File: directives, header, imports, exports, trailer | when the program is assembled | T6d |
| Names | the replay, (d) | T6d, T6s |

"The decisions that depend on the finished function are made when the
function's scope closes" (section 3) becomes "at the seal": finding 3.

**(d) Names.** Decided before this turn: the symbol of a binder and of a
reference is the variable's index, and the names are the replay's.

*The table `oxc_codegen` reads.* `Codegen::with_scoping` takes an
`oxc_semantic::Scoping`. A binder carries `symbol_id = variable`, a
reference carries `reference_id = variable`; the program slice creates one
symbol and one reference per variable, in index order, with the name of
`Vars::printed`: O(variables) and the bytes of the names, once per unit, no
step per reference. The mechanism is tried: the test helper `names` builds
the `Scoping` by hand and `a_reference_and_a_binder_print_the_name_of_
their_variable` prints `let v1 = 1; f(v1);` from a binder and a reference
that hold no text (ran against the prototype).

*An imported module and a cached bound are variables.* A symbol has to be
known where the node is built, and the number of variables is not final
then, so a second id space cannot be put after it. The first reference to
an import allocates a variable for it (kept in `pools.j_modules`); a range
loop whose bound is not simple allocates one for the bound. Neither has a
declaration the replay reads as a binder: the replay names the import in
the program's prologue and the bound at its loop (`Tables::synthetic`) and
writes both into `Vars::printed`. `Printed::modules` and `Printed::finishes`
go.

*How the replay reaches the function literals of a statement, in print
order* (changes "(g)" point 2, "the handle carries the first and last
literal"). A chain in the handle cannot be kept right: a rule that takes an
operand apart (`evaluate_now` moves an element of a literal into a
statement of its own) splits it, and the handle has no room (24 bytes are
the node, the flags, the kind and the payload). And by finding 4 the
replay cannot enter a literal's body from its scope row at all: the body is
inside the node. So: a statement's row has `HAS_FUN` when a literal is
inside it. The replay, on such a statement, descends its expressions in
operand order through the nodes whose row has `HAS_FUN`, and nowhere else;
at a function node it reads the scope row from the node's payload, does
what the replay does today (reservation, parameters) and walks the body's
statements. Operand order is print order, so `ambiguous_orders`, the
prelude and `Scratch::marks` go. Cost: one row read per operand of each
ancestor of a literal inside its statement ("T5 part B as built" measured
1.03 to 2.67 ancestors per literal). This is the one place besides `adopt`
and `release` where an expression is entered, it enters only the nodes
above a function literal, and it is counted (`descent_steps`); see open
question 1.

*`adopt`* stays: it reads an expression that was built before its
function's scope opened, now over oxc nodes (a `Kind::Var` row is a
reference; a function node gives its scope row).

**(e) The flatten pass, applied where a statement is written.** A statement
is "written" at the seal: once, when the unit is complete, in the replay's
walk over the final statement lists (the one statement-level walk; the
seal of a list comes before its naming). Not where a list is copied (T4b,
RESULT B) and not where a function closes (finding 3).

| Rule (`Flatten::statement`) | At the seal |
| --- | --- |
| F1 `Exp(Seq)`: one statement per part | the parts of the sequence become statements of the list being written; each is sealed |
| F2 `Exp` of a block literal: one statement per element | the same, from the literal's elements |
| F3 `Exp(Cond)`: an `if`; a branch without effect is dropped (`PURE` of the branch, from the table), the test negated when only the else branch is left; nothing, or the test alone, when both go | the `if` is written; the dropped branch is released; the test is not entered |
| F4 `Exp(target = Seq)`: the heads as statements, then the assignment of the last part | the same |
| F5 `Return(Cond)`: `if (test) { return a } else { return b }`, each `return` sealed again | the same; the test is not entered |
| F6 `Return(Seq)`: the heads as statements, then `return` of the last part | the same |
| F7 a block of one statement is that statement; F8 a block statement inside a list is spliced | the same |
| otherwise: every expression of the statement is mapped, which reaches the bodies of the function literals inside it | the descent of (d): the body of each literal is sealed where the replay enters it. A literal inside a test that F3 or F5 does not enter is named and its body is left as built |

The seal also writes the print forms of (c). It rewrites a statement list
only when a statement of it changes, and it enters an expression only below
`HAS_FUN` or `SEAL` (a chain or a sequence not in print form).

*The copied-branch reader (T4b, RESULT B).* `simplify_if_head` reads the
last statement of a copied branch as `Return(Cond)`. It keeps reading that:
nothing is sealed while the lowering runs, so every list the lowering
reads, copied or not, holds what its constructors wrote.
`flattening_a_copied_return_branch_changes_the_simplify_if_head_reader`
stays as it is; after the flip its two texts are the builder's.

*What T4g gets.* The site of a tail call is still read through the
reshaping (`sites` of "T4c design"): the `return` is not split when the
splice runs. The splice writes the `if` of F5 itself for the one statement
it splices into, and marks that `if` as not to be entered at its test.
The dropped branch of F3 is released at the seal, after every scope-close
decision: the count hazard `a_pure_branch_the_flatten_pass_drops_takes_
an_occurrence_built_still_counts` is not removed by T6, and T4g's design
step has to subtract those occurrences where the statement is built (the
branch's `PURE` flag is in the handle then). This corrects "T4c design",
"What has to move first", first item.

**(f) The readers of J-level `Bir` today.**

| Reader | After T6 |
| --- | --- |
| `bir/j/` rules (`norm.rs`, `logic.rs`, `equal.rs`, `facts.rs`, `plain.rs`) | Rewritten over handles in `emit/` (T6g to T6j), with the rule tests of `norm_tests.rs` and `facts_tests.rs` ported to the oracle form against `js_ir::build` and `js_exp_make`; the `bir/j/` files are deleted at the flip |
| The lowering (`bir/lower/`) | Reaches J nodes only through an interface (T6k to T6r), then the interface is the builder's (T6s) |
| The naming log: `open`, `close`, sites | Unchanged in what they do. A site is keyed by `node_id`; `Bir::replace` moving a site becomes the handle carrying its site in the payload of a `Kind::Var` row |
| The replay (`names::replay`) | Walks the builder's statements with the seal; the prelude, `Scratch::marks` and `ambiguous_orders` are deleted (T6s) |
| `export.rs` (rows, sites of the position facts) | A `Row` (the 8-byte top-level row) holds a statement's position in the top-level `List` instead of its `NodeId`; a position fact is recorded where the reference is built, as today |
| `close.rs`, `scope::return_sites` | Read the last statement of a list through `Builder::last_row` and its node |
| `globals.rs` (`decide`: from a reference up to the root) | No parent exists. The decision moves into the replay's walk, which knows the bindings around the statement it is in: a reference to a global is found by the descent only when its statement's row says one is inside (a flag, set like `HAS_FUN`). Designed in the turn that issues T6r |
| The check-mode gate | "The gate" below |
| The allocation-pinned tests (`unit.rs`, LOWERING_ALLOCATION_SCALING.md) | Re-pinned once at the flip, with the builder's vectors named; a pin is an invariant of the flip slice, not of the slices before it |
| `bridge_j.rs` (import and export), the `lambda-bridge` round trip of J | Deleted at the flip; `shadow.rs` keeps the Lambda bridge only |
| `validate.rs` on J nodes | Deleted at the flip: ownership makes a node attached twice a compile error |

**The gate.**

- *Until the flip (T6a to T6r)* check mode is what it is today: both texts
  through the legacy printer, before and after the passes. The builder is
  compared with the legacy text by the suite that exists for the oxc
  emitter: `scripts/test_printer_parity.py` (through
  `scripts/test_js_output_parity.sh --printer oxc` and the `stdlib` and
  `gentype` twins; CI job `printer-parity`), which reformats the legacy
  JavaScript once with `scripts/js-reformat` and compares with the oxc
  text, on the JavaScript, stdlib and genType corpora, with the ratchet
  `compiler-rust/tests/printer_coverage.json`. From T6f on the emitter of
  trunk writes through the builder, so every builder constructor is under
  that suite.
- (This bullet and the next are withdrawn by "T6: the order of the flip":
  the decision slices land before the flip and nothing is given up.)
  *From the flip (T6s)* check mode compares the builder's text with the
  legacy program after the passes that have left the new side: the legacy
  side keeps a copy of its program after P1 and P2, prints it with the
  legacy printer, reformats it once in process (`js_reformat::reformat`,
  already a dependency) and requires equality with what `oxc_codegen`
  prints for the builder's program. Corpora: the runtime library,
  tests/tests and the fixtures through `scripts/test_backend_coverage.py`,
  and the application through a `RESCRIPT_BACKEND=check` build. T4g moves
  the point after P3, T4d after P4, T4e after P5, T4f to the final text.
- *What is given up between T6s and T4f*: the second comparison of today
  (both programs through the remaining legacy passes). It caught facts the
  passes read that no text shows (purity, the kind of a declaration, the
  call information). Those surface in T4g to T4f, each of which compares
  its own decisions.
- *`RESCRIPT_BACKEND=new` keeps today's meaning* (the legacy lowering) until
  T4f: before that the builder's program is not the final program. This
  corrects 11.8, step 4 and its end state ("`RESCRIPT_BACKEND=new` below
  the default"): that measurement belongs to T4f.

**(g) The instruction budget.**

*Where the +10% of PRINTER_INSTRUCTIONS came from* (tests/tests, of
4,357 M): 298 M was `bridge_j::import_js`, the conversion of a finished
`JsArena` into `Bir`, which a lowering that writes its own tree never pays;
65 M was the adapter that decoded each J node into a JS-shaped view
(`EmitterView::ek` 23 M and its helpers); 56 M was the naming pass. The
rest is shared with printing from the JS IR.

*What the builder does instead, per node:* one bump allocation of the oxc
node, O(arity) flag arithmetic on rows that are in the operands' handles,
one 8-byte push. No second tree, no view, no naming pass: the replay costs
one step per statement and the descent of (d).

*Measured on a prototype* of T6a (the bodies behind the tests of
`emit/builder_tests.rs`): one expression of 10,000 calls `f(a.b, 1, "s")`
inside a call (60,002 nodes), release test binary with thin LTO,
cachegrind, one run each, the cost of the test harness and of building the
description subtracted (21,324,660):

| Path | Instructions | Per node |
| --- | ---: | ---: |
| Builder: construct the oxc nodes with their rows, print with `oxc_codegen` | 19,604,712 | 327 |
| Legacy: construct the JS IR | 14,839,066 | 247 |
| Legacy printer on that JS IR | 23,226,389 | 387 |
| `emit::emit` on that JS IR (naming pass, `Build`, `oxc_codegen`) | 45,856,062 | 764 |
| `bridge_j::export_js` of the J-level `Bir` of that program, then `emit::emit` | 79,211,835 | 1,320 |
| (`bridge_j::import_js`, to get that `Bir`; not part of any path after T6) | 155,654,043 | 2,594 |

So on this input the builder with its printing is 0.25 of "`bridge_j` plus
`emit`", which is what the new side would pay to print through oxc today,
and 0.51 of the legacy construction plus the legacy printer. What the
figure does not show: names (the identifiers are written by text, so no
replay and no `Scoping`), statements, the rules, the seal, and the
construction of the J-level `Bir` that the fifth row starts from. The
input is the smallest honest one, not a corpus. The first slice that
measures a corpus is T6f (the printer-parity build with
`RESCRIPT_JS_PRINTER=oxc`, before and after, by
`scripts/compare_build_instructions.py`); the first that measures the
lowering is T6s (check mode before and after, with the share of
`emit::builder` from the cachegrind output).

*The budget.* The default build runs neither the lowering nor the oxc
emitter, so every slice must leave the `Instruction count` job within
+0.02%; a slice that moves it more has changed a default-path function and
is wrong. T6a to T6e and T6g to T6j add code under `#[cfg(test)]` only: the
release binary is the same. T6f changes the `RESCRIPT_JS_PRINTER=oxc`
path: budget, no more instructions than before on tests/tests with that
variable set (the naming pass and `Build` stay; the constructors move).
T6s changes check mode: budget, fewer instructions than before (the J
tree, `export_lowered` and one printing go).

**Changed against earlier statements**, each with its reason above: the
table entry is 8 bytes and written at creation (section 3); the print
decisions that need the final statement are at the seal, not at the
function's close (section 3, 11.8 step 1 (c)); the handle carries no
literal chain, the replay descends below `HAS_FUN` ("(g)" points 2 and 5);
modules and cached bounds are variables ("(g)" point 3); the lowering's
change is not types only and comes in eight slices (11.8 step 4); the
legacy passes do not run on the builder's program and the gate's point
moves (11.6 preconditions and end state, 11.8 end state); `RESCRIPT_
BACKEND=new` is unchanged until T4f; "the Bir view of `emit/walk.rs`" does
not exist (11.8 step 5).

**Open questions**, each with the recommended answer.

1. *The descent below `HAS_FUN` and `SEAL` enters expressions, which "(g)"
   point 5 forbids.* Recommended: accept it as a counted exception
   (`descent_steps`, reported per corpus beside `adopted_nodes`), because
   finding 4 leaves no other way to reach a function body, and require of
   T6f the relation "descent steps <= 3 x the ancestors of function
   literals and of chains" on tests/tests.
2. *JSX in preserve mode on the lowering's path* (finding 10). Recommended:
   the unit stays unsupported on the builder's path (counted, one unit in
   tests/tests) until a slice after T6 gives the JSX node its indentation
   at the seal, which knows the depth.
3. *The lowering's interface (T6k to T6r) is cut by file here, not
   designed.* Recommended: one more design turn before T6k is issued, which
   writes the interface (the constructors and readers `bir/lower` may call)
   as a skeleton; T6a to T6j do not depend on it.
4. *Source maps on the builder's path.* The emitter sets spans on leaves
   and statements from locations; the handle has no room for one.
   Recommended: a location is set on the node where it is built (`span` is
   a field of every node), in the slice that wires the lowering (T6s), and
   check mode compares mappings as today.
5. *The comparison through the remaining passes is suspended from T6s to
   T4f.* Recommended: accept; the alternative is a converter from oxc nodes
   back to the JS IR, which is a fallback structure of about 2,000 lines.

#### T6: the cut

T6 as 11.8 wrote it is one slice of about 9,000 added and 9,000 deleted
lines. It is cut so that trunk is green and check mode stays at zero
differences after every slice. Four phases:

- **A, the builder** (T6a to T6f). The builder is written and tested
  against the legacy printer in the oracle form, under `#[cfg(test)]` (the
  form T5b-1 and T5b-2 had), and then becomes the back half of the oxc
  emitter trunk already has: `emit/build.rs` stops building nodes and
  drives the builder from the JS IR (T6f). From then on the printer-parity
  suite runs every constructor on three corpora in CI.
- **B, the rules** (T6g to T6j). The normalising rules of `bir/j/` over
  handles, each with its rule tests in the oracle form against
  `js_ir::build` and `js_exp_make`, under `#[cfg(test)]` until the flip.
- **C, the interface** (T6k to T6r). The lowering stops naming J opcodes:
  every construction, match, detach, release and copy of a J node in
  `bir/lower/` goes through functions of `bir/j/` over a handle type that
  is not `Copy`. The storage is still `Bir`, so check mode cannot move.
- **D, the flip** (T6s, T6t). The functions of the interface are the
  builder's; the J opcodes, `bir/j/`'s rules and `bridge_j.rs` are deleted;
  the gate changes as "The gate" says.

A slice "deletes what it replaces": in A (but T6f) and B nothing is
replaced yet, and what is added cannot be reached outside tests; T6f, each
slice of C, and T6s delete in the same pull request.

(The rows T6e and T6k to T6t are replaced by "T6: the cut of the
interface, revisited".)

| Slice | What | Files | Depends on | May run beside | Lines |
| --- | --- | --- | --- | --- | ---: |
| T6a | `Row`, `J`, `Kind`, the table, leaves, operators, calls, members, with their flags | `emit/builder.rs`, `emit/builder_tests.rs` | - | T6k | 450 |
| T6b | `S`, `List`, the staging stack; expression, `return`, `throw`, declaration, `if`, block, `while`, `break`, `continue`, `debugger`, in the form the rules read | the same two | T6a | T6c, T6k | 300 |
| T6c | Shaped literals: array, object, block with `Shape`, optional, spread, `await`, template, tagged template, JSON, flat call, record rest; `throw` of an exception block | `emit/builder_shape.rs` | T6a | T6b, T6k | 600 |
| T6d | The other statements (range loop with its bound's variable, `for of`, the two switches, `try`, labels); function nodes (parameters, the method's `this`, `async`, directive); raw JavaScript; JSX with its indentation as a parameter; the program (directives, imports, exports, trailer) and the `Scoping` from the names | `emit/builder_program.rs`, `Cargo.toml` uses `oxc_semantic` | T6b, T6c | T6g | 600 |
| T6e | The seal: print forms of (c), F1 to F8 of (e), the descent below `HAS_FUN` and `SEAL`; `Builder::release`, `Builder::copy` | `emit/builder_seal.rs` | T6d | T6g to T6j | 600 |
| T6f | `emit/build.rs` drives the builder: it walks the JS IR and calls constructors, then the seal; the node construction and the decisions of `walk.rs` that moved are deleted | `emit/build.rs`, `emit/walk.rs`, `emit/program.rs`, `emit/mod.rs` | T6e | T6g to T6j | 500, and 1,400 deleted |
| T6g | Taking a handle apart; `equal`; J-E1 to J-E4, J-E8 | `emit/rules_e.rs` | T6c | T6d to T6f, T6h | 600 |
| T6h | J-E5, J-E6, J-E7, J-E9, J-E10 | `emit/rules_logic.rs` | T6g | T6i, T6j | 600 |
| T6i | J-S1 to J-S5, J-M14 | `emit/rules_s.rs` | T6b, T6g | T6h, T6j | 500 |
| T6j | J-M0 to J-M13 | `emit/rules_m.rs` | T6g | T6h, T6i | 600 |
| T6k to T6q | The interface, one group of files a slice: (k) the handle types and `prim.rs`, `prim_cmp.rs`, `prim_block.rs`; (l) `cond.rs`, `switch.rs`; (m) `ffi_args.rs`, `external.rs`, `args.rs`, `call.rs`; (n) `jsx.rs`, `variant.rs`, `untagged.rs`, `record.rs`, `konst.rs`; (o) `loops.rs`, `tail.rs`, `rec.rs`, `try_.rs`, `exit.rs`, `label.rs`, `assign.rs`, `import.rs`, `expr.rs`; (p) `out.rs`, `mod.rs`, `unit.rs`; (q) `export.rs`, `close.rs`, `scope.rs` | `bir/j/`, the files named | T6k first, then any order | each other, phases A and B | 600 each |
| T6r | The interface for `names.rs` (the replay behind the statement interface of "(g)" point 2) and `globals.rs` (the decision in the replay's walk) | `bir/lower/names.rs`, `globals.rs` | T6q | phases A and B | 600 |
| T6s | The flip: `State` owns the allocator and the `Builder`; the interface's functions are the builder's and the rules of phase B; the replay seals and names the builder's lists; check mode compares as "The gate" says; deleted: `bir/bridge_j.rs`, the J opcodes of `bir/node.rs`, `bir/j/{norm,logic,equal,facts,plain}.rs`, the prelude, `Scratch::marks`, `ambiguous_orders`, `Printed::{modules, finishes}`, `validate.rs`'s J arms | `bir/`, `emit/`, `lambda/lam_compile.rs`, `bir/shadow.rs` | all | - | 600, and about 9,000 deleted |
| T6t | Measurements on the four corpora, docs/STATUS.md, `tests/backend_coverage.txt`, the allocation pins | docs, tests | T6s | - | 100 |

**Which slices change a default-path function.** None is meant to. T6f
changes `emit/` (reached with `RESCRIPT_JS_PRINTER=oxc` only) and T6s
changes the `CHECK` arm of `lam_compile.rs` and deletes code the default
build links but does not run: both need the full output gate (the four
parity scripts and the `Instruction count` job within +0.02%), because a
shared helper is easy to touch by accident. T6k to T6r change `bir/`
(check mode only): `scripts/test_backend_coverage.py` with the ratchet
unchanged, and the `Instruction count` job. The others add code under
`#[cfg(test)]`: `cargo test` for `emit::`, and the job as a check that the
binary did not move.

**End state of each slice**, to paste with the output:

| Slice | Facts |
| --- | --- |
| T6a | `rg -c 'todo!\("T6a"\)' src/emit/builder.rs` gives 0; `rg -n 'T6a build' src` is empty; `rg -n 'mod builder' -B1 src/emit/mod.rs` shows `#[cfg(test)]` |
| T6b | `rg -c 'todo!\(' src/emit/builder.rs` gives 0; `rg -n 'T6b build' src` is empty |
| T6c, T6d, T6e, T6g to T6j | `rg -n 'todo!\(' src/emit` is empty for the slice's file; `rg -n '<slice> build' src` is empty |
| T6f | `rg -n 'Expression::new_\|Statement::new_\|AstBuilder' src/emit/build.rs src/emit/program.rs` is empty; `rg -n 'cfg\(test\)' src/emit/mod.rs` shows test modules only; `rg -n 'chain_tasks\|string_tasks\|jsx_indent' src/emit` shows `builder` files only; the printer-parity ratchet unchanged or risen |
| T6k to T6r | for the slice's files, `rg -n 'View::J\|Op::J\|View::S[A-Z]\|Op::S[A-Z]'` matches only inside `#[cfg(test)]` modules; after T6r the same for all of `src/bir/lower` |
| T6s | `rg 'JSeq\|JBlockLit' src/bir/node.rs` is empty; `rg bridge_j src` is empty; `rg -n 'ambiguous_orders' src` is empty; `rg -n 'apply_js_flatten_pass' src/lambda/lam_compile.rs` shows the legacy side and the check copy only; `rg -n 'Names::collect' src` shows `emit/program.rs` (the legacy side's oxc printer) and check mode only |

What is designed to the level of a build prompt in this turn: T6a and T6b
(skeleton, acceptance tests, 11.9). T6c to T6j have their content, files
and end state fixed here and get their skeleton and tests from the next
design turn. T6k to T6r need the interface designed first (open question
3).

#### T6: the order of the flip

Status: design, answered from the code of trunk `127f3d89c8`. It answers
decision 5 of the review of "T6 design" and replaces the second and third
bullet of "The gate" and the rows T6k to T6t of "T6: the cut" (the new rows
are in "T6: the cut of the interface, revisited"). Nothing in it was run:
every statement is "read", and the two places where a claim rests on a
slice that is not designed yet say so.

**The question.** Can T4g, T4d, T4e and T4f be written against the
interface of phase C and land before the flip, so that check mode's
comparison through the remaining legacy passes never stops?

**The answer is (A): yes, in this order: T6k to T6r, T6u, T4g, T4d, T4e,
T4f, T6v, T6s.** The flip (T6s) is the last slice that changes what check
mode runs, and at the flip the two texts compared are both final texts.
Two things have to be true for that, and both are decided here:

1. the flatten rules (pass P1) leave the new side before the flip, as a
   slice of their own (T6u), written once above the interface;
2. a decision slice edits JavaScript it has built in one of three places
   only, each of which exists behind the interface on `Bir` rows today and
   on oxc nodes after the flip.

**What the new side runs today** (`LambdaCompiler::
compile_deps_program_with_lower_check`, `lambda/lam_compile.rs`):
`shadow::prepare_lower` (the lowering, `bridge_j::export_lowered`), then
`bridge_j::qualify`, `apply_js_flatten_pass` (P1),
`shadow::compare_decisions`, and `finish_flattened_output`: P3
`apply_js_tailcall_inline_pass`, P4 `apply_js_record_rest_pass`, P5
`apply_js_flatten_and_mark_dead_pass`, P6 `apply_js_shake_pass`.
`shadow::check_lower` compares two pairs of texts, both through the legacy
printer: `before` (the legacy program after export coercion against the
lowering's program) and `after` (both after their passes), and their
mappings.

**Why P1 has to leave first, and can.** "T4c design" showed that P3 cannot
leave the new side while P1 runs after the lowering (the two tests of (c),
and the dropped-branch term of (b)). P1 on the new side is a pass over a
`JsArena`; nothing of it is in the lowering. "T6 design" (e) puts its rules
F1 to F8 at the seal, and the cut put the seal in `emit/builder_seal.rs`
(T6e), so P1 could only leave at the flip. But the seal is a walk the
replay already makes: `names::replay` (`bir/lower/names.rs`,
`Replay::statements`, `child`, `statement`) visits every statement of the
final lists once, top down, with one frame per open list, and T6r puts
that walk behind the statement interface. F1 to F8 read a statement the
walk holds and write the statements that replace it (take the value of an
expression statement or a `return` apart, build an `if`, a `return`, an
expression statement, negate a test, release a branch). Each of those is a
function of the interface that the lowering needs anyway (`cond.rs` takes
sequences and conditionals apart, `expr.rs` and `export.rs` split a
sequence into statements). So the rules are written once, over the
interface, in the replay's walk (T6u, `bir/lower/seal.rs`), run on `Bir`
rows until the flip and on the builder after it, and the new side stops
running `apply_js_flatten_pass` when T6u lands. What stays in T6e is what
only the oxc tree needs: the print forms of "T6 design" (c), the descent
below `HAS_FUN` and `SEAL`, `Builder::release` and `Builder::copy`. This
is a change of the cut of T6e, recorded below.

T4b's RESULT B is not touched: nothing is flattened where a list is
copied. `simplify_if_head` keeps reading `Return(Cond)` in a copied
branch, because the walk of T6u runs when the unit is complete.

**Where a decision can edit built JavaScript, under the interface.** A
handle of the interface is not `Copy` and names no parent ("T6 design",
findings 2 and 4). "The design" of 11.4 was written for `NodeId`: "the
splice rewrites the `return` node in place", "marks its declaration in
place". Under the interface the same decisions are taken with these three
means, and no other:

| Means | What it reaches | On `Bir` rows | On the builder |
| --- | --- | --- | --- |
| E1: a statement of the run being closed is in flight | The statements `StatementStack::take_list` is about to copy: the lowering owns their handles, so it can take one, take its value apart, replace it or drop it | the slot's `NodeId` | the slot's `S` |
| E2: a mark by id | One bit or the payload of the row of a node that is already inside a parent (the dead mark of a declaration in a closed list, the late mark of a leaf, "the test of this `if` is not entered", "this `return` is the site of parked body `k`") | `Node::aux`, one store | `Builder::rows[id]`, one store |
| E3: the walk of the seal | Every statement of the final lists, once, top down, as an owned handle; an expression only below a flag (`HAS_FUN`, `SEAL`) | the walk of T6u | the same walk |

A value taken out at E1 that is put back at E3 waits in a pool of the
lowering (`Js::park`, one slot per parked body, 24 bytes after the flip).
What cannot be done is what the legacy passes do freely: rewrite a node
found from the side (through a site, a use count or a map from identifier
to expression). Every such rewrite below is restated as "decide at the
close from the tables, mark, and let the walk of the seal write it".
Counts are never read from the tree: `Uses::built` and `Uses::remaining`
(`bir/lower/scope.rs`) are tables of the lowering, above the interface.

**The four slices.** "Reads" and "writes" name the legacy pass; "through
the interface" says what the lowering uses instead. None of the four is
designed here beyond this: each has a design step of its own (T4g's is
commit 1 of 11.6), and what this section decides is that the design can be
written against the interface and gated before the flip.

| Slice | Reads and writes today | Through the interface, before the builder is behind it | Cost of the move |
| --- | --- | --- | --- |
| T4g, P3 | `lambda/js_pass_tailcall_inline.rs`. Reads: `UseCounts` (occurrences by identifier, purity of each declaration's value), the export set, `collect_tail_callees`, the site test of `TailcallInlineState::try_inline_single_return_statement` (last statement of a list, `return f(args)`, `f` a variable or a function literal), `inline_function_decl_from_variable` (not a method, not `async`, no directive), `inline_named_call` (`active_decls`, the arity), `immutable_param_mask` (`block_assigns_ident`: a walk of the body), `is_substitutable_constant` of each argument. Writes: `inline_tailcall_call` (a `let p = arg` per parameter that is not substituted, then `SubstituteInline` over the body: renamed or replaced parameters, pruned conditionals, shadowing), the status of every declaration (`transform_statement`: a dead pure one is dropped, a dead impure one becomes its value) | Reads, all above the interface or one row: `Uses::built`; the `STRICT` flag and `aux` (the `LetKind`) of the declaration's row; the function's header through the row's payload (`FuncId`); the site as `scope::return_sites` records it today, read through the interface's by-reference operand reads; a parameter is assigned: `VarFlags::ASSIGNED`, which the lowering maintains (no walk). Writes: the callee's declaration is a statement of the run being closed (E1): it is taken, the function literal taken apart (`Js::into_function`), and the body parked. The substitution runs over the owned body (`Js::substitute`: one step per node of a body that is inlined, each body once). The site: when its `return` is a statement of the same run, E1; when it is inside a list that closed earlier, E2 (the `return`'s row gets the parked slot) and E3 writes the body there, with the `if` of F5 when the site is under a returned conditional, marked "test not entered" | The slice itself (11.6 gives its size). Below the interface: `park`, `into_function` and `substitute`, each with a body for `Bir` rows (deleted by T6s) and one for the builder (T6v, or T4g when T6v has landed). 11.6 changes in three places, listed below |
| T4d, P4 | `lambda/js_pass_record_rest.rs`: `RecordRest::block_items` (last statement first), `materialize_fields`, `replace_source_fields`, `map_statement`. Reads: a declaration or a `return` whose value is a record rest; the statements after it in the same list, through blocks, declarations, expression statements and `return`s, and through ten expression kinds (`map_expr`); every `source.label` (`source_field`). Writes: `let x = source.label` is deleted and `x` becomes the binder; other reads become a fresh identifier (`field_ident_name`); `__unused<i>`; for a returned record rest a fresh `rest` and its declaration | The declaration and the statements after it are statements of the run being closed (E1). Each is taken, its value walked through the kinds `map_expr` enters by taking it apart and rebuilding it with the plain constructors, and put back. P4 runs after P1, so the walk reads through the reshaping as `return_sites` does: a conditional or a sequence in statement or `return` position is an `if` or several statements for P4, which does not enter an `if`; the rule is stated on the statement the lowering wrote. It runs only in a run that holds a record rest (one bit of the run, set where `record.rs` builds one) | The slice (about 300 lines and its rule tests). Nothing below the interface that T6k to T6q do not already need. Its fresh identifiers are created at the close, not after the lowering: risk 1 of section 12 |
| T4e, P5 | `lambda/js_pass_flatten_and_mark_dead.rs`: `Substitute::{statement, expression, try_substitute_caml_block_projection, substituted_caml_block_item}`, `should_materialize_block_binding_items`, `is_simple_block_binding_item`, `mark_dead_code`, `collect_mark_dead_states_*`, `apply_mark_dead_states_*`. Reads: the status P3 gave a declaration; a lexical declaration of an immutable block literal with two or more fields; whether each field is simple; every later `x[i]` and `x.f` of the variable, anywhere after it in program order (the map is not scoped); for the dead marks, occurrences after or before a declaration, one level. Writes: `x_0`, `x_1` declared before `x`; a read replaced by a simple field; statuses the printer reads | The declaration is in the run being closed (E1): materialising takes the literal apart and stages the fresh declarations before it. The reads are already recorded as sites (11.4, "Facts recorded while lowering"); the decision and its effect on `remaining` are taken from that chain at the close, by id, without touching a node. A read is rewritten by the walk of the seal (E3): its row carries `SEAL` from the moment it is built over a variable that has a block-literal fact, so the descent the seal already makes finds it. A dead declaration of the run is dropped or made its value at E1; one whose list closed earlier (finding 3, the late zero) is marked (E2) and omitted by the walk | The slice. Below the interface: nothing new. It needs T6u (the walk rewrites) and the `SEAL` flag settable by the lowering on a field read (`Js::index`, `Js::dot`) |
| T4f, P6 | `lambda/js_shake.rs`: `shake_program`, `flatten_toplevel_block`, `live_idents`, `free_variables_of_expression`, `free_variables_of_statement`, `js_statement_no_side_effects`. Reads: the top-level list with nested blocks spliced and dead declarations dropped; the export set; per declaration the free variables of its value and whether it is strictly pure; per other statement whether it has an effect and its free variables. Writes: a filter of the list | The rows of the top level exist (`export::Row`, T4a). Strict purity of a declaration's value is its row's flag; of a compound statement it is the `STRICT` flag of the statement's row, which the interface gives every statement (changes T6b: see D2 (a)). The references of a top-level statement are the sites of the top-level variables, each mapped to its row through the owner of its node (`export::row_of` today; `Js::owner` under the interface, D2 (f)). The worklist of `live_idents` runs over rows; statements that are not live are not written | The slice (about 250 lines). Below the interface: `Js::owner`, which T6q needs for `export.rs` in any case |

**What has to hold for each T4 slice to be gated before the flip**, and
what was not shown:

- *Storage.* All four run on `Bir` rows through the interface, and
  `bridge_j::export_lowered` still gives the remaining legacy passes a
  `JsArena`. So `after` stays "both sides through the passes that have not
  left", unchanged in kind until T4f, and `before` moves once, at T6u, to
  "the legacy program after P1 and P2 against the lowering's program".
- *The splice at the seal changes when names and occurrences are final.*
  Counts are tables, so D (the dead marks) reads `remaining` after the
  effects of A to C were subtracted at the close; the walk of the seal only
  writes. That the effects of a splice on `remaining` (a pruned branch, a
  renamed parameter) can be computed at the close without the edit is
  argued above from `SubstituteInline` (it reads only the body it is
  given), not tested. T4g's design step has to show it or move the
  substitution to the close and leave only the placement to the seal, which
  E1 allows (the body is owned when its declaration's run closes).
- *A run is closed more than once* ("T4c design", "as built"): unchanged by
  the interface, and still T4g's first question.
- *What is not possible in this order* and is not needed: running a legacy
  pass on the builder's program. No slice after the flip needs one.

**The order.** One row per slice from the first that touches the lowering.
"Protects it" is what a pull request of the slice must show at zero
differences; "corpora" are the runtime library, tests/tests and the
fixtures through `scripts/test_backend_coverage.py`, and the application
through a `RESCRIPT_BACKEND=check` build.

| Slice | What it does | Depends on | What protects it |
| --- | --- | --- | --- |
| T6k to T6q | The lowering's files stop naming J opcodes, a group of files a slice; storage is `Bir` rows | T6k first | Check mode as today: `before` and `after`, texts and mappings, on the corpora; `compare_decisions`; the name comparison of T5b; the allocation pins of `bir/lower/unit.rs` |
| T6r | `names.rs`, `globals.rs` behind the statement interface; the external-shadow decision in the replay's walk | T6k to T6q | The same; `globals_qualified` equal before and after on every corpus unit |
| T6u | F1 to F8 in the replay's walk (`bir/lower/seal.rs`); the new side stops running `apply_js_flatten_pass` | T6r | `before` is now "legacy after P1 and P2" against the lowering's program; `after` unchanged; `compare_decisions` on the lowering's own program; the tests of "T4c design" (c) and of T4b keep both texts |
| T4g | Step A with the splice | T6u | `after`: the new side runs P4, P5, P6; `before` moves to "legacy after P1, P2, P3"; `compare_decisions` stays (it compares what the lowering decided with what P3 decides on the legacy side) |
| T4d | Step B | T4g | `after`: the new side runs P5, P6; `before` after P4 |
| T4e | Steps C and D | T4d | `after`: the new side runs P6; `before` after P5 |
| T4f | The shake over rows | T4e, T6q | `before` and `after` are the same comparison: both final. The new side runs no legacy pass |
| T6v | The builder behind the interface, compiled for tests: the second implementation of `Js`; every rule test of `bir/lower/oracle_tests.rs` runs on both and compares the two texts after `js_reformat::reformat` | T6a to T6j, T6r; each T4 slice that landed before it | The tests; check mode is not touched |
| T6s | The flip: check mode instantiates the lowering with the builder; `Bir` rows of J, `bir/j/`, `bridge_j.rs` and the first implementation of `Js` are deleted | all above | The legacy final text, reformatted once, against what `oxc_codegen` prints for the builder's program, and the mappings, on the corpora; `compare_decisions` |
| T6t | Measurements, STATUS, the pins; the type parameter of the lowering is removed | T6s | - |

T6v may land before any T4 slice; a T4 slice that lands after it gives its
functions below the interface both bodies and runs its rule tests on both.
Phases A and B (T6a to T6j) run beside all of it, as before.

**The comparison is never suspended.** Until T6s the new side is the
lowering on `Bir` rows followed by the legacy passes that have not left,
compared with the legacy side before and after those passes: the check of
today, which sees every fact a remaining pass reads because the pass reads
it. At T6s no pass remains, the builder's program is the final program,
and its text is compared with the legacy final text. There is no period in
which the builder's program is compared with an intermediate legacy
program. What the comparison at T6s cannot see is what no final text
shows and no decision reads any more: nothing the passes read (they are
all decisions of the lowering by then, and their results are in the text);
only a fact that is wrong and unread, which is harmless until a later
slice reads it.

**The tail-call decision comparison stays across the flip.**
`shadow::compare_decisions` reads the lowering's `Decision` rows
(`scope.rs`, above the interface) and `js_pass_tailcall_inline::decisions`
on the legacy side's program. Neither depends on the storage, so it runs
unchanged after T4g and after T6s. Step 3 of 11.6 deletes both; that
deletion is struck and moves to the slice that deletes the legacy pass.

**`RESCRIPT_BACKEND=new`** keeps today's meaning through T6s. From T4f the
lowering's program is the final program, and from T6s it is the builder's:
the measurement "`new` below the default" and the switch of its meaning
belong to the slice after T6t, not to this order.

**Cost of this order against the one of "The gate"** (flip first, then
T4g to T4f against a moving point of the legacy side):

- Written twice: the functions below the interface that only a T4 slice
  needs (`park`, `into_function`, `substitute`): a body for `Bir` rows that
  T6s deletes. Estimated at 300 lines; not more, because the decisions,
  the marks and the walk are above the interface.
- Later: the flip waits for four decision slices, so check mode pays for
  the J rows, `export_lowered` and one legacy printing until then.
- Gained: every decision slice is compared through the legacy passes that
  follow it, which is the only check of the facts those passes read; the
  flip changes storage and printer and nothing else; `bridge_j.rs` is
  deleted in the slice that stops needing it.

**Changed against earlier statements.**

- "The gate", second and third bullet ("From the flip check mode compares
  the builder's text with the legacy program after the passes that have
  left"; "What is given up between T6s and T4f"): withdrawn. Nothing is
  given up; the point of `before` moves with each slice and the point of
  `after` never does.
- "T6 design" (e) and the row T6e of the cut: F1 to F8 are not part of the
  seal of `emit/builder_seal.rs`. They are T6u, over the interface. T6e is
  the print forms of (c), the descent, `release` and `copy`.
- "T6 design", "What T4g gets": unchanged in content; the `if` of F5 that
  the splice writes and its mark are E3 and E2 above.
- The re-cut table of 11.4, rows T4g to T4f, column "Needs": T4g needs
  T6u (not "T5, T6"); T4f needs T4e and T6q.
- 11.6 (the prompt of T4g): the precondition "T5 and T6 are merged"
  becomes "T6u is merged: `rg -n 'apply_js_flatten_pass'
  src/lambda/lam_compile.rs` shows the legacy side only"; step 3's "the
  callee's statements take the place of the `return`" is done with E1, E2
  and E3; "`compare_decisions` and `js_pass_tailcall_inline::decisions`
  are deleted" is struck. The prompt is reissued by the turn that designs
  T4g; it is not to be issued as it stands.
- 11.4, "The design", "A site in a closed list" and "Late zero": "in
  place" reads "marked by id and written by the walk of the seal".

#### T6: the interface

Status: design. The skeleton of its first slice is `bir/lower/js.rs`
(compiled for tests until T6k is built) with its tests in
`bir/lower/js_tests.rs`; the functions and their costs are the doc
comments there, and this section says why they are what they are. "Rows"
is the first implementation (J rows of `Bir`, as today); "the builder" is
the second (`emit/builder.rs` and the rules of phase B).

**(a) What the lowering calls.**

*The shape.* One trait, `Js` (`bir/lower/js.rs`), with the statement half
in a second trait `JsStmt: Js` (`bir/lower/js_stmt.rs`, T6l). The lowering
is generic over it: `State<'a, B: JsStmt>` holds `js: B` and keeps its
pools (`arena`, which stays a `Bir` until the flip and is named `Pools` in
every signature of the interface). A call is `self.js.bin(&mut self.arena,
op, left, right)`: the implementation and the pools are two fields, so the
borrow is of two fields and no wrapper type is needed. The pools are a
parameter because the builder needs them too (a name is a `StrId`, a
number a `ConstId`, a call's information a `JsId`), and because Rows keeps
its nodes in the same `Bir`.

*The handles.*

| Type | Rows | The builder | Bytes (Rows / builder) |
| --- | --- | --- | --- |
| `B::E`, an expression in flight; not `Copy` | `rows::E(NodeId)` | `J<'a>` | 4 / 24 |
| `B::S`, a statement in flight; not `Copy` (T6l) | `rows::S(NodeId)` | `S<'a>` | 4 / 24 |
| `B::L`, a statement list in flight; `Copy` (T6l) | `ListId` | `List` | 4 / 8 |
| `B::Ref<'r>`, a node read by reference; `Copy` | `NodeId` | `&'r Expression<'a>` with the builder | 4 / 8 |
| `Mark`, where the operands of the next list constructor start | an index into `Rows::operands` | `builder::Mark` | 4 / 4 |
| an id (`u32`): the row of a node, for a mark or a site | the `NodeId` | the `node_id` | 4 / 4 |

A handle is consumed by the function it is given to. That is the whole
ownership rule, and the compiler enforces it for both implementations
because the generic code has no `Copy` bound to use. Rows keeps its
run-time check (`Bir`'s "attached twice") until the flip.

*Construction.* Every J and S operation the lowering builds today (the
three construction tables of the inventory) has one function. Two
families, as `bir/j/plain.rs` and `bir/j/norm.rs` are two families today:
a **plain** function builds the node it is asked for (name without
prefix: `seq`, `bin_plain`, `not_plain`); a **rule** function is a row of
BACKEND_LOWERING 6 and may return an operand, a literal or another node
(`bin` is J-E4, `not` J-E8, `cond` J-E7, `seq_rule` J-M1, and so on, named
in (c)). The lowering chooses the family where it chooses today (`plain::`
or `norm::`); the choice is the lowering's decision and is not moved.

| Today | Function of `Js` | Cost |
| --- | --- | --- |
| `Var` | `var(a, var)` | O(1); counts the occurrence and records the site |
| `JQualified` | `qualified(a, module, member)` | O(1); counts the import use, records the site |
| `JNumber` | `int(a, i32)`, `number(a, ConstId)`, `char(a, ConstId, u32)` | O(1) |
| `JStr`, `JBool`, `JNull`, `JUndefined`, `JJson`, `JRaw` | `string(a, &str)`, `str(a, StrId)`, `boolean`, `null`, `undefined(a, unit)`, `json(a, StrId)`, `raw(a, StrId, is_statement)` | O(1), `string` O(length) |
| `JBin` | `bin_plain(a, op, l, r)`; rule `bin` | O(1); `bin`: (c) |
| `JNot`, `JBnot`, `JTypeof`, `JIn`, `JIsNullish`, `JLength`, `JStrAppend`, `JAwait`, `JSpread` | `not_plain`, `bnot_plain`, `typeof_plain`, `in_`, `await_`, `spread`; rules `not`, `bnot`, `typeof_`, `is_nullish`, `length`, `append` | O(1); rules: (c) |
| `JCond`, `JSeq` | `seq`; rules `cond`, `seq_rule` | O(1); (c) |
| `JIndex`, `JDot` | `index(a, object, index)`, `dot(a, object, StrId, FieldPos, tag)`; rules `project`, `poly_var` (J-M11) | O(1) |
| `JCall`, `JNew`, `JFlatCall`, `JTagged` | `call(a, callee, mark, JsId)`, `new_(a, callee, mark)`, `flat_call(a, callee, args)`, `tagged(a, tag, mark, JsId)` | one step per operand since the mark |
| `JArray`, `JBlockLit`, `JObject`, `JTemplate`, `JJsx` | `array(a, mark, mutable)`, `block(a, mark, JsId, mutable)`, `object(a, mark, JsId)`, `jsx(a, mark, JsId, has_children)`; rule `template(a, segments, mark)` (J-M12) | one step per operand since the mark |
| `JOptional`, `JRecordRest` | `optional(a, value, identity)`, `record_rest(a, value, JsId)` | O(1) |
| `JFun` | `function(a, FuncId, body: B::L)` (T6l: it takes a list) | O(1); the list is consumed, not copied |
| every `S` operation | `JsStmt` (T6l): `exp`, `exp_rule` (J-S1), `declare`, `rest`, `return_`, `throw`, `debugger`, `break_`, `continue_`, `block`, `if_plain`, `if_` (J-S3), `while_`, `for_range`, `for_range_existing`, `for_of`, `switch`, `try_`; lists `stage_mark`, `stage`, `list` | O(1), or one step per statement of the lists consumed; `if_`: (c) |

Operand lists go through the operand stack of the implementation
(`mark`, `push`), as in the builder: no `&[NodeId]` and no `Vec` per call.
Rows needs one new vector for it (`Rows::operands`, reserved once where
the unit's state is made); that is the one allocation this design adds to
a unit, and it is why each of the four allocation pins of
`bir/lower/unit.rs` rises by exactly one in T6k (85, 102, 85, 155 become
86, 103, 86, 156). Observed in the design turn with the `State` of T6k
and a reserve of 64 operands (see "T6k: the skeleton" below); T6k's prompt
makes any other movement of a pin a reason to stop.

*Reading back.* The read-back table of the inventory has four kinds of
read. None needs a walk, because each is one of these:

| Read today | Read instead | Why no walk |
| --- | --- | --- |
| A flag of a node the lowering holds (`flags().contains(STRICT)`, `delay_safe`, `strictly_pure`, `PURE` of an argument; `args.rs`, `cond.rs`, `expr.rs`, `ffi_args.rs`, `mod.rs::seq`, `loops.rs`) | `has(a, r, flag)` on the handle's reference | The flag was computed where the node was built (Rows: the node's flags; the builder: the row in the handle) |
| The kind of a node it holds, and a literal's value (`View::JUndefined`, `JOptional`, `JStr`, `primitive_int`, `primitive_bool`, `primitive_string`, `primitive_bigint`) | `kind(a, r)`, `aux(a, r)`, `int(a, r)`, `text(a, r)`, `bigint(a, r)`, `var_of(a, r)`, `qualified_of(a, r)` | O(1) each: the row, or one pool entry |
| A child, or a child of a child (`JCall` of a `JQualified` in `primitive_int_comparison`; the elements of an array of pairs in `Pmakedict`; `JDot` chains in `jsx_tag`, `copy_replacement`; `JSeq` ends in `extract_exports`) | `operand(a, r, i)` gives the reference of operand `i`; `arity(a, r)` | Each step is one read chosen by the caller; the depth is the pattern's, which is fixed (two for the runtime `compare` call, three for a dictionary entry) or counted where it is a chain (`descent` steps of the JSX tag and of `copy_replacement`, as today) |
| Taking a node apart to keep a part (`detach` then `release`: `positive`, `PvalFromOption`, `evaluate_now`, `fold_return_tail`, `hold_external_arg`, `primitive_int_comparison`) | `keep_operand(a, e, i)` for one part of a node with a fixed number of operands (the rest is released); `unpack(a, e) -> Mark` for a list (its operands go onto the operand stack, in order; `take(a, mark, i)` moves one out, `drop_operands(a, mark)` releases what is left) | The parts are operands of the node in hand; releasing the rest is `release`'s cost, one step per node released |
| A statement of a run or of a list (`single_return`, `terminal`, `merge_tail_guard`, `returns_after_effects`, empty blocks; `tail.rs`; `switch.rs`) | `JsStmt` (T6l): `stmt_kind(a, &S)`, `stmt_has`, `value_of(a, &S) -> Ref` and, for a list in flight, `len(l)`, `kind_at(a, l, i)`, `take_at(a, l, i)` and `with_stmt_at(a, l, i, read)`, which lends statement `i` to a reader where it is ("T6x-b: an output's value, as built" (b)) | The statement stack owns the handles of a run; a list in flight is read by position |
| Equality of two expressions (`same_reusable_value` in `export.rs`; inside the rules) | `equal(a, r1, r2)`, with the cost of `bir/j/equal.rs` (stops at the first difference; pairs on an explicit stack) | It is a rule's read, already counted |
| The parent of a node (`export::row_of`, `declared`; `globals::shadowed`, `binding_scope`; the prelude of `names::replay`) | `owner(a, id)`: (f). `globals.rs` and the prelude stop needing it: (d) | - |
| Cold data: a location, a comment, a character (`set_cold`, `JS_LOC_PRESENT`, `js_char`) | `locate(a, &mut E, LamLoc)`, `located(a, r)`, `comment(a, &mut E, StrId)`, `copy_cold(a, from: Ref, &mut E)` | O(1). The builder sets the span and drops the comment (decoration comments stay dropped; the pure annotation is the `pure` bit of the call's `JsId`) |

`release(a, e)` and `copy(a, r) -> E` are the two functions that enter an
expression (one step per node released or copied, with the reference
bookkeeping `Bir::release` does today). The lowering calls `copy` only
where it calls `copy_j` or duplicates a leaf today.

*What changes in "T6 design" because of (a).*

- `Kind` gets the kinds of every J and S operation in this turn (it had
  the 31 of T6a and T6b): the interface reads kinds the builder does not
  build yet. T6c and T6d build constructors for kinds that exist; they
  add none. `Kind`, `Row`, `flag`, `num` and `var` move to `emit/row.rs`,
  which T6k compiles outside tests.
- A statement's row carries `STRICT` (the statement has no effect as
  `js_statement_no_side_effects` reads it), computed where the statement
  is built from the rows of what it holds. "A statement's row has no
  other flag" (T6b) is withdrawn for this one flag; T6v adds it to the
  builder, with its test. `export::has_toplevel_effect` reads it today by
  reading a compound statement until its first effect, and T4f reads it
  for every top-level statement.
- A flag `JSX` (bit 7): (e).

**(b) One set of call sites, two implementations.**

- *Before T6s* the lowering is instantiated once, `State<'_, Rows>`.
  `Rows` (`bir/j/rows.rs`) is a struct with the operand stack and nothing
  else; each function is the call of `bir/j/plain.rs`, `bir/j/norm.rs` or
  `Bir` that the lowering makes today, so the J rows written are the same
  rows and check mode cannot move.
- *From T6v* a second implementation exists, `Oxc<'a>`
  (`bir/lower/js_oxc.rs`: the `Builder`, the owner column of (f), the
  parked bodies), compiled for tests. The oracle tests of the lowering are
  then generic and run on both.
- *At T6s* check mode instantiates `State<'_, Oxc<'_>>`, and `Rows`, the J
  opcodes and `bir/j/` are deleted. T6t removes the type parameter (one
  implementation is left; a trait with one implementation stays only as
  long as it takes to delete it).

What the compiler monomorphizes: every function of `bir/lower` once per
implementation that is instantiated in the build: once (`Rows`) in a
release build until T6s, once (`Oxc`) after it, twice in a test build
from T6v to T6s. There is no `dyn Js`, no enum of implementations, and no
branch on the implementation: a call of the interface is a direct call
that the compiler can inline (every function of `Rows` is `#[inline]`
over a call that exists today). The default build runs neither
instantiation.

*The transition inside phase C.* The output types (`Out`, `Probed`,
`Free`, the slots of `StatementStack`) hold `NodeId` until T6x converts
`out.rs`, so that the slices between can run in any order. A converted
file crosses that boundary with three functions that only `Rows` can
have: `B::from_node(NodeId) -> B::E`, `B::node(B::E) -> NodeId` and
`B::at(NodeId) -> B::Ref<'static>` (and the statement twins in
`JsStmt`). They are part of the trait until T6x deletes them and their
last call; the end state of each slice counts them.

**(c) The rules of BACKEND_LOWERING 6.** Every row is behind the
interface: the lowering calls a function and does not know whether a rule
fired. "After the flip" is the file of phase B.

| Rule | Function of the interface | Rows calls | After the flip |
| --- | --- | --- | --- |
| J-E1 | `append` | `je1_string_append` | `emit/rules_e.rs` |
| J-E2 | `length(a, e, LengthObject)` | `je2_length` | `rules_e.rs` |
| J-E3 | `is_nullish` | `je3_is_null_or_undefined` | `rules_e.rs` |
| J-E4 | `bin` | `je4_bin` | `rules_e.rs` |
| J-E5, J-E6 | `and`, `or` | `je5_js_and`, `je6_js_or` | `rules_logic.rs` |
| J-E7 | `cond` | `je7_cond` | `rules_logic.rs` |
| J-E8 | `not` | `je8_not` | `rules_e.rs` |
| J-E9, J-E10 | none: reached from `and`, `or` and `cond` only (no call in `bir/lower`) | `je9_simplify_and`, `je10_simplify_or` | `rules_logic.rs` |
| J-S1 | `exp_rule` | `js1_exp` | `rules_s.rs` |
| J-S2, J-S5 | none: no call in `bir/lower`; the lowering unnests on its stack (`cond.rs::unnest`) | `js2_block`, `js5_unnest_block` | not ported: deleted with `norm.rs` |
| J-S3 | `if_`, and `if_head` for the form that works on runs (`simplify_if_head`) | `js3_simplify_if`, `simplify_if_head` | `rules_s.rs` |
| J-S4 | `switch` (every statement constructor applies it today through `plain::statement`; only a switch can match) | `js4_normalize` | `rules_s.rs` |
| J-M0 | `without_pure(a, e) -> Option<E>` | `jm0_remove_pure_subexpression` | `rules_m.rs` |
| J-M1 | `seq_rule` | `jm1_js_seq` | `rules_m.rs` |
| J-M2 | `nullish_eq(a, neq, l, r)`, `int_eq` | `jm2_nullish_strict_comparison`, `jm2_int_equality` | `rules_m.rs` |
| J-M3 to J-M8, J-M10, J-M13 | `to_int32`, `int_or`, `int_add(a, subtract, l, r)`, `int_mul`, `int_pow`, `int_lsl`, `int_lsr`, `int_xor`, `int_and`, `bnot`, `int_div(a, check, l, r)`, `int_mod` | the `jm*` function of the same row | `rules_m.rs` |
| J-M9 | `typeof_` | `jm9_typeof` | `rules_m.rs` |
| J-M11 | `project(a, e, field, index) -> Result<E, E>`, `poly_var(a, e, payload)` | `jm11_projection`, `jm11_poly_var_access` | `rules_m.rs` |
| J-M12 | `template` | `jm12_interpolated_template` | `rules_m.rs` |
| J-M14 | `effect(a, e)`: stages the statements of a value used for its effect; `effect_if_impure` | `jm14_push_effect_expression`, `jm14_push_s_if_empty`; `jm14_push_s_exp` has no call in `bir/lower` and is not ported | `rules_s.rs` |

What stays a decision of the lowering, in the file it is in today: the
literal folds of the primitives (`prim_cmp.rs`: `comparison_constant`,
the bool and literal comparisons, `primitive_min_max`; `prim.rs`:
`Psome`'s identity test, `PisNotNone`, `Plsrint` by zero), rows R1 to R6
of the conditional (`cond.rs`), argument sequencing (`args.rs`), the
grouping of switch cases, the choice between `bin` and `bin_plain`, and
every decision of 11.4. They read the interface's readers and call its
constructors; none of them is a row of section 6.

**(d) `names.rs` and `globals.rs` (T6r), and the seal (T6u).**

*The walk.* `names::replay` becomes generic over `JsStmt` and keeps its
shape: one frame per open list, no recursion. What it reads changes from
`bir.view(statement)` to the statement interface:

| The replay needs | Function of `JsStmt` | Cost |
| --- | --- | --- |
| The final lists of a statement, in print order (`Replay::child`) | `bodies(a, &S) -> u32` and `body(a, &mut S, i) -> B::L`: the list is taken out of the statement and `set_body(a, &mut S, i, B::L)` puts it back | O(1) each (Rows: the `ListId`; the builder: the arena vector moved in and out of the node) |
| The statements of a list, each once | `len`, `take_at(a, l, i) -> S`, then `stage` and `list` for the list that replaces it | one move per statement (4 bytes on rows, 24 on the builder) |
| The binders of a statement (`Replay::statement`) | `stmt_kind`, `binder(a, &S) -> Option<VarId>`, `rest_fields`, `stmt_aux` (the status of a declaration) | O(1) |
| The function literals of a statement, in print order | `functions(a, &mut S, visit)`: the descent below `HAS_FUN`, calling `visit(FuncId, &mut B::L)` with the body's list for each literal; `SwitchStats::descent_steps` counts one per operand read | the descent of "T6 design" (d): one row read per operand of each ancestor of a literal inside its statement |
| References to JavaScript globals in a statement | `globals(a, &mut S, visit)`: the same descent below `HAS_GLOBAL`, calling `visit(VarId) -> bool`; `true` makes the reference `globalThis.name` | the same form of cost |

The prelude, `Scratch::marks`, `Scratch::next` and `ambiguous_orders` are
deleted by T6r, not by T6s: with the descent, operand order is print
order on rows too. The replay rebuilds each list it walks (take, stage,
`list`); "it rewrites a statement list only when a statement of it
changes" ("T6 design" (e)) is given up for one move per statement, which
is what makes one walk serve both implementations. The step test of T6r
states it: moves equal statements.

*The external-shadow decision in the walk.* `globals::decide` marks the
scope of every binding that prints with a referenced global's name and
then climbs from each reference (`shadowed`). Top down there is nothing
to climb: the walk keeps, per referenced global name (the rows of
`Globals`), a count of the bindings of that name that cover the place it
is at. It adds one when it enters what `binding_scope` returns for a
binder (a list for its declarations, read from the rows of the list
before its statements are walked, with an explicit block's declarations
counted in the list it is spliced into; a function for its parameters; a
loop for its variable; a handler for its catch variable; the cases of a
`switch` for the declarations of all of them) and subtracts on leaving. A
reference found by `globals` is qualified when its name's count is not
zero or an imported module prints with the name. Cost: one step per
binder that prints with a referenced global's name, on entry and on exit,
and the descent; nothing for a unit that references no global
(`Globals::names` is empty, as today). `Globals::marks` and the epochs
are deleted by T6r. Step 3 of `decide` (the table of names) is unchanged.

*The seal* (T6u, `bir/lower/seal.rs`) is the same walk with one more
step where a statement is taken out of its list: F1 to F8 of "T6 design"
(e) are applied to the statement in hand, and what they produce is staged
instead of it, each result offered to the rules again (an explicit work
stack; a result that is not an expression statement, a `return` or a
block is final). The functions it uses are the lowering's: `keep_operand`
and `unpack` on the value, `not`, `if_plain`, `return_`, `exp`,
`release`. Two marks direct it: a statement whose row has none of
`SEAL`, `HAS_FUN`, `HAS_GLOBAL`, `JSX` and is not an expression
statement, a `return` or a block is staged without being read further;
the test of an `if` that F3, F5 or a splice wrote is not entered (the
mark of E2). After the rules, and after the names of the list, the
implementation writes its print forms: `seal(a, l, Position) -> B::L`,
which is the identity on rows (the legacy printer writes them) and T6e's
work on the builder. `Position` is 8 bytes: `top`, `tail`, and the
indentation of (e).

**(e) JSX in preserve mode** (review decision 6). A preserved JSX element
prints its children on lines of their own, indented by where the element
stands (`Build::jsx_indent` in `emit/build.rs`: one level per enclosing
block and function body, and one or two per enclosing member, index,
conditional and call argument). That is known going down. So the element
is built with its whitespace children empty and its row, and every row
above it up to its statement, carries `JSX` (bit 7 of `Row::flags`,
inherited as `HAS_FUN` is). The seal knows the indentation of the list it
writes; `seal` descends below `JSX` adding the levels of the parents it
passes (read from their rows' kinds) and writes each whitespace child
where it reaches the element. Cost: one row read per operand of each
ancestor of a preserved element inside its statement, in `descent_steps`,
and one arena string per whitespace child, which the emitter allocates
today. Rows ignores the flag. This is T6e's (the descent) and T6d's (the
element with empty whitespace); it is closed when `tests/tests` has no
unit left uncompared for JSX on the builder's path, which T6v's tests
state for the one unit the ratchet counts. Not tried.

**(f) The readers of J rows outside `bir/lower` and `bir/j`.**

| Reader | What happens to it |
| --- | --- |
| `bridge_j::Exporter::build`, `export_lowered`, `export_js` | Kept until T6s: it is how the remaining legacy passes and the legacy printer read the lowering's program. Deleted by T6s |
| `bridge_j::Importer`, `import_js`; `shadow::check_js` (the JS bridge's round trip) | Deleted by T6s with the J opcodes ("T6 design" (f)) |
| `validate.rs`, the J arms | Kept until T6s (Rows relies on it); deleted by T6s |
| `edit.rs`: `attach_list`, the pooled constructors (`block_from_list`, `call_from_list`, `switch_from_list`, `object_from_list`, `jsx_from_list`, `explicit_block_from_list`) | Called by `Rows` only from T6l on (the lowering's `rg` end state excludes them); deleted by T6s |
| `edit.rs`: `bind`, `unbind`, `value_fact`, `binding_facts`, `update_facts`, `register_kind`, `mark_captures` on J operations: binders, variable facts (`ASSIGNED`), import uses, captures | The facts are the lowering's and stay: after the flip `Oxc` calls the same table updates from its constructors (`declare` binds, `bin` with `=` marks its target assigned, `qualified` counts an import use, `function` closes captures). The J arms inside `edit.rs` are deleted by T6s; the tables (`vars`, `js_scope`) are not |
| `node.rs`: `pack`, `view`, `remap`, the accessors of J operations | Deleted by T6s with the opcodes |
| `shadow::prepare_lower`, `compare_decisions`, `check_lower` | `prepare_lower` calls the lowering and `export_lowered` until T6s, the lowering and `oxc_codegen` after; `compare_decisions` reads decision rows and is unchanged; `check_lower` compares as "The order of the flip" says |
| `replay.rs` (the Lambda constructor replay) | Reads no J row; unchanged |
| `export.rs` (inside `bir/lower`, but the one reader of parents that stays): `row_of`, `declared`, `mentions` | `owner(a, id) -> Option<u32>`: the id of the node a node is an operand of. Rows: `Bir::parents`. The builder has no parent, and "T6 design" (f) said a position fact is recorded where the reference is built; it cannot be ("T4a as built": a reference is built before its statement has a slot, and `row_of` climbs when the top level is complete). So `Oxc` keeps one column, `owners: Vec<u32>` dense by `node_id`, written by the function that attaches an operand: one store per operand, 4 bytes a node, in the lowering's implementation and not in `Builder` (the emitter of T6f does not pay it). `row_of` and `declared` read kinds through `kind_of(a, id)`. The callee test of `mentions` (`callee == site.node`) becomes `operand_index(a, id) == 0` of a call's row. This is the one new per-node cost of the interface on the builder's path; it is counted in T6v's step test and measured at T6s |

**(g) The instruction budget.**

- *The default path* runs no function of `bir/lower`, `bir/j` or `emit`.
  Every slice of phase C must leave the CI job `Instruction count` within
  +0.02%; that job is the measurement, per pull request.
- *Check mode* is not measured by CI. Each slice of phase C states two
  numbers in its pull request: the instructions of a clean
  `RESCRIPT_BACKEND=check` build of `tests/tests` before and after
  (`scripts/compare_build_instructions.py` with the variable set, one
  worker thread; noise is about 0.1%). The budget is +0.1% a slice and
  +0.3% for T6k to T6x together. Why it should be level: `Rows` adds no
  work to a construction (the call it wraps is the call of today) and a
  read is the load of today plus, for `has`, three shifts and masks to
  the interface's bits. Two things can cost and are named: `operands`
  (one push and one pop per operand of a list constructor that takes a
  slice today) and the rebuild of each list in T6r's walk (one move per
  statement). T6k's pull request is the first measurement; if `operands`
  alone exceeds the budget the builder stops and reports, and the fix is
  a slice-taking twin of the list constructors on `Rows` only.
- *Not measured in this turn*: anything. The costs above are read from
  the code.

#### T6: the cut of the interface, revisited

Replaces the rows T6e and T6k to T6t of "T6: the cut". Three things
changed the cut: `prim.rs`, `cond.rs` and `switch.rs` are each a slice's
worth of call sites (the inventory counts 83, 57 and 40 places), so the
interface itself cannot share a slice with the largest file; `out.rs`
goes last, so that the slices between can run in any order ((b)); and
the order of the flip adds T6u and T6v and puts the T4 slices before
T6s.

"Own" names what a slice may change; a function not named belongs to
another slice. Every slice of phase C also owns the `impl` header lines
of the files it converts and nothing else in them. Lines are added or
changed lines without tests.

| Slice | Files | Own | Depends on | May run beside | Lines | Default path |
| --- | --- | --- | --- | --- | ---: | --- |
| T6e (changed) | `emit/builder_seal.rs` | The print forms of "T6 design" (c), the descent below `HAS_FUN`, `SEAL` and `JSX`, `Builder::release`, `Builder::copy`. Not F1 to F8 | T6d | T6g to T6j, phase C | 450 | no |
| T6k | `bir/lower/js.rs`, `bir/j/rows.rs`, `emit/row.rs`; `bir/lower/prim_cmp.rs`, `prim_block.rs`; `State` | Every function of `Js` on `Rows`; `State<'a, B>` and the `impl` headers of every file of `bir/lower`; all of `prim_cmp.rs` and `prim_block.rs`; the 22 call expressions of their functions in `prim.rs`, `rec.rs` and `mod.rs` (wrapped, see "T6k: the skeleton") | - | phases A, B | 650 | no |
| T6l | `bir/lower/js_stmt.rs`, `bir/j/rows_stmt.rs`; `assign.rs`, `loops.rs`, `try_.rs` | Every function of `JsStmt` on `Rows` that "T6l: the skeleton" names; the bound `B: JsStmt` of `State` and of every `impl` header; all of the three files | T6k | phases A, B | 600 | no |
| T6m | `prim.rs`, `konst.rs`, `record.rs`, `import.rs` | All of the four files | T6l | T6n, T6o, T6p, T6w, T6q | 600 | no |
| T6n | `cond.rs`, `expr.rs` | All of the two files | T6l | T6m, T6o, T6p, T6w, T6q | 600 | no |
| T6o | `switch.rs`, `variant.rs`, `untagged.rs`, `location.rs` | All of the four files | T6l | T6m, T6n, T6p, T6w, T6q | 600 | no |
| T6p | `args.rs`, `call.rs`, `ffi_args.rs`, `external.rs`, `jsx.rs` | All of the five files | T6l | T6m, T6n, T6o, T6w, T6q | 600 | no |
| T6w | `tail.rs`, `rec.rs`, `exit.rs`, `label.rs` | All of the four files | T6l | T6m, T6n, T6o, T6p, T6q | 400 | no |
| T6q | `export.rs`, `close.rs`, `scope.rs` | All of the three files; `Js::owner`, `kind_of`, `operand_index` on `Rows` | T6l | T6m, T6n, T6o, T6p, T6w | 600 | no |
| T6x | `out.rs`, `mod.rs`, `unit.rs`; the plan structs of the converted files | `Out<B>`, `Probed<B>`, `Free<B>`, `StatementStack<B>`; the `NodeId` and `ListId` fields of the plans (`loops::Plan`, `try_::Plan` and their like); `State::{leaf, seq, effect, complete_unit, complete, finish}`; deletes `from_node`, `node`, `at` and their statement twins from both traits and every call | T6m to T6q, T6w | - | 600 | no |
| T6r | `names.rs`, `globals.rs` | Both files; `JsStmt::{bodies, body, set_body, functions, globals, binder, rest_fields}` on `Rows` | T6x | phases A, B | 600 | no |
| T6u | `bir/lower/seal.rs`, `names.rs` (the call of the seal in `Replay::statements`), `lambda/lam_compile.rs` (the new side of `compile_deps_program_with_lower_check`), `bir/shadow.rs` (`prepare_lower`, `check_lower`) | F1 to F8; `JsStmt::seal` on `Rows` (the identity) | T6r | phases A, B | 450 | check mode only: needs the full output gate |
| T4g, T4d, T4e, T4f | as their prompts will say | 11.4, "The order of the flip" | T6u, in this order | T6v | - | check mode only |
| T6v | `bir/lower/js_oxc.rs`, `bir/lower/oracle_tests.rs`, `emit/builder.rs` (the `STRICT` flag of a statement) | `Oxc<'a>` and every function of `Js` and `JsStmt` on it | T6a to T6j, T6r | T6u, the T4 slices | 600 | no (compiled for tests) |
| T6s | `bir/`, `emit/`, `lambda/lam_compile.rs`, `bir/shadow.rs` | The flip | all above | - | 300, and about 9,000 deleted | check mode; deletes code the default build links: full output gate |
| T6t | docs, tests, `bir/lower` | Measurements on the four corpora, STATUS, `tests/backend_coverage.txt`, the allocation pins re-pinned with the builder's vectors named, the type parameter `B` removed | T6s | - | 100, and the mechanical removal | no |

**What each slice deletes**, in the same pull request:

| Slice | Deletes |
| --- | --- |
| T6k | In its two files: every `plain::`, `norm::` and `View::J` use; `State::primitive_int`, `primitive_bool`, `primitive_string` and `primitive_bigint` become calls of the readers and are deleted where they only forwarded |
| T6l to T6q, T6w | The same in their files; a helper of `State` that only wrapped a constructor (`State::pure_expression` when its last caller is converted, by the slice that converts it) |
| T6x | The three transitional functions and their twins; the `NodeId` in `Out`, `Free` and the stack's slots |
| T6r | `Replay::prelude`, `Scratch::{marks, next}`, `Replayed::ambiguous_orders`, `globals::{shadowed, binding_scope}`, `Globals::{marks, epoch}` |
| T6u | The call of `apply_js_flatten_pass` on the new side; `bridge_j::qualify`'s caller keeps its order |
| T4g to T4f | The call of one legacy pass on the new side, each |
| T6v | Nothing (it is the second implementation, for tests) |
| T6s | `bir/bridge_j.rs`, the J opcodes of `bir/node.rs`, `bir/j/`, `Rows`, the J arms of `validate.rs` and `edit.rs`, `Printed::{modules, finishes}`, the legacy printing of the new side in `shadow.rs` |
| T6t | The type parameter of `State` and of the output types |

**End state of each slice**, to paste with the output (`rg` runs in
`compiler-rust/`; "outside tests" means the match is not in a
`#[cfg(test)]` module, which is checked by reading the matches):

| Slice | Facts |
| --- | --- |
| T6k | `rg -c 'todo!\("T6k"\)' src/bir` prints nothing; `rg -n 'T6k build' src` is empty; `rg -n 'View::J\|Op::J\|View::S[A-Z]\|Op::S[A-Z]\|plain::\|norm::\|\.arena\.(view\|node\|release\|detach\|replace)\(' src/bir/lower/prim_cmp.rs src/bir/lower/prim_block.rs` matches only below `mod tests` of each file; `rg -n 'cfg\(test\)' -A1 src/bir/lower/mod.rs` does not show `mod js;` |
| T6l | The same `rg` for `assign.rs`, `loops.rs`, `try_.rs` with `block_from_list\|new_node\(\|pure_expression\|lists\.get` added to the pattern; `rg -c 'todo!\("T6l"\)' src/bir` prints nothing |
| T6m to T6q, T6w | The same `rg` for the slice's files, outside tests; `rg -c 'from_node\|B::node\(\|B::at\(' <files>` is pasted (it may only fall in T6x) |
| T6x | `rg -n 'from_node\|fn node\(\|fn at\(' src/bir` is empty; `rg -n 'NodeId' src/bir/lower/out.rs` matches only inside its tests |
| T6r | `rg -n 'View::J\|Op::J\|View::S[A-Z]\|Op::S[A-Z]\|parents\[' src/bir/lower` matches only inside `#[cfg(test)]` modules and `export.rs` has no `parents\[`; `rg -n 'ambiguous_orders\|fn prelude' src` is empty |
| T6u | `rg -n 'apply_js_flatten_pass' src/lambda/lam_compile.rs` shows the legacy side (`finish_lowered_output`) only |
| T6v | `rg -n 'impl.* JsStmt for' src` shows two implementations; the oracle tests run on both |
| T6s | As "T6: the cut" says for T6s, and `rg -n 'struct Rows' src` is empty |

What is designed to the level of a build prompt in this turn: T6k
(skeleton, acceptance tests, 11.9). T6l to T6x have their functions,
files and end state fixed here; each gets its skeleton and tests from a
design turn, T6l first. T6u, T6v and the T4 slices need a design turn
each.

#### T6k: the skeleton

Status: skeleton and acceptance tests committed; bodies are T6k's
(11.9). Files: `bir/lower/js.rs` (the trait, every function with its
cost), `bir/j/rows.rs` (`Rows`, 85 bodies `todo!("T6k")`, with a table in
its header that says what each body is), `bir/lower/js_tests.rs` (15
tests, 11 ignored as "T6k build"), `emit/row.rs` (`Kind`, `Row`, `flag`,
`num`, `var`, moved out of `emit/builder.rs`, which re-exports them). The
three modules are compiled for tests only until T6k's second commit.

**What ran, and against what.** A prototype of all 85 bodies was written,
the 15 tests were run against it (15 passed), and the bodies were then
taken out; with the bodies out, each of the 11 ignored tests fails with
`not yet implemented: T6k` and with nothing else, which is the mechanical
check that an ignored test reaches no body of a later slice (the tests
call `Rows`, `bir/j/plain.rs` and `bir/j/norm.rs` and nothing of the
lowering). A second, throw-away probe then did the rest of T6k on the
prototype: `State<'a, B>` with every `impl` header, and `prim_cmp.rs` and
`prim_block.rs` converted whole. With it `cargo test --lib bir::lower`
gave 514 passed and 4 failed, the 4 being the allocation pins, each by
exactly one (86, 103, 86, 156). The probe is not committed: the committed
tree is today's lowering, and its tests pass as before (`bir::lower` 518
passed and 11 ignored, `emit::builder` 26, `bir::j` 58).

**What the tests are.** The oracle form: the same nodes are built in two
arenas that start equal, once through `Js` on `Rows` and once with the
calls of `plain.rs` and `norm.rs` the lowering makes today, and
`Bir::dump` of the two must be equal (every node with its operation,
`aux`, flags and operands; every variable with its uses). No expected row
is written down. The rule functions are compared on 11 operands that the
rules treat differently, in every pair (22 binary rules, 10 unary). The
step test is a relation: steps at 10,000 minus steps at 1,000 equal nine
times the step from 1,000 to 2,000, for a nest, for a wide call and for
taking a wide call apart. The allocation test is a relation too: building
a call of 1,000 and of 10,000 arguments through a warm `Rows` allocates
less than building it with an argument vector, as the lowering does today.
No test pins a count that a later slice changes.

**Changes to "T6: the interface" that the skeleton made**, each with its
reason:

| Change | Reason |
| --- | --- |
| `int` (a) is `int_literal`; `int` is the reader | Two functions had one name |
| `not_plain`, `bnot_plain`, `char` are not in the trait | The lowering has no call of them today (`rg 'View::JNot\|View::JBnot' src/bir/lower` matches readers and tests only; a character literal is `number` of its constant, and the lowering sets a character on a node only when it copies one, which is `copy_cold`). A function without a caller is not added |
| `unpack(a, e) -> Mark` and `take(a, mark, i)` are `unpack_rev(a, e) -> u32` and `pop()` | `take` by index would leave a hole in the operand stack that the next `mark` could not describe. `unpack_rev` pushes the operands last to first, so `pop` returns them first to last, and every operand is moved out exactly once |
| `into_operand` is `keep_operand` | Clippy's convention for `into_` wants `self` by value; the crate builds without `allow` |
| `copy_leaf(a, r) -> E` is added | `primitive_min_max` copies a literal leaf without the bookkeeping of `copy` (no occurrence is counted for a literal). With it the function needs no `View` |
| `assume_strict(a, &mut E)` is added | The lowering sets `STRICT` on arrays, objects, blocks, optionals and functions it builds through `bir::j::pure_expression`, whatever their operands are. That is today's behaviour and it is kept: the function says so at the call. A leaf has the flag already (tested: a leaf built by `pure_expression` and the leaf of the interface dump alike), so the leaves need no second family. Whether the forced flag can disagree with the computed one is an open question of this turn |
| `text` returns `None` for a template whose one part has no cooked text | `State::primitive_string` does; `plain::string_of` returns the empty string. The lowering's reader is the one the interface replaces |
| `equal`, `owner`, `kind_of` as a trait function, `operand_index`, `park`, `effect`, `if_head` are not in the skeleton | They are T6l's, T6q's and the T4 slices' additions, each with the slice that has their first caller. `kind_of` exists as a free function of `rows.rs` (tested: every J and S operation has a kind of its own, and `Named` is no operation's) |
| The interface is `pub`, with `emit::row` | Outside tests the trait has, after T6k, 57 functions without a caller; a `pub(crate)` trait would need `#[cfg(test)]` on each, on its implementation and on the imports only they use, moved by every later slice. `bir::j::norm`, `bir::j::plain` and `bir::lower::out` are `pub` modules already. Tried both ways in the probe: the `pub` form compiles without a warning. T6t narrows it when the type parameter goes |
| A converted function takes and returns `B::E`; its callers in files of later slices are wrapped at the call (`B::node(self.f(B::from_node(x)))`) | The other form (convert inside, keep `NodeId` at the edge) makes a later slice change a signature in a file another slice owns: `primitive_set_field` is called from `prim.rs` (T6m) and `rec.rs` (T6w), which run side by side. A wrapper is removed by the slice that owns the file it is in |
| `State<'a, B: js::Js = Rows>`: the parameter has a default | 73 tests say `State::new(input)` and about 40 closures say `State<'_>`; with the default none of them changes |

**Found on the way, not changed.** `norm::jm8_int32_lsr` folds two
literals with `>>` on the count as given, which overflows in a debug build
for a negative count. The lowering does not produce one (the tests skip
that pair); it is a note for the T6h slice, whose rule it becomes.

#### T6l: the skeleton

Status: skeleton and acceptance tests committed; bodies are T6l's
(11.9). Files: `bir/lower/js_stmt.rs` (the trait `JsStmt: Js`, every
function with its cost), `bir/j/rows_stmt.rs` (`impl JsStmt for Rows`, 29
bodies `todo!("T6l")` and 4 of later slices, with a table in its header
that says what each body is), `bir/lower/js_stmt_tests.rs` (14 tests: 3
run, 8 are ignored as "T6l build" and 3 for the later slices). Compiled
for tests only until T6l's second commit. T6k was being
built while this was written: `rows.rs`, `js.rs` (no function added),
`js_tests.rs`, `prim_cmp.rs`, `prim_block.rs`, `unit.rs` and `State` are
untouched by it.

**What ran, and against what.** The prototype of T6k's 85 bodies was put
back locally, with a prototype of the 29 bodies of the statement half;
the 14 tests passed against them. Both prototypes were taken out before
the commit. With T6k's prototype present and the statement bodies out,
each of the 8 tests ignored for T6l fails with `not yet implemented: T6l`
and with nothing else: that is the check that an ignored test reaches no body
of another slice (in the committed tree, where T6k's bodies are out too,
they fail in T6k's `todo!` first, which is why the check needs the
prototype). A throw-away probe then did the rest of T6l on the
prototypes: `State<'a, B: JsStmt>` with every `impl` header, and
`assign.rs`, `loops.rs` and `try_.rs` converted whole. With it
`cargo test --lib bir::lower` gave 517 passed and 4 failed, the 4 being
the allocation pins at exactly T6k's numbers (86, 103, 86, 156): T6l
moves no pin. The probe is not committed.

The probe changed the order in which two kinds of node are made: the
block of a `try` is made when the `try` is built and no longer when its
child returns, and the body block of a `while` with a prelude is made
after its `true` condition. No test of the lowering changed its result.
Rows are "today's rows" up to that numbering.

**What the tests are.** The oracle form of T6k: two arenas, the interface
on one, today's calls on the other, equal dumps. Every constructor is
compared on six list shapes (empty, one statement, a `return`, a `break`,
two, three ending in a `throw`); `if_plain` and J-S3 on every pair of
them, J-S3 with 11 tests; J-S1 and both forms of J-M14 on the same 11
values, with the statements given compared one by one. Steps at 10,000
minus steps at 1,000 are nine times the step from 1,000 to 2,000, for a
wide block, a nest of loops, a list taken apart and made again, and the
effect statements of a comma. One test states that a block the lowering
builds from a slice of statements today (`Bir::new_node`, `plain::node`,
`plain::list`) is the row `block_of`, `explicit_block` and `function`
write for the list of the same statements, so that no constructor takes
a slice. Allocation is a relation: a list and its
block through the interface allocate exactly what today's two calls do,
and J-M14 through a warm operand stack allocates less than with a vector
taken empty.

**Changes to "T6: the interface" that the skeleton made**, each with its
reason:

| Change | Reason |
| --- | --- |
| There is no `stage_mark` and `stage`; `list(a, len, statements)` takes the statements as an iterator | The lowering has a staging stack (`StatementStack`) and keeps it (`StatementStack<B>`, T6x). A second one behind the interface moves every statement twice: 8 bytes more a statement on rows, 24 on the builder, on what becomes the final path (review decision 5). `list` is `Lists::push_iter` on rows, the call `take_list` makes today, and needs no vector of `Rows`: no allocation pin moves. Until T6x `take_list` stays as it is and a converted file gets its list with `B::list_from` |
| A constructor that has a body takes the list, not a block statement (`while_`, `for_range`, `for_of`, `try_`, `if_plain`, `if_`, `function`) | It is the builder's form (`Builder::while_` and `if_` take lists). The block is made inside, so the lowering never holds a block it has to take apart again |
| The statement block is `block_of`; `block` stays the block literal of `Js` | Two functions of one name on one type are ambiguous at every call |
| `assign(a, var, value)` is added | `bir::j::assign` writes the `=` with `Bir::new_node`; `bin_plain` writes it with `plain::node`, which sets the delay flag. A composition of `var`, `bin_plain` and `exp` would not be today's row |
| `declare` takes `Option<E>` | `declare_empty` (`exit.rs`) is the same statement without a value |
| `for_range` takes its bounds as `Range { init, end, direction }` | Eight parameters is over clippy's limit and the crate builds without `allow`. `Range<E>` is 16 bytes on rows |
| `try_(a, body, handler: Option<(VarId, L)>, finaliser: Option<L>)` | A handler always has its exception variable and a `try` without a handler has a finaliser (`Bir::check_shape`). `try_.rs` stores the lists in the order its children return; the function takes them by what they are |
| `effect` and `effect_if_impure` give their statements to a closure | J-M14 pushes to a vector. On rows the vector is the operand stack above its length on entry, cut back afterwards, so the rule gets a warm vector and `Rows` gets no second one |
| `explicit_block` is added | `Bir::explicit_block_from_list` (`cond.rs`, `untagged.rs`) is a different statement: it keeps its braces |
| `switch` is plain | No function of `bir/lower` calls J-S4 (`rg 'js4_normalize\|plain::statement' src/bir/lower` is empty); (c) said every statement constructor applies it |
| `rest` and `for_range_existing` are not in the trait | No function of `bir/lower` builds an `SRest` or an `SForRangeExisting` outside the tests of `globals.rs`; the replay (T6r) reads them and adds what it needs |
| `row_at` is `kind_at`; `stmt_has` and a flag reader by position are not in the trait | Rows has no `Row` to return. A statement of `Bir` has no strict flag today (`export::has_toplevel_effect` reads a compound statement until its first effect), so `stmt_has` cannot be O(1) on rows without a new flag: it is T6q's, with `export.rs` |
| `stmt_aux` is added | The declaration kind, the string bit of a switch and the explicit bit of a block are read by the lowering (`cond.rs`, `tail.rs`) and by the replay |
| `if_head` is not in the trait | It works on runs of the lowering's stack (`norm::simplify_if_head` over `IfLists`), which `out.rs` owns until T6x: see "T6m to T6x: what each slice adds" |
| `State<'a, B: JsStmt = Rows>`: T6l changes the bound | `State` uses both halves. Every `impl` header changes once more, mechanically |
| The plans keep `NodeId` and `ListId` (`loops::Plan`, `try_::Plan`) until T6x | They hold what `Out` holds. T6x converts them with `Out`: they are added to its row of the cut |

**Found on the way, for T6v.** A loop's label is a symbolic `StrId` that
gets its text after the loop is built (`label.rs`: `symbolic_label`,
`finish_labels`). `Builder::while_`, `break_` and `continue_` take the
label as `&str`. The interface takes the `StrId`; T6v's design says how
the builder prints a label whose text is not known when the statement is
built (the text is known when the unit is sealed).

**For T6v: a dotted global, and `Kind::Named` in `optional_duplicable`.**
A:69 `is_okay_to_duplicate` refuses a global whose name has a dot
(`Intl.DateTimeFormat` reads a member each time it is evaluated). On
rows such a reference is a `Var` whose variable has
`VarFlags::JS_GLOBAL`, and `ffi_args.rs::optional_duplicable` tests the
flag in its `Var` arm. The same function also accepts `Kind::Named`,
which no row has (the arm came from the prompt of T6p, which wrote
`Named` where the old code matched `JQualified`; the builder of T6p
added `Qualified` and kept `Named`). Nothing changes today. On the
builder `Js::var` of a global may write a row of kind `Named` (a name
printed as written), and the `Named` arm would then call a dotted
global duplicable. Decided for T6v, so that no test of the lowering
depends on which kind an implementation gives a reference:

- `var_of(a, r)` answers `Some(var)` for every row `Js::var` built,
  whatever its kind. A `Named` row that no variable stands behind (the
  builder writes none for the lowering today) answers `None`.
- A test of the lowering that asks "is this a reference" reads
  `var_of`, not `kind == Var`; what it then decides it reads from the
  variable's flags, which are the pools' and the same on both
  implementations. `optional_duplicable`, `duplicate_jsx_key` and
  `hold_external_receiver` are the three chain walks that match on
  `Kind::Var`: T6x's slice of `ffi_args.rs`, `jsx.rs` and `external.rs`
  rewrites each as `if let Some(var) = var_of(r)` before the match on
  the kind, and deletes the `Named` arm of `optional_duplicable`.
- T6v's oracle tests include a dotted global as an optional argument of
  an external: the two implementations must hold it in a variable
  alike.

#### T6m to T6x: what each slice adds

Status: a survey, not a probe. For each slice the non-test code of its
files was searched for every use of the arena, of `plain::`, `norm::`,
`bir::j::`, of the node flags, of the list pool and of the statement
stack, and the uses that the two traits do not cover were read. No file
of these slices was converted or compiled: only `prim_cmp.rs`,
`prim_block.rs` (T6k) and `assign.rs`, `loops.rs`, `try_.rs` (T6l) were.
What is listed is therefore what reading found; a conversion can find
more, and each slice's design turn starts with the probe that this turn
did not do.

**In code now** (statement side: signature and cost in `js_stmt.rs`, body
`todo!` with the slice's name in `rows_stmt.rs`, one test ignored for the
slice in `js_stmt_tests.rs`; each test ran against a prototype, and with
the bodies of T6k and T6l present each fails only with its own slice's
`todo!`):

| Function | Slice | Called from |
| --- | --- | --- |
| `locate_stmt(a, &mut S, LamLoc)` | T6m | `prim.rs::primitive_statement` (the statement of a `debugger` and of a raise). T6o calls it too (`location.rs::locate_switch_run`), with `stmt_located` |
| `take_value(a, S) -> E` | T6n | `cond.rs`: `effect_output` (a lone expression statement becomes the value), `fold_return_tail` |
| `unblock(a, S, sink)` | T6n | `cond.rs::unnest`; also `untagged.rs::emit_cached_action` (T6o) and `tail.rs` (T6w), which run beside T6n: the slice that lands first builds the body |
| `stmt_located(a, &S) -> bool` | T6o | `location.rs::locate_switch_run` |

**Expression side, to add after T6k has merged** (`rows.rs` was the
builder's in this turn). Each is one function of `Js` with its body on
`Rows` and one test in `js_tests.rs`:

| Function | Slice | Cost | Body on rows | Test that pins it |
| --- | --- | --- | --- | --- |
| `str_of(a, r) -> Option<StrId>`: the interned text of a string literal | T6m (`Pmakedict`: the key of a pair becomes a `PropertyKey::Literal`) | O(1); no hashing (`text` would have to be interned again) | the `text` of `View::JStr`, `None` otherwise | of `str(a, name)` it is `name`; `None` for a template, a number, a variable |
| `push_list(a, ListId)`: the nodes of a pool list built by a caller that is not converted, pushed as operands in order. Transition, deleted by T6x | T6p (`external.rs::compile_js_call` and `compile_js_object_create` get their operands as a `ListId` from `prim.rs`, T6m; the two run side by side) | one step per node | `Rows::operands` extended by `Lists::get(list)` | a call built from `mark`, `push_list`, `call` dumps as the call built with the slice |
| `owner(a, id) -> Option<u32>`, `operand_index(a, id) -> u32`, `kind_of(a, id) -> Kind` | T6q | O(1) | `Bir::parents`; the position among the parent's operands; `rows::kind_of` | "T6: the interface" (f) |
| `equal(a, r1, r2) -> bool` | T6q (`export.rs::same_reusable_value`) | that of `bir/j/equal.rs` | `plain::equal` | two copies are equal, a copy and a different literal are not; steps at 10,000 nodes are ten times those at 1,000 |

**Found and not added, each with what decides it:**

| What | Slice | Why it is not in code |
| --- | --- | --- |
| A statement copy that freshens its binders and labels: `copy_stmt(a, &S, fresh: &mut Vec<(VarId, VarId)>) -> S` (`untagged.rs::copy_dispatch_output` copies a cached run with `Bir::copy_subtree_with_scratch`) | T6o | Its body on rows needs the copy scratch and the label vector as fields of `Rows`. "T6: the interface" (a) said the lowering copies expressions only; it copies statements here. One step per node copied |
| J-S3 on runs: `if_head` (`norm::simplify_if_head` over `IfLists`, implemented by `StatementStack` in `cond.rs`) | T6n or T6x | The function works on runs of the lowering's stack. Until `StatementStack<B>` exists (T6x) it cannot be given handles. Recommended: `cond.rs::if_in_place` and the `impl IfLists` stay on rows through T6n (its end-state `rg` excludes `simplify_if_head` and `IfLists`) and are converted by T6x with the stack |
| Taking an `if` apart to build another with one of its blocks (`cond.rs::merge_tail_guard`: the then-block of a guard is reused as it is) | T6n | With lists in the constructors the block must become a list again, which costs one step per statement of it where today's move is O(1). Either `take_if(a, S) -> (E, L, L)` with that cost and a step test that the guard merge stays linear, or an `if` constructor over two block statements. T6n's design turn decides with the probe |
| `stmt_has(a, &S, STRICT)` | T6q | A statement of `Bir` has no strict flag: `export::has_toplevel_effect` reads a compound statement until its first effect. On rows the function is that read (not O(1)); on the builder it is the row's flag. T6q's design states the cost per implementation |
| The operands a primitive is given: `values: &mut Vec<NodeId>` (`prim.rs`, filled by `args.rs`) and the scratch vectors of `object_scratch` | T6m, T6x | Storage, not interface. A handle is not `Copy`, so `values[0]` becomes a move. Recommended: a slice converts the scratch that is private to its files (a `Vec<B::E>`, emptied with `drain` or `pop`), and storage that crosses files (`Out`, the evaluation of `args.rs`, `values`) waits for T6x. T6x is then more than the 600 lines of the cut; its design turn re-cuts it after counting the uses |

**What reading settled without an addition:**

- T6m. `Pmakedict` and `PdictSpread` take a literal apart with
  `unpack_rev`; the values kept go to the lowering's scratch and are
  pushed when the object is built, because the operand stack cannot be
  read and written at once. `Psome`, `PisNotNone`, `PvalFromOption` are
  `kind`, `aux` and `keep_operand`; the leaf copies of `PnullToOpt` are
  `copy_leaf`; the location of a primitive's value is `located` and
  `locate`; the comment of `PcreateExtension` is `comment`. A function
  whose body is one statement (`import.rs`, `call.rs`, `ffi_args.rs`) is
  `list` of one and `function` (tested: the same row).
- T6o. The actions of a switch are written into a reserved pool list out
  of order (`Lists::set`, `truncate`); they become `list` over the
  lowering's scratch of action statements, in clause order. A cached run
  that is staged is `unblock`.
- T6p. The values of a JSX element are in hand before the element is
  built (the callee is stored last today, at index 0): they are pushed in
  the order callee, tag, spread, properties, children, key.
  `bir::j::member` is `dot`. `Bir::copy_subtree(arg, &[])` is `copy`.
- T6w. `tail.rs` restages the statements of a body with `unblock` and
  builds its loop with `while_` over the list. The placeholder of a
  recursive member (`rec.rs`) is a statement held outside the stack: a
  `NodeId` until T6x, as the plans are.
- T6x. `list` has its first caller in the lowering here
  (`StatementStack::take_list`); T6l builds it and its test.

**Decision 6 of the review: can `export.rs` get the top-level row of a
reference without the owner column?** No. The proposal was the site
table and the row that is open when a statement is staged. It fails
because a reference is not built for the statement that is open: it is
built into a value (`Out::value`), and a value is put into a statement
by its consumer, after the statements of the operands lowered behind it
have been staged. The case: at the top level, `let a = f(x, e)` where `e`
lowers to statements (a `try`, a `switch`, a loop). The reference to `x`
is built first; then the statements of `e` are staged and become rows of
their own; then `let a = f(x, tmp)` is staged. The site of `x` was
recorded before the rows of `e` and lies in the row after them. Neither
"the row open when the reference was built" (the row before `e`'s) nor
"the sites recorded since the last row was staged" (which gives `x` to
the first row of `e`) is its row. Read from `Out`, `args.rs` and
`export.rs`, not run.

What would work without a column is a list of sites carried by every
expression handle and joined by every constructor (head and tail, 8
bytes more in a 24-byte handle, two stores per operand), stamped with
the row when a top-level statement is staged. That is more per node than
the column (one store per operand, 4 bytes a node) and it widens the
handle, so the owner column stays. `mentions` also needs two things the
site table alone does not have: whether a function literal lies between
the reference and its row, and whether the reference is the callee of
its parent; both are climbs of the same column.

#### T6m to T6q: the probes, and slices built side by side

Six slices convert the remaining lowering files at the same time. This
section records what a probe of each found and the rules that keep six
pull requests off one another's lines. A probe is a throw-away
conversion of the slice's files in a copy of the tree, compiled and run
against the bodies of the interface (`--lib bir::lower` and `--lib
bir::j`), then taken out again; none of it is in the tree.

**What a probe is and is not.** A script rewrote every `plain::`,
`norm::`, `pure_expression`, `release` and `bir::j::` call of a file
into the interface call, wrapping each handle at the call
(`B::from_node`, `B::node`); the sites it could not rewrite were
converted by hand. The probe therefore proves that every J operation of
the file has a function in the interface with the same rows (the tests
of the lowering compare rows) and that the allocation pins hold. It does
not prove handle ownership across a function: locals stay `NodeId` in
the probe except at the hand-converted sites.

**Rules for the six slices** (they replace two sentences of the common
block of phase C, and are part of every prompt below):

1. *No signature changes.* Every function of the lowering keeps its
   parameters and its result as they are: a J node crosses a function
   boundary as a `NodeId` until T6x. Inside a body a handle is made at
   the first interface call (`B::from_node(x)`, or `B::at(x)` to read)
   and turned back (`B::node`, `B::stmt_node`) only where it is stored,
   returned or passed to a function of the lowering. Reason: 33
   functions with a `NodeId` in their signature are called from a file
   of another slice (counted by a script over the non-test code) (`if_statement` from five files, `drop_pure_effect`
   from seven, `primitive_runtime` from five); a signature change is an
   edit in another builder's file. The common block's "the functions of
   the file take and return `B::E`" held for T6k and T6l, whose callers
   were not being converted.
2. *No shared file.* No slice edits `js.rs`, `js_stmt.rs`, `rows.rs`,
   `rows_stmt.rs`, `mod.rs`, `out.rs`, `unit.rs` or a test file of the
   interface. Every function a probe found missing is in the trait with
   its body on rows and its test, written by the design turn; where a
   body could not be written it is a `todo!` named for its slice and
   that slice alone edits that one function.
3. *No bound changes.* Every impl header already reads
   `B: super::js_stmt::JsStmt` (T6l). None of the six slices needs
   another bound, field or module line.
4. *Storage stays.* `Out::value`, `values: &mut Vec<NodeId>`, the plans,
   `argument_values`, `object_scratch` and every other field of `State`
   keep their types (T6x).

**One fix a probe forced.** With `prim.rs` converted, a wide call pushes
its operands on the operand stack, which was reserved for 64: the
allocation count of a unit grew with its width (90 against 94, 100
against 104). `State::with` now reserves the stack for the count of
source operands, as the argument scratch is; still one allocation, the
pins stay 86, 103, 86, 156.

| Slice | Files | Probe | What it lacked |
| --- | --- | --- | --- |
| T6m | `prim.rs`, `konst.rs`, `record.rs`, `import.rs` | 546 passed (`bir::lower`), 58 (`bir::j`); 589 lines changed | Nothing in the trait (`str_of` and `locate_stmt` were added before it). The operand-stack reserve above |
| T6n | `cond.rs`, `expr.rs` | 546 and 58, on top of T6m's; 279 lines changed | `is_empty_block`, `branch_last_kind`, `release_stmt`, `if_blocks`, `take_if`, `function_of_block` |
| T6p | `args.rs`, `call.rs`, `ffi_args.rs`, `external.rs`, `jsx.rs` | 550 and 58, on top of T6m's and T6n's; 703 lines changed | `take_operands`, `refill`; `new_` wrote the wrong `aux` |
| T6w | `tail.rs`, `rec.rs`, `exit.rs`, `label.rs` | 551 and 58, alone on trunk (no other probe in place); 139 lines changed | Nothing. `label.rs` builds no J node |
| T6o | `switch.rs`, `variant.rs`, `untagged.rs`, `location.rs` | 550 and 58 with T6w's probe in place, the one failure being the size pin of `Rows` that this turn moves; 348 lines changed | `copy_stmt`, `copy_fresh`, and their storage in `Rows` |
| T6q | `export.rs` | 557 and 58, alone on trunk after the five conversions, the one failure being the size pin of `Rows` that this turn moves; 315 lines changed | `equal`, `id_bound`, `declared`, `block_ids`, `effect_free` |

**What the functions of the survey became.** "T6m to T6x: what each
slice adds" listed six expression-side functions to add once T6k had
merged. In code now, each with its body on rows and a test: `str_of`,
`push_list`, `owner`, `kind_of`, and `is_callee(a, id) -> bool` in place
of `operand_index` (the one reader, `export.rs`, asks only whether the
reference is the callee of its owner; that is one comparison where an
index is a scan of the owner's operands). `equal` is not added:
`export.rs::same_reusable_value` compares two chains of member reads
over a variable or a module by their names, which `var_of`,
`qualified_of`, `member_of`, `aux` and `operand` already give; it is not
`plain::equal` and needs no function. The four statement functions that
were `todo!` for a later slice (`locate_stmt`, `take_value`, `unblock`,
`stmt_located`) have their bodies: each is a plain call, and a body left
for "the slice that lands first" is an edit two builders would make.

**T6p: a node over other operands.** `args.rs` (A:116 `evaluate_now`)
holds each operand of a literal in a variable and builds the literal
again with its `aux`, its information, its location and its comment;
`sequence_arguments` does the same to the object of a member callee and
`ffi_args.rs::hold_external_arg` to the payload of an optional. Today
the node stays as a shell without children while its operands are
lowered. With handles that is two functions: `take_operands(a, &mut E)
-> u32` moves the operands to the operand stack and leaves the node,
and `refill(a, E, mark) -> E` builds the node of the same kind over the
operands pushed since the mark and releases the shell. It is defined
for `Optional`, `Array`, `BlockLit`, `Object` and `Dot`, the five kinds
the three callers have; it is plain, and `args.rs` asserts strictness
with `assume_strict` as `bir::j::pure_expression` did. The alternative,
readers for a node's location and comment so that the caller carries
them, puts cold data in the lowering's work stack (24 bytes a frame
where it has 8).

**T6p: `new_`.** The body T6k built wrote `aux` 0 on a `JNew`, which in
`bir/node.rs` means "no argument list"; `Bir::call_from_list(callee,
args, None)`, the only producer in the lowering, writes 1. The function
had no caller, so nothing was wrong in any output, and its test compared
with `plain::node(.., 0)`, which was the same mistake on both sides. The
probe showed it as a disagreement of the naming replay in two tests of
`external.rs`. The body writes 1 and the test compares with
`call_from_list`. Lesson for the remaining probes: an oracle test of a
function without a caller proves the two sides alike, not that either is
what the lowering writes; the probe is the first real check.

**T6p: operand lists in the pool.** `external.rs`, `ffi_args.rs` and
`jsx.rs` receive and return the operands of a call as a `ListId` of the
arena's list pool (`compile_js_call(.., args: ListId)` is called from
`prim.rs`, T6m) and assemble lists in place (`Lists::set`, `truncate`,
`slice`). That is storage, and its type is in signatures: it stays
until T6x. What changes is the constructor: `call_from_list`,
`object_from_list` and `jsx_from_list` become `mark`, `push_list(list)`
and `call`, `new_`, `object`, `jsx`. Cost: the operands of an external
call are copied once more into the node's own list (one move per
operand, counted by the constructor's step per operand). T6x removes the
copy with the lists. The probe held the allocation tests of the five
files with this, among them 10,000 dispatch cases without an allocation.

**T6p: what stays on rows.** `jsx.rs::printed_form` and `jsx_tag` are
free functions over `&Bir` that `names.rs` (T6r) calls on the finished
node; they are not the lowering building JavaScript and are converted
with `names.rs`.

**T6w and T6o: the actions of a switch stay a pool list.** `exit.rs`,
`switch.rs` and `untagged.rs` reserve a list of the arena's pool for
the actions of a switch, write each action into its slot
(`Lists::set`) and hand the list to the switch. The survey proposed to
collect the actions in a scratch vector of the lowering and build the
list with `list`. The probe of T6o did that with `State::scratch`: the
allocation count of the untagged unit went from 156 to 164 at width
1,000 and 168 at 10,000, because the vector grows with the widest
switch where the pool is reserved once from the source's counts.
Decided: the reserved list, `set` and `truncate` stay (storage, as the
operand lists of T6p) and the switch takes it with `B::list_from`. The
pins hold with it. T6x replaces the pool list when `StatementStack<B>`
gives a list its statements. (`ffi_args.rs::external_dispatch`, T6p,
collects in `State::scratch` as its prompt says: its dispatch is built
inside a function literal and its cases are few; its allocation test
held in the probe.)

**T6o: the copy (decision 7 of the review of the T6l skeleton).**
`untagged.rs` copies a statement (an action that the dispatch emits
more than once, `copy_dispatch_output`) and an expression (a scrutinee
that is not a variable), and gives each binder the copy freshened the
identifier of its source. Two functions, one body on rows:
`copy_stmt(a, &S, fresh) -> S` in `JsStmt` and `copy_fresh(a, Ref,
fresh) -> E` in `Js`; each appends `(fresh, source)` per binder to the
caller's vector, in the order the variables were made. `Js::copy` stays
for the copies of T6p, whose operands have no binder. One step per node
copied, read from the copy's own traversal (`CopyScratch::copied`): the
growth of the node vector, which `Js::copy` counts, is not the number
copied when freed slots are reused.

`Rows` gains two fields and is 392 bytes (it was 32):

| Field | Bytes | Why it is in `Rows` |
| --- | --- | --- |
| `copy: CopyScratch` | 336 | The traversal order and the five renaming tables of `Bir::copy_subtree_with_scratch`. Kept between copies so that a copy in a warm unit allocates nothing; `untagged::Storage::copy_scratch` holds it today and T6o deletes that field |
| `labels: Vec<(u32, u32)>` | 24 | The copy writes each static label it freshened there. The lowering reads none (a label is renamed inside the copy), so the vector is cleared after every copy; it is a field so that a copy with labels allocates nothing in a warm unit. `untagged::Storage::copied_labels` today, deleted by T6o |

The vector of fresh binders stays the lowering's
(`untagged::Storage::copied_vars`): the lowering reads it. `Rows` is
one value per unit and is never passed down a walk, so the 16-byte rule
does not apply; `State` holds it inline. The test
`a_copy_costs_one_step_per_node_and_allocates_nothing_in_a_warm_unit`
copies a nest of 1,000, 2,000 and 10,000 statements: no allocation, the
capacities of the storage unchanged, as many steps as releasing the copy
counts, and exactly linear. The allocation test of `untagged.rs` reads
the storage through two test-only functions of `Rows`
(`reserve_copy`, `copy_capacities`).

**Corrections owed by the reviews of the conversion slices** (T6m to
T6p, T6w, T6o; each has a test that fails without it):

1. `Js::copy` on rows counted the growth of the node vector, which is
   zero when the copy takes slots a release freed. It is now the body of
   `copy_fresh` with a vector of its own for the binders, which it
   drops: one step per node the copy's traversal visited. It uses the
   copy storage of `Rows`, which changes a warm unit for the better:
   `Bir::copy_subtree` made its traversal vectors and its renaming
   tables anew for every copy (the node table sized by the arena), and
   a copy now allocates nothing once the storage has its capacity
   (`a_copy_into_freed_slots_costs_one_step_per_node`: 1,000, 2,000 and
   10,000 calls copied after a release of as many; the node vector does
   not grow, the steps are the nodes, no allocation).
2. `Rows::object` asserts one operand per key of its information and
   `Rows::jsx` the callee, the tag and what its header counts; the two
   assertions had gone with `object_from_list` and `jsx_from_list`.
3. A chain of merged guards is linear:
   `a_chain_of_merged_guards_moves_each_statement_once` (`tail.rs`)
   nests 1,000, 2,000 and 10,000 conditionals through their continuing
   branch, each with a guard that ends in a throw followed by a return,
   checks on two levels that both merged, and reads the interface's
   steps, the statements scanned and the body statements moved as a
   linear relation. No code changed. (A guard that ends in a `return`
   of a value does not reach the merge: J-S3 folds it into a
   conditional expression first.)
4. `unblock`, `effect` and `effect_if_impure` passed their statements
   through the operand stack of `Rows`, reserved by the unit's source
   operands. A statement comes from a source node that need not own an
   operand: a loop body of 10,000 `let` declarations in a unit with four
   source operands grew the stack from 64 to 10,002
   (`a_block_wider_than_the_operand_stack_is_unblocked_without_growing_it`
   failed so). Of the three ways out, the reserve by source nodes costs
   four bytes a node in every unit for a buffer five callers use, and a
   larger constant only moves the width that grows it. Chosen: nothing
   is buffered. `unblock` reads each statement by its index, takes it
   out and gives it on, as the lowering did before the conversion; the
   J-M14 rules take a sink (`norm::jm14_effect_expression`,
   `jm14_s_exp`, `jm14_s_if_empty`; the `push` forms call them) and
   `effect` gives each statement on as the rule makes it. The operand
   stack holds operands of list constructors only, and the tests assert
   that a `Rows` that reserved nothing keeps capacity 0 through both.
   This also takes back the one more move a statement that the reviews
   of T6n and T6o noted. "T6l: the skeleton" said the rule pushes to the
   operand stack as scratch: withdrawn.

**T6q: the export coercion.** `export.rs` does not build JavaScript and
hold it: it reads the finished top-level run into tables indexed by row
and by node id (`Tables::rows`, `row_of`, `later`, `inserted`), climbs
from a reference to its row, and then moves, removes and adds
declarations. The probe converted the whole file. What it decided:

1. *The files.* T6q is `export.rs` alone. `close.rs` (`decide(bir,
   list)`) and `scope.rs` (`Scope`, `return_sites(bir, ..)`) are free
   functions and tables over `&mut Bir`; they have no `State<B>` and no
   `self.js`, and their callers are `out.rs` and `globals.rs`. Giving
   them the interface is a new parameter, which is their callers'
   signature change: `close.rs` goes with `out.rs` (T6x), `scope.rs`
   with `names.rs` and `globals.rs` (T6r), as `jsx::printed_form` does.
2. *A row's statement is an id.* `Row::stmt`, the `NodeId` of an
   initialiser (`Init`), of a replacement, of a site and of every entry
   of the tables are storage until T6x, as `Out::value` and the operand
   lists are. A read makes a handle or a reference from the id
   (`B::stmt_from_node`, `B::at`) and reads through the interface.
3. *The climbs* are the three id readers that were added for this file
   without a caller, and the probe confirms exactly these: `owner`
   (`declared`, `row_of`, `mentions`), `kind_of` (`is_literal`,
   `classify`, `declared`, `row_of`, `copy_replacement`, `define`) and
   `is_callee` (`mentions`: the test is the one `is_callee` makes, a
   call, a flat call or a `new` whose callee the site is, or a tagged
   template whose tag it is). `id_bound(a) -> u32` is new: `row_of`
   sizes its table by the number of ids.
4. *`equal`.* `equivalent_later` compares an initialiser with a literal
   through `bir::j::equal::equal`. `Js::equal(a, left, right, steps)` is
   that function: partial as the rules are, one step per pair it
   inspects, bounded by the smaller tree. It takes the step counter as
   `bir/j/equal.rs` does, because a reader counts nothing in
   `Js::steps`. The test compares its answers and its counts with the
   arena's function and reads a linear relation at 1,000, 2,000 and
   10,000 calls. (`same_reusable_value` stays the lowering's own
   comparison of member chains by name.)
5. *The strictness of a statement* (decisions 4 and 9 of the review of
   the T6l skeleton). A new function of `JsStmt`:
   `effect_free(a, &S) -> bool`, S:1053 `js_statement_no_side_effects`.
   On rows it is the read `has_toplevel_effect` makes today, moved: a
   work stack of the children of a compound statement, the `STRICT`
   flag of each expression, `false` at a throw, a `debugger`, a jump, a
   declaration and a loop over an iterable; one step per node read, and
   it stops at the first effect. On the builder it is the statement
   row's `STRICT` flag, O(1) (the one flag "T6: the interface" (b)
   gave a statement). The other choice, a reader of a statement's parts
   so that the lowering keeps the walk, makes the builder walk what it
   already knows. The work stack is a field of `Rows` (24 bytes;
   `size_of::<Rows>()` is 416): the walk is `&mut self`, and the
   operand stack is not lent to a walk ("Corrections owed by the
   reviews", 4: it must not grow with a statement's width). `has_toplevel_effect` keeps its
   test of a declaration row (a value that is not strictly pure; a
   rest declaration always), because a declaration inside a compound
   statement counts as an effect and a declaration row does not.
6. *`SRest`* is `Kind::Rest`: `stmt_kind` answers it, `declared(a, &S)`
   gives the variable of a `Declare` and of a `Rest`, and a rest row
   keeps its own id as its initialiser, as today (nothing reads into
   it; `equivalent_later` excludes it by that id).
7. *A top-level block* gives its statements' ids with
   `block_ids(a, &S, sink)`: the statements stay in the block.
8. *Three edits stay transition calls until T6x*, and the end-state
   search of T6q names their eight lines: the replacement of a
   reference in place (`Bir::replace` in `substitute_after`), a row
   taken out of its block and released (`release_row`), and the final
   list (`coerced_list`: the statements of a dissolved block detached,
   the blocks released, the list pushed). Each changes a structure that
   was finished: on the builder these are edits of sealed lists (E1 to
   E3 of "T6: the order of the flip"), whose functions enter the trait
   with their first slice (T4g) and with `StatementStack<B>` (T6x). A
   rows-only shim for each now would be a vocabulary nobody else calls.
9. *What goes dead.* With `export.rs` converted, `bir::j::member` and
   `Bir::copy_leaf` have no production caller (`cargo check` named
   both in the probe). By the common rule the builder deletes
   `Bir::copy_leaf`, which nothing else calls, and puts `#[cfg(test)]`
   on `bir::j::member`, which tests of `bir/j/mod.rs` and of `args.rs`
   still call.
   `copy_replacement` copies a leaf with `Js::copy_leaf` and
   `Js::copy_cold`, where `Bir::copy_leaf` copied the node's words and
   flags: the flags are computed again by the plain constructor, and
   a module member is asserted strict as before.

`has_toplevel_effect`'s steps move from `Tables::steps` to `Js::steps`
(one stays, for the row). The tests of `export.rs` bound
`Tables::steps` from above, so none changes.

**T6n: the guard merge (decision 6 of the review of the T6l skeleton).**
`cond.rs::merge_tail_guard` takes a guard `if (c) { ..; jump }` whose
else is empty, and builds `{ if (c) { ..; jump } else { the rest } }`,
reusing the guard's then-block as it is. Decided: an `if` constructor
over two block statements, `if_blocks(a, test, yes: S, no: S)`, and
`take_if(a, S) -> (E, S, Option<S>)` that gives the blocks back as
statements. Both are O(1) and neither reads a statement of a block. The
other choice, `take_if` giving lists, costs one step per statement of
the then-block each time a guard is merged, and a chain of guards merges
the same statements again: quadratic in the depth of the chain. A block
statement is already a handle the lowering holds (`explicit_block`,
`block_of`), so no new kind of value appears. The guard's two tests
(its else has no statement; its then ends in a jump) are one reader,
`branch_last_kind(a, &S, otherwise) -> Option<Kind>`, O(1).

**T6n: what stays on rows (decision 5).** `cond.rs::if_in_place` calls
`norm::simplify_if_head` over `impl norm::IfLists for StatementStack`.
Both work on runs of the lowering's stack and cannot be given handles
before `StatementStack<B>` exists (T6x). They stay, and T6n's end-state
search excludes exactly those two names.

**T6n: `function_of_block`.** `expr.rs` builds a function literal over a
block that `tail.rs::loop_function_body` (T6w) may have rewritten; that
function takes and returns a block statement and is another builder's.
`function_of_block(a, header, body: S)` is a transition function: T6x
deletes it when the body crosses as a list.

#### T6x: the cut

Status: counted; T6x-a is probed and cut again in "T6x-a: the statement
stack, after the probe" below, which also has the counts of trunk after
T6q and after T6x-a. A script
(`scripts/count_lowering_ids.py`, run from `compiler-rust`) read the non-test code of
`src/bir/lower` on trunk after T6m to T6p, T6w and T6o (T6q's
`export.rs` is not converted yet; its numbers below are its raw sites).
It cannot tell the `NodeId` of a source node from that of a J node in a
signature or a field, so "touching J" is read from the body (a
transition call or a call of `self.js`), and the field table is
classified by hand below. The line figures of the slices are estimates
from these counts; each slice's design turn starts with its probe.

**What T6x has to change.**

| File | Lines | fns with NodeId/ListId in signature | of these, touching J (a transition call or self.js in the body) | transition calls | from_node | node | at | stmt_from_node | stmt_node | list_from | list_id | function_of_block | push_list | raw J sites left |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `args.rs` | 216 | 6 | 5 | 22 | 7 | 7 | 5 | 1 | 2 | 0 | 0 | 0 | 0 | 0 |
| `assign.rs` | 32 | 0 | 0 | 3 | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `call.rs` | 453 | 5 | 2 | 10 | 4 | 5 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `close.rs` | 82 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 4 |
| `cond.rs` | 998 | 31 | 21 | 96 | 29 | 16 | 4 | 17 | 23 | 7 | 0 | 0 | 0 | 3 |
| `exit.rs` | 596 | 7 | 1 | 14 | 0 | 4 | 0 | 1 | 7 | 2 | 0 | 0 | 0 | 0 |
| `export.rs` | 1757 | 19 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 141 |
| `expr.rs` | 324 | 3 | 2 | 16 | 6 | 3 | 2 | 1 | 3 | 1 | 0 | 1 | 0 | 0 |
| `external.rs` | 476 | 8 | 6 | 40 | 16 | 17 | 3 | 0 | 4 | 0 | 0 | 0 | 4 | 0 |
| `ffi_args.rs` | 644 | 14 | 13 | 64 | 22 | 23 | 17 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| `globals.rs` | 273 | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 10 |
| `import.rs` | 267 | 5 | 4 | 8 | 3 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `jsx.rs` | 295 | 6 | 4 | 19 | 5 | 7 | 7 | 0 | 0 | 0 | 0 | 0 | 1 | 6 |
| `konst.rs` | 307 | 4 | 4 | 15 | 8 | 6 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `label.rs` | 471 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `location.rs` | 143 | 3 | 1 | 2 | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| `loops.rs` | 196 | 3 | 1 | 17 | 2 | 3 | 0 | 0 | 5 | 7 | 0 | 0 | 0 | 0 |
| `mod.rs` | 1209 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 78 |
| `names.rs` | 1270 | 12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 53 |
| `out.rs` | 548 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| `prim.rs` | 744 | 9 | 7 | 139 | 123 | 5 | 7 | 1 | 3 | 0 | 0 | 0 | 0 | 0 |
| `prim_block.rs` | 206 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `prim_cmp.rs` | 284 | 1 | 1 | 7 | 2 | 4 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `rec.rs` | 210 | 5 | 2 | 11 | 3 | 4 | 0 | 0 | 3 | 1 | 0 | 0 | 0 | 0 |
| `record.rs` | 181 | 4 | 2 | 7 | 4 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `scope.rs` | 246 | 3 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 3 |
| `switch.rs` | 1115 | 11 | 1 | 23 | 3 | 3 | 0 | 6 | 9 | 2 | 0 | 0 | 0 | 0 |
| `tail.rs` | 116 | 4 | 2 | 11 | 3 | 0 | 1 | 1 | 5 | 1 | 0 | 0 | 0 | 0 |
| `try_.rs` | 138 | 3 | 0 | 5 | 0 | 2 | 0 | 0 | 1 | 2 | 0 | 0 | 0 | 0 |
| `unit.rs` | 103 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `untagged.rs` | 1137 | 10 | 7 | 39 | 12 | 8 | 2 | 3 | 9 | 5 | 0 | 0 | 0 | 0 |
| `variant.rs` | 505 | 6 | 5 | 22 | 7 | 9 | 2 | 1 | 3 | 0 | 0 | 0 | 0 | 0 |
| total | 15542 | 217 | 92 | 590 | 260 | 135 | 53 | 34 | 80 | 28 | 0 | 1 | 5 | 299 |

Of the 217 functions with a `NodeId` or a `ListId` in their signature,
92 touch J. The 590 transition calls are what the conversion slices
left where a handle meets storage or a signature: 260 `from_node` (123
in `prim.rs`, where every operand is read from `values: &mut
Vec<NodeId>`), 135 `node`, 53 `at`, 34 `stmt_from_node`, 80 `stmt_node`,
28 `list_from`, no `list_id`; `function_of_block` once (`expr.rs`) and
`push_list` five times (`external.rs` 4, `jsx.rs` 1). The raw J sites
left are `export.rs` (T6q), `names.rs`, `globals.rs` and `scope.rs`
(T6r), `mod.rs` (78: the probe and the realisation of `State`),
`close.rs`, `jsx.rs` (`printed_form`, `jsx_tag`), `cond.rs` (3:
`IfLists` and `simplify_if_head`) and `out.rs`.

The J-touching functions that are called from another file (a
signature change edits every file in the row):

| Function (file) | Called from other files |
| --- | --- |
| `sequence_arguments` (`args.rs`) | `call.rs` 1, `prim.rs` 1 |
| `call_node` (`call.rs`) | `ffi_args.rs` 1 |
| `place` (`cond.rs`) | `switch.rs` 1, `untagged.rs` 2, `variant.rs` 1 |
| `single_assignment` (`cond.rs`) | `switch.rs` 1 |
| `if_statement` (`cond.rs`) | `exit.rs` 1, `loops.rs` 1, `switch.rs` 1, `untagged.rs` 1, `variant.rs` 1 |
| `unnest` (`cond.rs`) | `exit.rs` 1, `switch.rs` 1, `untagged.rs` 4, `variant.rs` 1 |
| `merge_assignments` (`cond.rs`) | `switch.rs` 1 |
| `assignment_statement` (`cond.rs`) | `switch.rs` 1 |
| `realize_conditional` (`cond.rs`) | `mod.rs` 1 |
| `catch` (`exit.rs`) | `mod.rs` 1 |
| `drop_pure_effect` (`expr.rs`) | `cond.rs` 3, `exit.rs` 1, `loops.rs` 1, `mod.rs` 1, `rec.rs` 2, `switch.rs` 1, `try_.rs` 1, `unit.rs` 1, `untagged.rs` 1 |
| `compile_js_object_create` (`external.rs`) | `prim.rs` 1 |
| `compile_js_call` (`external.rs`) | `prim.rs` 1 |
| `optional_duplicable` (`ffi_args.rs`) | `external.rs` 1 |
| `compile_external_arg_const` (`ffi_args.rs`) | `external.rs` 1 |
| `assemble_external_args_no_splice` (`ffi_args.rs`) | `external.rs` 3 |
| `external_arg_effect` (`ffi_args.rs`) | `external.rs` 1 |
| `add_external_effect` (`ffi_args.rs`) | `external.rs` 12 |
| `static_member` (`import.rs`) | `external.rs` 6, `jsx.rs` 2, `prim.rs` 2 |
| `compile_import` (`import.rs`) | `prim.rs` 1 |
| `compile_jsx` (`jsx.rs`) | `prim.rs` 1 |
| `number` (`konst.rs`) | `label.rs` 1, `prim.rs` 2, `untagged.rs` 1, `variant.rs` 4 |
| `string` (`konst.rs`) | `ffi_args.rs` 3, `prim.rs` 2, `untagged.rs` 1, `variant.rs` 2 |
| `constant` (`konst.rs`) | `loops.rs` 1, `mod.rs` 1, `switch.rs` 2 |
| `locate_switch_run` (`location.rs`) | `switch.rs` 1, `untagged.rs` 1 |
| `primitive_runtime` (`prim.rs`) | `external.rs` 1, `ffi_args.rs` 3, `jsx.rs` 2, `prim_cmp.rs` 2, `rec.rs` 1 |
| `flat_make_field` (`prim_block.rs`) | `mod.rs` 1 |
| `primitive_bool` (`prim_cmp.rs`) | `prim.rs` 2 |
| `duplicate_record` (`record.rs`) | `prim.rs` 1 |
| `record_rest` (`record.rs`) | `prim.rs` 1 |
| `plan_switch` (`switch.rs`) | `variant.rs` 1 |
| `finish_self_call` (`tail.rs`) | `call.rs` 1 |
| `loop_function_body` (`tail.rs`) | `expr.rs` 1 |
| `untagged_switch` (`untagged.rs`) | `mod.rs` 1 |
| `named_variant` (`variant.rs`) | `mod.rs` 1 |
| `switch_key_expression` (`variant.rs`) | `switch.rs` 1 |

Where an output and a statement are stored and read:

| File | `Out {` built | `.value` of an output read or written | `statements.push`/`fill`/`place` | `impl norm::IfLists` / `simplify_if_head` |
| --- | --- | --- | --- | --- |
| `args.rs` | 0 | 1 | 3 | 0 |
| `assign.rs` | 0 | 2 | 1 | 0 |
| `call.rs` | 1 | 0 | 0 | 0 |
| `close.rs` | 0 | 0 | 0 | 1 |
| `cond.rs` | 3 | 5 | 23 | 2 |
| `exit.rs` | 6 | 2 | 6 | 0 |
| `export.rs` | 0 | 0 | 1 | 0 |
| `expr.rs` | 0 | 12 | 2 | 0 |
| `external.rs` | 1 | 2 | 4 | 0 |
| `ffi_args.rs` | 0 | 5 | 1 | 0 |
| `loops.rs` | 2 | 2 | 6 | 0 |
| `mod.rs` | 6 | 5 | 4 | 0 |
| `out.rs` | 4 | 1 | 0 | 0 |
| `prim.rs` | 2 | 0 | 1 | 0 |
| `rec.rs` | 2 | 4 | 3 | 0 |
| `record.rs` | 0 | 1 | 0 | 0 |
| `switch.rs` | 3 | 2 | 7 | 0 |
| `tail.rs` | 1 | 0 | 4 | 0 |
| `try_.rs` | 2 | 1 | 1 | 0 |
| `unit.rs` | 0 | 4 | 0 | 0 |
| `untagged.rs` | 2 | 2 | 6 | 0 |
| `variant.rs` | 2 | 3 | 3 | 0 |
| total | 37 | 54 | 76 | 3 |

The structs and enums with a `NodeId` or a `ListId` (source ids
included; the script cannot tell):

| Struct (file) | Fields that hold a NodeId or a ListId |
| --- | --- |
| `Work` (`args.rs`) | `Enter`, `Rebuild` |
| `Evaluation` (`args.rs`) | `values: Vec<NodeId>`, `statements: Vec<NodeId>` |
| `Plan` (`call.rs`) | `operands: crate::bir::ListId` |
| `Conditional` (`cond.rs`) | `condition: NodeId`, `then_: NodeId`, `else_: NodeId` |
| `Exit` (`exit.rs`) | `args: ListId` |
| `Plan` (`exit.rs`) | `body: NodeId` |
| `Row` (`export.rs`) | `stmt: NodeId` |
| `Init` (`export.rs`) | `Literal`, `Qualified`, `Var`, `Other` |
| `Replacement` (`export.rs`) | `Node`, `Member` |
| `Tables` (`export.rs`) | `values: Vec<NodeId>`, `path: Vec<NodeId>`, `later: Vec<NodeId>` |
| `Resume` (`expr.rs`) | `value: Option<NodeId>`, `body: NodeId`, `first: NodeId`, `second: NodeId`, `body: NodeId` |
| `Plan` (`loops.rs`) | `node: NodeId`, `nodes: [Option<NodeId>; 3]`, `blocks: [Option<ListId>; 3]`, `values: [Option<NodeId>; 2]` |
| `ProbeInput` (`mod.rs`) | `first: NodeId`, `test: NodeId` |
| `ProbeWork` (`mod.rs`) | `Enter`, `EnterChild` |
| `State` (`mod.rs`) | `tail_assignments: Vec<NodeId>`, `call_reversed: Vec<NodeId>`, `eta_arguments: Vec<NodeId>`, `switch_work: Vec<(NodeId`, `group_nodes: Vec<NodeId>`, `switch_output_nodes: Vec<NodeId>`, `switch_pairs: Vec<(NodeId`, `constant_children: Vec<NodeId>`, `constant_values: Vec<(NodeId`, `argument_values: Vec<NodeId>`, `external_values: Vec<NodeId>`, `location_work: Vec<(NodeId`, `scratch: Vec<NodeId>`, `catch_table: Vec<(NodeId`, `catch_work: Vec<NodeId>` |
| `Log` (`names.rs`) | `pending: Vec<NodeId>` |
| `Frame` (`names.rs`) | `statement: NodeId` |
| `Out` (`out.rs`) | `value: Option<NodeId>` |
| `Slot` (`out.rs`) | `Statement` |
| `StatementStack` (`out.rs`) | `held: Vec<NodeId>` |
| `Free` (`out.rs`) | `test: NodeId`, `first: NodeId` |
| `RealizeWork` (`out.rs`) | `Seq`, `Cond` |
| `Prim` (`prim.rs`) | `operands: crate::bir::ListId` |
| `Group` (`rec.rs`) | `node: NodeId` |
| `Member` (`rec.rs`) | `source: NodeId`, `code: Option<ListId>`, `placeholder: Option<NodeId>` |
| `Record` (`record.rs`) | `operands: ListId` |
| `Scratch` (`record.rs`) | `operands: Vec<NodeId>`, `values: Vec<NodeId>` |
| `Site` (`scope.rs`) | `node: NodeId` |
| `VarFacts` (`scope.rs`) | `site: NodeId` |
| `Scope` (`scope.rs`) | `spine: Vec<(NodeId` |
| `Plan` (`switch.rs`) | `scrutinee: NodeId`, `operands: crate::bir::ListId`, `default: Option<NodeId>`, `value: Option<NodeId>` |
| `Plan` (`try_.rs`) | `nodes: [Option<NodeId>; 3]`, `blocks: [Option<ListId>; 3]` |
| `Action` (`untagged.rs`) | `source: NodeId` |
| `ActionState` (`untagged.rs`) | `cached: Option<NodeId>` |
| `Storage` (`untagged.rs`) | `test_values: Vec<NodeId>` |
| `Plan` (`untagged.rs`) | `source: NodeId`, `operands: crate::bir::ListId`, `scrutinee: Option<NodeId>` |
| `Plan` (`variant.rs`) | `scrutinee: NodeId`, `value: Option<NodeId>` |


Read by hand, the ones that hold J: `Out::value`; `Free::Leaf` and the
`test` and `first` of its two combinations; `RealizeWork`;
`Slot::Statement` and `StatementStack::held`; `args::Work` and
`Evaluation`; in `State` the vectors `tail_assignments`,
`call_reversed`, `eta_arguments`, `switch_output_nodes`,
`constant_children`, `constant_values`, `argument_values`, `scratch`,
`external_values`, `external_pending`; `loops::Plan::blocks` and
`values`; `try_::Plan::blocks`; `rec::Member::code` and `placeholder`;
`untagged::ActionState::cached`, `Storage::test_values` and
`Plan::scrutinee`; `switch::Plan::value`; `variant::Plan::value`;
`record::Scratch`; every table of `export::Tables`. The rest are ids of
the source tree and stay.

**What the reviews left for T6x**, collected: the `constant_children`
field and its extra move (`konst.rs`); the functions that return
`B::node(..)` to a caller in their own file that wraps it again
(`compile_import`, `static_member`, `duplicate_record`, `record_rest`,
`recursive_dummy`); the turn-backs into `primitive_runtime`,
`if_statement` and `drop_pure_effect`; the receiver that `external.rs`
turns back for `import.rs::static_member`; the repeated four lines
around the two copies of `untagged.rs`; `IfLists` and
`simplify_if_head`; `function_of_block`; `push_list` and the operand
lists in the pool; the reserved pool list of a switch's actions; the
three edits of `export.rs` and its tables; the `Named` arm and the
three chain walks ("For T6v: a dotted global").

**The cut.** Storage first, then the bodies of each cluster of files,
then the functions that cross clusters. A handle is not `Copy`, so the
slices that change storage are the ones that change the most code that
is not a call: `Out` is passed by value in 37 constructions and read at
54 places.

| Slice | What changes | Files | Estimate | After | Side by side with |
| --- | --- | --- | --- | --- | --- |
| T6x-a1 | `StatementStack<B>`: the slots and `held` own `B::S`, `take_list` gives `B::L`; every caller wraps at the call; the reads still give rows | `out.rs`, `mod.rs`, the 16 files that call the stack | 511 measured on the probe, about 550 with cost notes | T6q, the design turn of T6x-a | none |
| T6x-a2 | The statement-holding fields of one file (`Evaluation::statements`, the `blocks` of the two plans, `rec::Member`, `tail_assignments`), `primitive_statement`, a hold filled by a sink; `loop_function_body` takes and returns a list, and `function_of_block` is deleted | `args.rs`, `loops.rs`, `try_.rs`, `rec.rs`, `tail.rs`, `prim.rs`, `expr.rs`, `mod.rs`, `out.rs`; the interface for the deletion | 154 measured, about 200 with the deletion | T6x-a1 | none |
| T6x-a3 | The stack's reads give references, `take(slot)`, the stack implements `Runs` and `if_in_place` calls `JsStmt::if_head`; `place`, `if_statement`, `unnest`, `single_assignment`, `assignment_statement` change with all their callers | `out.rs`, `cond.rs`, `location.rs`, `export.rs`, `mod.rs`, `exit.rs`, `loops.rs`, `switch.rs`, `untagged.rs`, `variant.rs` | about 475 measured | T6x-a2 | none |
| T6x-a4 | The reserved pool list of a switch's actions becomes a run of the stack taken with `take_actions`; `switch_output_nodes` and `ActionState::cached` hold handles | `exit.rs`, `switch.rs`, `ffi_args.rs`, `untagged.rs`, `mod.rs`, `out.rs` | about 210 measured | T6x-a3 | none |
| T6x-b | `Out<B>`, `Probed`, `Free`, `RealizeWork` and the five types that change with them: an output's value is a `B::E`. Built in four parts ("T6x-b: an output's value, as built"). On trunk: **b1** (pull request 355) `Free`, `RealizeWork`, `FreePool`, `ProbeInput` and `Realizer` hold `B::E`; **b2** (357) `Out::value` is `Option<B::E>`, one whole in 27 files; **b3a** (358) the turn-backs b1 and b2 left are removed in ten files. **b3b** (363), the close of a list and the unit's finish. `close::decide` takes the implementation and a list in flight and reads each statement where it is (`JsStmt::with_stmt_at`); `StatementStack::close` takes `B::L` and `take_list` loses the last `B::list_id`; the `return` arm names the returned value by its id for `scope::return_sites` (T6r). `extract_exports` takes the value as a handle and copies the export identifiers out of the block's shared payload, so `complete_unit` no longer walks the comma spine, copies the payload or writes it (`Node::set_block_info` is deleted). `finish` takes `B::L`, makes the root with `block_of` and reads it by its id until T6s. `FreePool::probe`, `ProbeInput` and the counter `probes` are deleted (`FreePool<Rows>` 88 to 80 bytes) and their two tests become tests of `FreePool::realize` | b3b: `close.rs`, `out.rs`, `mod.rs`, `export.rs` (`extract_exports` only), `bir/node.rs` (the deletion) | b3b: 118 lines added and 189 removed as built (the design turn's check measured 117 and 188); transition calls 437 to 433 | T6x-a4; b3b after this design turn | none |
| T6x-c1 | Bodies and private functions: the primitives. `values` becomes a vector of handles from `sequence_arguments` on; `constant_children` goes; the functions of the cluster that only the cluster calls take and return handles | `prim.rs`, `prim_cmp.rs`, `prim_block.rs`, `konst.rs`, `record.rs`, `import.rs`, `args.rs`, `call.rs` | On trunk, taken from the commits of its probe (draft pull request 365, which met no gap in the interface and measured 716 changed lines): **c1a** (pull request 366) the storage and `prim.rs`, transition calls 433 to 314; **c1b** the rest, 314 to 246. As built it differs from this row in five places. `values` is a `Vec<B::E>` drained once in order: no arm needs an element after a later one was moved. The row edits `mod.rs` for the types of five fields of `State`, and one test line of `ffi_args.rs`. `primitive_runtime` and `static_member` keep their signatures for T6x-d: the cluster calls their handle forms (`runtime_call`, `import::member`). `call_reversed` holds source ids and does not change; `number` and `string` of `konst.rs` are private (their rows in the callers' table are name matches). A self call turns its values back into `State::scratch` for `finish_self_call` (T6x-d), and `names::adopt` is given an id until T6r. Left in the row's files: 11 transition calls the script counts and 4 it does not (a transition function passed by path, `.map(B::node)`), each at a function of T6x-d or of another cluster | T6x-b | c2, c3, c4 |
| T6x-c2 | The same for the externals; the operand lists in the pool become operands pushed as they are converted, and `push_list` loses its five calls; the three chain walks read `var_of` first | `external.rs`, `ffi_args.rs`, `jsx.rs` (not `printed_form`, `jsx_tag`) | On trunk, taken from the commits of its probe (draft pull request 369; 706 changed lines, so cut in two by its commits): **c2a** the conversion and assembly of the arguments in `ffi_args.rs`, transition calls 199 to 159; **c2b** `external.rs`, `jsx.rs` and the three functions `prim.rs` calls, to 82. As built it differs from this row and from the row of T6x-d in these places. `compile_js_call`, `compile_js_object_create` and `compile_jsx` take handles already (a drain and an iterator), with their one caller each in `prim.rs`: they are no longer rows of T6x-d, and neither are `add_external_effect` and the functions of `ffi_args.rs` the callers' table lists, whose callers are all in `external.rs`. The row forms left by T6x-c1 lost their last callers: `call_node` is a test's helper, `primitive_runtime` and `static_member` are deleted. `push_list` has no call left in the lowering. One pool list fewer is made per assembled call. Two places of `jsx.rs` keep a form the interface cannot yet replace, each under a comment, and are owed by a design turn before T6x-f: `Js::jsx` reads the callee as its first operand while the lowering builds it last, so the operands wait in `State::external_values` (a `jsx` that takes the callee apart, as `call` does); `duplicate_jsx_key` reads the member chain of the key again by id, four `B::at` (a copy of a member chain by the interface). Owed as a test: a spliced array of 10,000 elements through `assemble_external_args_with_splice`, whose loop pair is one step an element | T6x-b | c1, c3, c4 |
| T6x-c3 | The same for conditionals and switches | `cond.rs`, `expr.rs`, `switch.rs`, `variant.rs`, `untagged.rs`, `location.rs` | On trunk, taken from the commits of the probe of c3 and c4 (draft pull request 368, which met no gap in the interface): 287 changed lines; the transition calls of the row's files go from 75 to 28. The plans hold the scrutinee as a handle (`switch::Plan<E>`, `variant::Plan<E>`, `untagged::Plan<S, E>`, and `Storage<S, E>` for the tests in flight); the functions of 3.6, `merge_assignments`, `assignment_statement` and `switch_key_expression` take and give handles. `expr.rs` and `location.rs` had nothing to convert, and the three fields of `Conditional` are ids of the source tree. What is left is wraps at `if_statement` and `drop_pure_effect`, rows of T6x-d: without the one turn-back of `finish_if`, each of the twelve calls of `if_statement` in `cond.rs` turns its test back. Every caller of `if_statement` is in a file of c3 or c4, so its row of T6x-d can follow these two directly and edits no other file | T6x-b | c1, c2, c4 |
| T6x-c4 | The same for loops, exits and recursion; `recursive_dummy` gives a handle to its two callers in `rec.rs` | `loops.rs`, `try_.rs`, `exit.rs`, `rec.rs`, `tail.rs`, `assign.rs`, `label.rs` | Built from the last two commits of the same probe, in a pull request of its own (it does not need c3): 52 changed lines; the transition calls of the row's files go from 17 to 8. `loops::Plan<L, E>` holds its two values as handles, `recursive_dummy` gives one, `recursive_block` calls `runtime_call`, and `finish_self_call` wraps each row it is given once. `try_.rs`, `exit.rs`, `assign.rs` and `label.rs` had nothing of their own to convert: their transition calls are wraps at `drop_pure_effect` and `if_statement` | T6x-b | c1, c2, c3 |
| T6x-d | The functions that cross clusters, each with all its callers in one slice: the 31 rows of the callers' table that are left after T6x-a (`drop_pure_effect`, `primitive_runtime`, `static_member`, `number`, `string`, `constant`, `add_external_effect`, `compile_js_call`, `compile_jsx`, `sequence_arguments`, ..., and `if_statement`, `assignment_statement` and `merge_assignments` for the expression each still takes or returns). `place`, `unnest`, `single_assignment`, `loop_function_body` and `locate_switch_run` are no longer rows: T6x-a changed the first four, and the last names a source node only. No turn-back is left between two files | every file of a row | On trunk, taken from the first three commits of the probe of T6x-d and T6x-e (draft pull request 376), which met no gap in the interface for this row: 106 changed lines, transition calls 82 to 49. As built the row is four functions, because T6x-c1 to c4 changed the others with their clusters (see the rows above): `if_statement` takes its test as a handle (callers in `cond.rs`, `exit.rs`, `loops.rs`, `switch.rs`, `untagged.rs`, `variant.rs`); `drop_pure_effect` takes its value as a handle (callers in `cond.rs`, `exit.rs`, `expr.rs`, `loops.rs`, `rec.rs`, `switch.rs`, `try_.rs`, `untagged.rs`, `unit.rs`); `finish_self_call` takes an iterator of handles and `call.rs` gives it the drain of its argument values, so a self call no longer moves them through `State::scratch`; `constant` gives a handle to its one caller in `mod.rs`. Neither path-form use the count script misses is left in these files. What is left outside `export.rs`: the four `B::at` of `jsx.rs` `duplicate_jsx_key`, and the test helpers `call_node`, `empty_block` and `raw_if` | c1 to c4 | none |
| T6x-e1 | `export.rs`: the export values, the fold's own declarations and the final list are handles of the interface (pull request 379) | `export.rs`, and the field `State::coercion` in `mod.rs` | On trunk as far as the interface allows, taken from the last four commits of the probe of T6x-d and T6x-e (draft pull request 376): about 335 changed lines, `export.rs` 36 transition calls to 18. Built: `Tables<E, S>` holds the export values as handles (`extract_exports` fills, `coerce_exports` drains, every arm moves the value once); `define` gives the declaration to its caller, which keeps it in `inserted` or the new table `tail` until `coerced_list` moves it into the list; `coerced_list` gives `B::L` in two passes without a buffer, and `mod.rs` no longer wraps it. The four kinds of place that still reach a node through its id are T6x-e3 and e4; the interface they need is in "T6x-e and T6x-f: the fold reads where its rows are" | T6x-d, T6q | none |
| T6x-e2 | `jsx.rs`: `compile_jsx` pushes the operands as they come and gives the callee to `Js::jsx_element`; `duplicate_jsx_key` copies with `Js::copy_members`; `Js::jsx` is deleted; `State::external_values` stays for `ffi_args.rs` | `jsx.rs`, `js.rs`, `rows.rs`, `js_tests.rs` | 54 lines added and 100 removed in the design turn's throw-away build; transition calls 30 to 26. Prompt in 11.9 | the design turn of T6x-e and f | none |
| T6x-e3 | `export.rs`, kinds 1 and 4: a row says where its statement is (a place of the stack, an index in its block, an index in `inserted` or `tail`) and every read of it goes from there (`with_block_stmt`, `lend_block_stmt`, `StatementStack::at_place`); a removed row is released when `coerced_list` takes the run, and the statements of a dissolved block are taken out by index (`take_block_stmt`); `build_rows` recurses, and two allocation counts of `unit.rs` move (103 to 102, 156 to 155) | `export.rs`, `out.rs` (two attributes), `unit.rs` (two numbers) | not built; the probe measured 434 changed production lines for these two kinds. No prompt until a build of it ran | T6x-e2 | none |
| T6x-e4 | `export.rs`, kinds 2 and 3 and the binder: an expression the fold names is a position (a row's initialiser, or the export value in hand); a use is replaced by `JsStmt::substitute` at its row's place, with rows and counts in `Tables::later`; `alias_of` reads `JsStmt::alias_at` | `export.rs` | not built; the probe measured 293 added and 129 removed lines for kind 2 and left kind 3 and the binder open. No prompt until a build of it ran | T6x-e3 | none |
| T6x-f | The transition functions leave the two traits: `from_node`, `node`, `at`, `stmt_from_node`, `stmt_node`, `list_from`, `list_id`, `push_list` (`function_of_block` left in T6x-a2). `Rows` keeps the first seven as functions of its own compiled for tests, which the tests of `out.rs`, `js_stmt_tests.rs` and `js_tests.rs` call (54 calls); the three generic test helpers go (`call_node`, `empty_block`, `raw_if`); `rg 'B::(from_node\|node\|at\|stmt_from_node\|stmt_node\|list_from\|list_id)\(' src/bir/lower` is empty. `norm::jm14_push_effect_expression`, which only tests call since T6q, gets `#[cfg(test)]` | `js.rs`, `js_stmt.rs`, `rows.rs`, `rows_stmt.rs`, `norm.rs`, `call.rs`, `cond.rs` | about 150 (estimate; not built). It does not wait for T6r: `names.rs` and `globals.rs` call no transition function | T6x-e4 | none |

Order: a1, a2, a3, a4, b, then c1 to c4 at once, then d, e1, e2, e3,
e4, f. The
four c slices share no file and edit no function of another cluster: a
function of the callers' table that takes or returns an expression
keeps its signature until d, and a c slice wraps at those calls as the
conversion slices did. A function that takes or returns a statement or
a statement list changed in T6x-a together with all its callers ("T6x-a:
the statement stack, after the probe" (b)). T6x-d is the one slice where
a signature changes together with callers in several files; if its
probe shows more than 600 lines it is cut by the callee's file
(`cond.rs` and `expr.rs`; `konst.rs`, `prim.rs` and `import.rs`; the
externals), in that order, each still with all callers of its rows.

#### T6x-a: the statement stack, after the probe

Status: probed and designed; not built. Row T6x-a of the cut above was
converted as a throw-away by a builder (the probe: branch
`bir-lower-js-interface-2`, never merged). It came to 1,093 changed
lines against the 500 estimated, found two things the traits lacked and
six signatures that have to change across files in this row. This
section adds what was lacking, takes the decisions the probe left, and
cuts the row into four slices; their prompts are in 11.9.

**How the additions were checked.** A test of a function nothing calls
shows the two sides alike, not that the lowering needs it. So the
probe's code was put on this turn's interface in a working copy that
was not pushed, its two gaps were closed with the functions below, and
the decisions of (c) and (b) that differ from the probe were applied.
On that copy `--lib bir::lower` reads 565 passed (the 562 of trunk and
the three interface tests of this turn that existed then), `--lib
bir::j` 58, none ignored; `cargo clippy --all-targets -- -D warnings`
is clean; the four allocation counts of `unit.rs` and every `size_of`
test hold. Each of the four slices below was also composed from the
probe's commits and run alone on the slice before it: 562 passed after
each. Not run on the copy: the JavaScript, standard-library and genType
parity suites, `Backend bridge coverage`, `Instruction count`, check
mode on the application. The builders' pull requests run them.

**Added to the interface in this turn** (signature and cost in
`js_stmt.rs`, body in `rows_stmt.rs`):

| Function | Cost | Probe site that calls it | Test |
| --- | --- | --- | --- |
| `JsStmt::stmt_id(&self, a, &S) -> u32`: the id of a statement in hand, read in place. It is what `Js::owner` gives for its value, what `block_ids` gives for it inside a block, and a key for `Js::kind_of` | O(1). Rows: the row. The builder: the `node_id` of the owned node, one load (a statement in flight is 24 bytes, the node and its row; the id is in the node, as it is for an expression) | `out.rs`: `note_empty_block` and `drop_empty_blocks` (the empty-block table names a statement, since a slot is reused); `export.rs::build_rows` (`Row::stmt` of each statement of the top level). The probe turned the handle into a row and back for these (`peek`) | `a_statement_in_hand_gives_the_id_its_readers_know_it_by` |
| `JsStmt::if_head(a, runs, &mut test, &mut yes, &mut no) -> Option<IfHead<S, R::Run>>` with `R: Runs<Self>`: rules 0 to 6 of J-S3 over two runs the caller holds; `None` when none applies, with the test and the runs as the rules left them | One step, and what the runs count for the statements they release and take; a negation stripped counts no step. A kept run is not scanned: the empty blocks it noted are dropped (`trim`), `last` and `only` are asked of it and nothing else | `cond.rs::if_in_place`, the one call of `norm::simplify_if_head` from the lowering. The probe called it through an adapter over the stack that gave rows | `if_head_over_two_runs_is_rules_0_to_6_of_j_s3` (11 tests and every pair of 10 branch shapes, against `js3_simplify_if` on pool lists, compared as trees); `if_head_costs_what_it_consumes_and_does_not_read_the_tail` (1,000, 2,000 and 10,000 statements) |
| `Runs<B>`: `trim`, `empty`, `last`, `only`, `release`, `take` over a `Run: Copy`. The statement stack implements it (T6x-a3) with `Run = Span` | each is the stack's function of the same work; the costs are in the trait | `impl Runs<B> for StatementStack<B>` in `out.rs`, in place of `impl norm::IfLists for StatementStack` in `cond.rs` | the two tests of `if_head`, over a test implementation that counts every statement it hands out |
| `rows_stmt::S::row` (`#[cfg(test)]`, not in the trait) | O(1) | the stack's test-only `statements` on rows, which the 23 tests that release a run row by row call | `a_statement_in_hand_gives_the_id_its_readers_know_it_by` |

`if_head` takes the stack and not two lists because the kept branch
must stay where it was lowered: as a list it would be moved once per
enclosing conditional. Its body on rows is `norm::simplify_if_head`
itself, reached through a 16-byte adapter (`rows_stmt::RunLists`) that
gives the rule each function of `Runs` under the name `norm::IfLists`
has for it. The rules are not moved out of `norm.rs` and not copied:
`js3_simplify_if` (`Rows::if_`) runs the same head over pool lists, so
a second body would be a second J-S3. `norm::IfLists`,
`norm::simplify_if_head` and `norm::IfHead` are therefore called by
`js3_simplify_if` and by `Rows::if_head` until T6s deletes `norm.rs`;
what T6x-a3 deletes is the lowering's own implementation of `IfLists`
(`cond.rs`). On the builder `if_head` is the head of `rules_s.rs`, and
every read of a run is a reference to an owned statement.

Nothing else was needed from the traits. Read for it: the probe's
`cond.rs`, `untagged.rs`, `location.rs`, `switch.rs`, `exit.rs`,
`ffi_args.rs`, `tail.rs` and `expr.rs`. `location.rs` needs a `&mut S`
from the stack (`head_mut`), `untagged.rs` a by-reference read of its
own pool (`Pool::get_ref`): both are the lowering's, not the
interface's.

**(a) What the stack's reads return, and the stack after the slice.**

A read returns a reference to the statement where it is, with its slot
where the caller goes on to take it. Not an id: every reader of the
interface takes `&S`, and on the builder the handle is the node, so an
id would have to be turned back into the statement by a lookup the
stack already did. Not a second reference type like `B::Ref` of
expressions: twelve sites read, and each reads through `stmt_kind`,
`value_of`, `branch_last_kind` or `stmt_located`, which take `&S`. The
three places that need an id call `stmt_id` on the reference.

At seven sites a statement is consumed while the stack still holds its
row (`take_value`, `take_if`, `unblock`, or a move to another slot),
and the slot is forgotten afterwards with `clear` or `kill`. With
handles the statement has one owner, so the stack gets `take(slot)`,
which moves it out and leaves the slot dead: `cond.rs` `unnest`,
`effect_output`, `merge_assignments` (twice), `merge_tail_guard`;
`switch.rs`, the declaration fold of the small switch; `untagged.rs`,
`Op::Block`. `clear` has no caller after it.

The functions of `StatementStack<B>` after T6x-a4 (`js: &mut B`, `a:
&mut Pools`):

| Function | Cost |
| --- | --- |
| `with_capacity(slots)`, `mark()`, `since(mark)`, `reserve()` | O(1); `with_capacity` one allocation |
| `push(B::S)`, `fill(slot, B::S)` | O(1), one move of the handle |
| `fill_held(slot, impl IntoIterator<Item = B::S>)` | one step per statement, each moved once |
| `held_mark() -> usize`, `hold(B::S)`, `fill_held_since(slot, mark)` | O(1) each: a hold filled by a sink (`expr.rs::hold_effect`), in place of collecting rows in `State::scratch` |
| `hold_run(slot, run)` | one step per slot of the run, each statement moved once |
| `statement_refs(run) -> impl Iterator<Item = &B::S>` | one step per slot of the run and per held statement |
| `first(run) -> Option<&B::S>`, `first_slot(run) -> Option<u32>`, `first_single_slot(run) -> Option<(u32, &B::S)>` | the holes and dead ranges before the first statement, counted in `scanned` |
| `only(run) -> Option<(u32, &B::S)>` | as `first`, twice |
| `last(run) -> Option<&B::S>`, `last_slot(run) -> Option<u32>` | O(1) on a trimmed run, else one step per trailing hole or dead range, counted ("T6x-b: an output's value, as built" (h)) |
| `at(slot) -> &B::S`, `head(slot) -> &B::S`, `head_mut(slot) -> &mut B::S` | O(1) |
| `take(slot) -> B::S` | O(1): one write, the slot is dead |
| `take_run(run)`, `take_run_rev(run) -> impl Iterator<Item = B::S>` | one step per slot of the run and per held statement, a dead range crossed in one; the caller kills the run |
| `trim(floor)`, `kill(run)`, `has_statements(run)`, `remove_empty(run)`, `append(first, second, value)` | as today |
| `note_empty_block(slot, id: u32)` | a binary search and an insertion among the unit's empty blocks; `id` is the block's `stmt_id` |
| `drop_empty_blocks(js, a, run)` | two binary searches, then one step per empty block of the run |
| `take_list(js, a, run) -> B::L` | one step per slot and per statement of the run, each moved once, and the close of the list |
| `take_actions(js, a, run) -> B::L` | `take_list` without the close: (c) |
| `close(a, ListId)` | as today, until T6x-b3b, which makes it `close(js: &B, a, B::L)` |
| `impl Runs<B>` | the six functions above under the names of `Runs` |
| `statements(run) -> impl Iterator<Item = NodeId>`, `#[cfg(test)]`, on `StatementStack<Rows>` only | the rows of a run, for the tests that release a run row by row |

Gone: `clear`, `statements_rev` and the by-row `statements` of
production (T6x-a3), and `peek`, which T6x-a1 adds and T6x-a3 deletes.

Sizes. `StatementStack<Rows>` stays 96 bytes and
`Option<Slot<rows::S>>` 12: both tests exist and move only by their type
argument. `held` becomes `Vec<Option<B::S>>`: a hold is moved out of
the middle of the vector (`take_run`, `hold_run` of a run that has a
hold) and `B::S` has no placeholder. On rows that is 8 bytes an entry
where it was 4 (`size_of::<Option<S>>() == 8` is pinned in
`js_stmt_tests.rs::sizes`). Accepted: an entry lives from the hold to
the list that takes it, rows are deleted by T6s, and the two forms
that avoid it are worse: an "absent" statement in the trait is a state
every reader would have to exclude, and uninitialised slots are
`unsafe`. On the builder the entry is the statement and the tag of an
option over an enum; T6v pins its size with the builder's stack. Not
measured in this turn.

**(b) The cross-file signatures.** Five functions of `cond.rs` and one
of `tail.rs` take or give a statement or a list of the stack, and are
called from other files:

| Function | On trunk | After | Callers in other files | Slice |
| --- | --- | --- | --- | --- |
| `cond.rs::place` | `(u32, NodeId)` | `(u32, B::S)` | `switch.rs` 1, `untagged.rs` 2, `variant.rs` 1 | a3 |
| `cond.rs::if_statement` | `(NodeId, Span, Span) -> NodeId` | `(NodeId, Span, Span) -> B::S` (the test stays a `NodeId` until T6x-d) | `exit.rs` 1, `loops.rs` 1, `switch.rs` 1, `untagged.rs` 1, `variant.rs` 1 | a3 |
| `cond.rs::unnest` | `-> Option<(u32, NodeId)>` | `-> Option<u32>`, the slot | `exit.rs` 1, `switch.rs` 1, `untagged.rs` 4, `variant.rs` 1 | a3 |
| `cond.rs::single_assignment` | `-> Option<(NodeId, NodeId)>` | `-> Option<u32>`, the slot (no caller reads the value) | `switch.rs` 1 | a3 |
| `cond.rs::assignment_statement` | `-> NodeId` | `-> B::S` (its `merged` argument stays until T6x-d) | `switch.rs` 1 | a3 |
| `tail.rs::loop_function_body` | `(LoopRef, FuncId, NodeId) -> NodeId` | `(LoopRef, FuncId, B::L) -> B::L` | `expr.rs` 1 | a2 |

They change in T6x-a, each together with all its callers in one slice.
Keeping them until T6x-d, as the cut had it, leaves a turn-back at
every one of those calls and a wrap in the callee, on values the stack
no longer gives as rows: five wraps at the callers of `if_statement`,
four turn-backs at the callers of `place`, and both directions of
`loop_function_body`.

The rule of the cut is rewritten with this: *a function that takes or
returns a statement or a statement list changes its signature in the
slice of T6x-a that changes what the stack gives or takes there,
together with all its callers; a function of the callers' table that
takes or returns an expression keeps its signature until T6x-d, and a
c slice wraps at those calls.* T6x-d's table loses `place`, `unnest`,
`single_assignment`, `loop_function_body` and `locate_switch_run`
(whose signature names a source node only); it keeps `if_statement`,
`assignment_statement` and `merge_assignments` for the expression each
still takes or returns.

**(c) The action lists of a switch.** Four places wrote the actions of
a switch into a reserved pool list (`exit.rs` the dispatch of a catch,
`switch.rs::finish_switch`, `untagged.rs` the value and `typeof`
switch) or collected them as rows in `State::scratch` (`ffi_args.rs`).
A handle cannot be written into a pool list out of order, so all four
stage their actions on the statement stack and take them as one list.

- `exit.rs`, `switch.rs` and `ffi_args.rs` push each action at the top
  and take the run. Nothing else is on the stack above the mark, so the
  layout before and after is that of trunk.
- `untagged.rs` takes the runs of its clauses while it assembles the
  actions. A push would land where the top clause run was just popped,
  below the mark. It reserves one hole per action above the clause
  runs, fills them in order and takes the holes' run. That changes the
  slot layout: every clause run becomes a dead range, where on trunk
  the last clause run is popped. For a switch of n clauses and a
  default whose runs have w slots each, trunk leaves 1 + n·w slots in
  the enclosing run (the switch and the dead ranges of the default and
  of all clauses but the last) and this form 1 + (n + 1)·w, with n + 1
  holes above them while the switch is assembled. The dead slots are
  slots the clauses pushed: the stack never holds more than was pushed
  and reserved since the enclosing run started, and the run's take
  pops them all. `out.rs`,
  `the_actions_of_ten_thousand_switches_leave_only_the_slots_of_their_runs`,
  runs this protocol on today's stack at 1,000 and 10,000 switches in
  one run: each leaves exactly its statement and the slots of its
  runs, the run's take empties the stack, and a read from the end of
  the run crosses the dead ranges of the last switch only (the same
  count at both sizes).
- The list is taken with `take_actions`, which is `take_list` without
  the close. An action is a block, and `close::decide` reads `return`s
  and declarations only: closing the list would cost a step per action
  that decides nothing and would move `close_steps` away from trunk's.

Not chosen: staging the actions at the end of
`State::switch_output_nodes` and listing them from there, which leaves
the stack's layout exactly as on trunk. Tried on the probe's code: it
compiles, and five allocation tests fail (two of them pins of
`unit.rs`), because that table is reserved for the outputs of a switch
and its actions outnumber them. Giving it a second reserve is a new
estimate to keep right in every unit; the stack already has its
capacity from the unit's output estimate.

This is the one place where a slice changes where statements sit on
the stack, and no parity suite has run on it. The prompt of T6x-a4
makes `Backend bridge coverage` at zero differences and the three
parity suites (JavaScript, standard library, genType) its gate, read
in CI before the pull request is marked ready.

**(d) `loop_function_body` on lists.** The body of a function goes
through the tail loop as the list it is, and `expr.rs` builds the
function with `JsStmt::function`. Per function through the tail loop
whose body has n statements, the lowering makes and releases one block
fewer and counts n + 3 steps fewer: no `block_of` of the body (1 + n),
no `unblock` (1 + n), no `block_of` of the one loop statement (2) and
no `function_of_block` (1), against n `take_at` and one `function` (2).
`js_stmt_tests.rs`,
`a_loop_function_over_a_list_is_the_one_over_a_block_in_fewer_steps`,
builds both and asserts the same function and n + 3 at 1,000 and
10,000. The rows built after the function get other ids on rows, which
no decision reads; `Backend bridge coverage` in the pull request of
T6x-a2 is the check.

What loses its last caller, and the slice that deletes it:

| Function | Deleted by | Tests that call it |
| --- | --- | --- |
| `JsStmt::function_of_block` (the trait, the body in `rows_stmt.rs`, its row in the header table there) | T6x-a2, in the commit after the one that removes its call (T6x-f had it) | `js_stmt_tests.rs`: `a_function_over_a_block_is_the_function_over_its_list` and `a_loop_function_over_a_list_is_the_one_over_a_block_in_fewer_steps`, deleted with it |
| `StatementStack::clear` | T6x-a3 | none |
| `StatementStack::statements_rev` | T6x-a3 | none |
| `cond.rs::terminal` | T6x-a3 (its one caller reads the last statement by reference while `self.statements` is borrowed, so the test is written out there) | none |
| `impl norm::IfLists for StatementStack` (`cond.rs`) | T6x-a3 | none; `norm_tests.rs` reads the source of `norm.rs` only |
| `norm::jm14_push_effect_expression` (no production caller since T6q) | `#[cfg(test)]` by T6x-f; deleted by T6s with `norm.rs` | `norm_tests.rs` 3 and `js_stmt_tests.rs` 2, as the oracle of the sink form |

**(e) Changes to earlier sections of this document**, each with its
reason:

- "T6: the interface" (a), the read-back table: `row_at(a, l, i)` is
  `kind_at(a, l, i)`. The trait never had `row_at`; the kind is what
  the one reader (`tail.rs`) needs. The table is not complete with
  it: a read by reference of statement `i` of a list in flight
  (`close.rs`, two sites, found by the probe of T6x-b) is open for the
  design turn of T6x-b.
- "T6: the interface" (a): `JsStmt` gains `stmt_id`, `if_head`, `Runs`
  and `IfHead` (above). `if_head` was named in (c) for J-S3 and had no
  signature.
- "T6x: the cut": T6x-a is four slices; the rule about signatures is
  the one of (b); `function_of_block` leaves in T6x-a2, not in T6x-f.
- `js_stmt_tests.rs`: the helper enum `St` gains `Empty` (an explicit
  empty block), which two existing tests match on. No expected value
  changed.

**The cut of T6x-a.** Measured on the probe's code: each slice is the
probe's commits of its files applied on the slice before, and for a3
and a4 the copy with the gaps closed. One after the other, none side
by side: `out.rs` or `mod.rs` is in every one.

| Slice | What changes | Files | Functions of shared files it edits | Changed lines | After |
| --- | --- | --- | --- | --- | --- |
| T6x-a1 | `StatementStack<B>`: the slots and `held` own `B::S`; `push`, `fill`, `fill_held` take handles, `take_list` and `drop_empty_blocks` take the implementation and `take_list` gives `B::L`. The reads still give rows, through `peek`. Every caller wraps at the call | `out.rs`; `mod.rs`; and for their calls of the stack `args.rs`, `assign.rs`, `cond.rs`, `exit.rs`, `export.rs`, `expr.rs`, `external.rs`, `ffi_args.rs`, `loops.rs`, `prim.rs`, `rec.rs`, `switch.rs`, `tail.rs`, `try_.rs`, `untagged.rs`, `variant.rs`, `oracle_tests.rs` | `out.rs`: every function of the stack; `mod.rs`: the field `statements`, the pushes of the realisation, the two lists of `finish` | 511 measured (`out.rs` 290), about 40 more for cost notes | trunk with this turn's interface |
| T6x-a2 | The fields that hold statements and lists of one file: `Evaluation::statements`, `loops::Plan::blocks`, `try_::Plan::blocks`, `rec::Member::{code, placeholder}`, `State::tail_assignments`; `prim.rs::primitive_statement`; a hold filled by a sink; `loop_function_body` on lists with its caller; `function_of_block` deleted | `args.rs`, `loops.rs`, `try_.rs`, `rec.rs`, `tail.rs`, `prim.rs`, `expr.rs`, `mod.rs`, `out.rs`; `js_stmt.rs`, `rows_stmt.rs`, `js_stmt_tests.rs` for the deletion | `out.rs`: `held_mark`, `hold`, `fill_held_since` (new); `mod.rs`: the types of five fields | 154 measured, about 45 more for the deletion | a1 |
| T6x-a3 | The reads by reference, `take(slot)`, the stack implements `Runs`, `if_in_place` calls `if_head`, `stmt_id` keys the empty blocks; the five signatures of `cond.rs` with all their callers; `location.rs`; `export.rs::build_rows` | `out.rs`, `cond.rs`, `location.rs`, `export.rs`, `mod.rs`; and for the callers `exit.rs`, `loops.rs`, `switch.rs`, `untagged.rs`, `variant.rs` | `out.rs`: the reads, `note_empty_block`, `drop_empty_blocks`, `take`, `take_run`, `take_run_rev`, the test-only `statements`; `mod.rs`: `append_outputs` (one line) | about 475 measured (`out.rs` 200, `cond.rs` 239) | a2 |
| T6x-a4 | The actions of a switch on the stack (`take_actions`); the fields `State::switch_output_nodes` and `untagged::ActionState::cached` hold handles | `exit.rs`, `switch.rs`, `ffi_args.rs`, `untagged.rs`, `mod.rs`, `out.rs` | `out.rs`: `take_actions` (new), `take_list`; `mod.rs`: the types of three fields | about 210 measured (`untagged.rs` 103) | a3 |

a1 is accepted at about 550 lines and not cut again. It is one type
that every file uses: the stack cannot compile on handles without each
of its callers wrapped, and the 290 lines of `out.rs` are the methods
of one struct. The holding fields, which the probe's report put in the
same half, are a2: they are what took that half over 600. The sum of
the four is above the probe's 1,093 because a later slice rewrites
lines an earlier one wrapped (39 of the 80 wraps of a1 meet a
turn-back and cancel in a2 to a4).

**Counts** (`python3 scripts/count_lowering_ids.py`, totals; "after" is
the probe's code with the gaps closed and the decisions above):

| | Trunk | After T6x-a |
| --- | --- | --- |
| lines | 15,513 | 15,689 |
| functions with a `NodeId` or `ListId` in their signature | 217 | 191 |
| of these, touching J | 105 | 97 |
| transition calls | 628 | 498 |
| `from_node` / `node` / `at` | 270 / 142 / 68 | 271 / 143 / 68 |
| `stmt_from_node` | 38 | 8 |
| `stmt_node` | 82 | 3 |
| `list_from` | 28 | 2 |
| `list_id` | 0 | 3 |
| `function_of_block` | 1 | 0 |
| `push_list` | 5 | 5 |
| raw J sites | 165 | 161 |
| `statements.push` / `fill` / `place` | 76 | 81 |
| `IfLists` / `simplify_if_head` named | 3 | 1 (a comment of `close.rs`) |

What is left of the statement transition after a4: `cond.rs` 3 and 2
`list_from` (two `#[cfg(test)]` helpers, `empty_block` and `raw_if`);
`export.rs` 4 `stmt_from_node` and 1 `stmt_node` (T6x-e); `mod.rs` 4
`stmt_from_node` around the raw constructions of the realisation and 2
`list_id` into `finish` (T6x-b); `out.rs` 1 `list_id` into `close`
(T6x-b).

**How a builder may use the probe.** Its code for a file may be read
as a starting point (`git show
origin/bir-lower-js-interface-2:compiler-rust/src/bir/lower/FILE`). It
is unreviewed and it predates this turn: where a prompt gives code,
the prompt's code is the one to write. Its gaps are closed with the
functions above, every function a slice changes gets its cost note
(the probe has none, which is why its `script-tests` job is red:
`scripts/check_lowering_cost_docs.py`), and nothing is merged or
cherry-picked from that branch.

#### T6x-b: an output's value, as built

Status: the row is on trunk. b1, b2 and b3a were taken from the second
probe; b3b is designed here, was checked as said below, and was built
from its prompt in 11.9 as pull request 363 (four commits, no deviation
from the task; transition calls 437 to 433). Row T6x-b was probed twice
(pull requests 345 and 353, neither merged). The second probe was made
on trunk after T6x-a4 and its body is the report this section starts
from.

**(a) What was built, and where it differs from the row.**

| Part | Pull request | What it changed | Transition calls |
| --- | --- | --- | --- |
| b1 | 355 | `Free`, `RealizeWork`, `FreePool`, `ProbeInput` and `Realizer` hold `B::E`; `Out::value` unchanged. About 120 lines | 498 to 507 |
| b2 | 357 | `Out`, `Probed` and `ProbePlan` take the implementation as a type parameter and `Out::value` is `Option<B::E>`; `ProbeRules` has the associated type `Js`. About 540 lines in 27 files, one whole | 507 to 493 |
| b3a | 358 | The turn-backs b1 and b2 left are removed in ten files; `State::pure_expression` is `#[cfg(test)]`. About 120 lines | 493 to 437 |

The row said one slice of 600 lines; it is three and a fourth to come.
It listed four types; nine change (`ProbeInput`, `Realizer`,
`ProbePlan`, `SourceProbe` and `ProbeRules` with them). It said "`Out`
stops being a value that is copied": `Out` never derived `Copy`; what
was copied was the `Option<NodeId>` read out of `.value`, at the 15
sites of the report's section 3, each of which is now a move
(`Option::take`) or a read in place. Its "37 constructions and 54
reads" were columns of the script, not sites: 24 and 28 production
lines changed.

On trunk after b3a: `--lib bir::lower` 568 passed, `--lib bir::j` 58,
`--lib emit::builder` 26, none ignored; the four allocation counts of
`unit.rs` are 86, 103, 86, 156; `size_of::<Rows>()` is 416; `Out`,
`Probed`, `Free`, `FreePool` and `StatementStack` on rows are 20, 20,
16, 88 and 96 bytes, as before the row. `Instruction count` read
+0.014%, −0.039% and +0.023% on the three pull requests (the default
build does not reach the lowering).

*Steps.* b3a builds a value through the interface where the lowering
called `bir::j` directly: `Js::var`, `Js::qualified`, `JsStmt::declare`,
`assign`, `return_`, `Js::release`, `Js::seq_rule` and `JsStmt::effect`
count a step on rows (`Rows::steps`) where `pure_expression`,
`j::declare`, `Bir::release` and `jm1_js_seq` counted none. No node
differs. One test of the lowering reads that count across these calls,
and it reads a relation, not a number: `tail.rs`,
`a_chain_of_merged_guards_moves_each_statement_once`, requires the
interface's steps to grow linearly from 1,000 to 2,000 to 10,000
levels, which holds with a constant more per level as it did without.
Found with `rg -n 'steps\(&|\.steps\(\)' src/bir/lower src/bir/shadow.rs
src/lambda`: beside it the search matches `js_tests.rs` and
`js_stmt_tests.rs` (the interface's own tests, which build through the
interface on both sides of every comparison), `names.rs`
(`Replayed::steps`) and `globals.rs` (a local counter of its tests).
The counters the other tests read (`SwitchStats`, `close_steps`,
`StatementStack::copied` and `scanned`, `Coerced::steps`) are not
`Rows::steps`. The row of the table said "no lowering test reads the
count across them"; it is corrected by this paragraph.

**(b) What b3b lacked, and what this turn added.** Two places of the
probe could not be written through the interface. One gets a function;
the other needs none.

| | Decision | On rows | On the builder | Probe site that uses it | Tests |
| --- | --- | --- | --- | --- | --- |
| A statement of a list in flight, read by reference | `JsStmt::with_stmt_at<R>(&self, a, list, index, read: impl FnOnce(&Self::S) -> R) -> R`. O(1) and what `read` costs; counts no step; allocates nothing | `read(&S(a.lists.get(list)[index]))`: the row of the pool entry is named for the length of the call; no row is read to find it | `Builder::statement_at(list, index)`, which exists since T6b; the reads a declaration and a `return` then need are in the handle's row (`kind`, `payload`, `aux`) and in `S::value`, added here: the expression a statement evaluates first, in place, O(1) | `close::decide`, both arms: the three `PROBE-GAP 1` comments of `git show e1e5175130` | `js_stmt_tests.rs`, `a_statement_of_a_list_in_flight_is_read_where_it_is`; `builder_tests.rs`, `the_statements_of_a_list_in_flight_are_read_where_they_are` and `a_statement_reads_the_expression_it_evaluates_first` |
| The payload of the unit's export block | No function. `export.rs::extract_exports` holds the block literal by reference when it reads the exports (it walked to the end of the comma spine to find it): it reads the tag through `Bir::block_tag` and copies the identifiers, where it took them out of the payload. `complete_unit` loses its walk, its copy of the payload and `Node::set_block_info`, which has no other caller | the same code | the same code: the payload is in the pools on both sides, and nothing is written into the owned node | `complete_unit`, the `PROBE-GAP 2` comment of `git show 6b6be5b6e2` | exist: `unit.rs`, `export_consumption_does_not_empty_shared_block_metadata`, `supported_unit_exercises_both_texts_and_shared_export_coercion` and the four allocation counts |
| The root block in `finish` | No function. `finish` takes `B::L`, makes the root with `JsStmt::block_of` and reads its id with `JsStmt::stmt_id` | the row | T6s rewrites `finish` (the program is the list) | `finish`, `complete`, `complete_unit` | the lowering's tests |

*The read by reference: why a closure.* `decide` reads, of a statement
of the list: its kind (`kind_at`, which exists); of a declaration the
variable (`declared`), the declaration kind (`stmt_aux`) and of its
value the `STRICT` flag and whether it is a function literal that may
be inlined (`value_of`, then `Js::has` and `Js::function_of`); of a
`return` its value. Every one of these is a reader of a statement in
hand that takes `&S`. Three forms give them without detaching:

- a function that returns `&Self::S`. Not possible on rows without
  `unsafe`: the pool stores row ids, not statements, so there is
  nothing for the reference to point at;
- position twins of each reader (`declared_at`, `aux_at`, `value_at`).
  Three functions now and one more for every later reader of a list,
  each a second name for a reader that exists;
- one function that lends the statement to a closure. Chosen: one
  function, every reader of `&S` works under it, and the statement
  cannot leave the list because the closure is given a reference.

What the closure cannot do is return a reference into the statement
(`value_of` gives a `Ref` that lives as long as the `&S`). `decide`
does not need to: it returns a `Decision` (8 bytes) from the
declaration arm and the id of the returned value from the `return`
arm.

`Rows::take_at` does not detach, and that is a fact, not a fault: a
list in flight is a pool list no node holds, its statements have no
parent, and `take_at` gives the entry (the header table of
`rows_stmt.rs` says so). The report's item reads as a fault only
because the probe used a transition call to read without taking;
`with_stmt_at` makes the question irrelevant to `decide`, and `take_at`
is unchanged.

*The step test.* A reader counts no step, so the relation is on the
rows read (`Bir`'s test counter of row reads): reading the first, a
middle and the last statement of a list with the readers `decide` uses
reads the same number of rows at each position, and the same at 1,000
and at 10,000 statements. Seen to fail with a body that walks to the
statement (6 rows read against 505). What it cannot see is a walk that
reads no row (a scan of the pool's ids): the body is one indexed read
of a slice, and on the builder one indexed read of a vector, which has
no counter; the builder's test pins that the reads count no step and
leave the list whole at both sizes.

*The payload: why the fold and not a function of `Js`.* The copy
exists because the fold took the identifier vector out of the block's
payload, and the payload is the shape's: `Bir::block_info` interns one
per distinct tag, so another block of the same shape, and the source,
share it. `complete_unit` therefore gave the unit's block a payload of
its own before the fold emptied it. The fold already holds what it
needs: it finds the block literal at the end of the comma spine by
reference and reads its `JsId`. Copying the identifiers there (one
`Vec` clone, the allocation `complete_unit` made) leaves the shared
payload untouched, so no payload is written into a node and no node is
found a second time. Per unit: one `JsPayload` fewer in the pool, the
same number of allocations. The fold reads the tag through
`Bir::block_tag`, which also reads a block whose shape is a constant's
(`JsPayload::ConstantBlock`); `complete_unit`'s copy turned that into a
`JsPayload::Block` on the way, which is why the fold matched `Block`
only.

Not chosen: `Js::set_info_at_seq_end(a, &mut E, JsId) -> bool`, the
probe's proposal. It is a second walk of the spine the fold walks, it
is O(spine) on the builder through `&mut` operands, and it exists for
one call that the fold makes unnecessary.

What changes on rows: the `JsId`s of payloads made after the fold are
one lower, and the pool has no emptied copy. No decision reads a
`JsId`'s value. Checked by the lowering's tests (the constant-block
unit runs `check_lower`); `Backend bridge coverage` in the pull request
of b3b is the gate.

`extract_exports` takes the value as `Option<B::E>` in the same commit
(it has one production caller, `complete_unit`, and one test): the body
changes there anyway, and `complete_unit` then makes no node id of the
unit's value at all.

*The root.* The rest of `finish` reads the root as a row three times:
`Bir::finish_bulk(root)`, `replay_names(root, ..)` (`names.rs`, T6r)
and `bridge_j::Imported::from_lowering(arena, root, ..)` (T6s). So the
root stays a row until T6s. It is made through the interface
(`block_of`, which is `Bir::block_from_list` on rows and counts one
step and one per statement) and read by its id (`NodeId(js.stmt_id(a,
&root))`), not turned back with `B::stmt_node`: T6x-f can then delete
the transition functions while `finish` still has its row. An id
made into a row this way is the form `export.rs` and `jsx.rs` already
use where a row is still needed (`rg -n 'NodeId\(self\.js\.(id|stmt_id)\('
src/bir/lower` shows ten lines there, and this one after b3b); the
slice that removes the last reader of the row removes the line. T6r
changes `replay_names` to take the statement; T6s deletes
`finish_bulk`, the importer and this line.

**How it was checked.** A test of a function nothing calls shows the
two sides alike, not that the lowering needs it. In a copy of this
turn's tree that was not pushed, b3b was built as the four commits of
its prompt, from the probe's `close.rs` and its hunks of `mod.rs`
(`complete_unit`, `complete`, `finish`) with the gaps closed as above.
After each of the four commits: `--lib bir::lower` 569 passed (trunk's
568 and this turn's interface test), `--lib bir::j` 58, `--lib
emit::builder` 28 (trunk's 26 and this turn's two), none ignored, no
compiler warning. The four were then put on this turn's final head,
which has three more tests of the lowering: 572, 58 and 28. On the
last: `cargo clippy --all-targets -- -D
warnings` clean; `cargo doc` with warnings denied clean;
`check_lowering_cost_docs.py --base` prints `changed/new=8;
missing/generic=0; removed=0`; the four allocation counts hold at 86,
103, 86, 156; the close test of `close.rs` reads the same 10,004 steps
and no allocation; transition calls 437 to 433; 117 lines added and
188 removed in five files (`close.rs`, `out.rs`, `mod.rs`, `export.rs`,
`bir/node.rs`). One size moves, by a deletion: `FreePool<Rows>` 88 to
80 ((f)). The shortcut was run too: the copy deleted from
`complete_unit` and the fold left taking the identifiers out fails six
tests (the two export tests of `unit.rs` and the four allocation
counts). Not run on the copy: `Backend bridge coverage`, the parity
suites, `Instruction count`, check mode on the application. The
builder's pull request runs them.

**(c) The `Return` arm of `close::decide`.** It stays on a row until
T6r, as one named turn-back: the arm reads the id of the returned
value under `with_stmt_at` and calls `scope::return_sites(bir,
NodeId(id), last)`. `return_sites` is not given a signature on the
interface now, for two reasons read off the code. It keeps its pending
operands in `Scope::spine`, a vector of rows that lives across calls;
a `Ref` of the builder is a borrow and cannot be kept there, so the
generic form is a descent the implementation owns, of the kind T6r adds
for function literals and globals (`JsStmt::functions`, `globals`), not
a change of parameter type. And it has a second caller on rows,
`norm.rs` (J-S3, where a branch becomes a list of its own), which T6s
deletes with the file.

What T6r does with it: adds the descent to `JsStmt` beside its other
two (the calls in tail position of a `return` in hand: both branches
of a conditional, the last operand of a sequence, a call of a
variable; the same steps), calls it from `decide` under `with_stmt_at`,
and makes `VarFacts::site` the id the interface gives (production only
compares it with `NO_SITE`: `rg -n '\.site\b' src/bir` shows `close.rs`
as its one reader). Until T6s `Rows` implements the descent by calling
`return_sites`; T6s deletes `return_sites` and `Scope::spine` with
`norm.rs`. If T6r's design turn finds the descent does not fit its
walk, the turn-back stays until T6s and nothing else depends on it:
it uses no transition function.

**(d) The leaves.** `Js::var` builds a strictly pure node
(`plain::node` sets `STRICT` on a variable). `Js::qualified` and
`Js::undefined` do not, where `pure_expression` did, because whether a
module reference or an `undefined` is known pure is the caller's
knowledge: six sites of `qualified` build it without the flag, as
they did with `plain::node` before the interface (`prim_block.rs` 2,
`prim.rs`, `jsx.rs`, `external.rs` 2). So the pair `qualified` then
`assume_strict` is the form, and no constructor is added: a
`qualified_strict` would be a second name for two sites, and a
constructor that always marks would be wrong at six.

Every site where a node is made and then marked (`rg -n 'assume_strict'
src/bir/lower`, 18 calls outside the trait):

| What is marked | Sites |
| --- | --- |
| `qualified` | `mod.rs` `enter` (the global leaf); `call.rs` `finish_application` (an external callee) |
| `copy_leaf` of a module member | `export.rs` `copy_replacement` |
| `var` (the flag is already set: the mark writes the bit it has) | `args.rs` `evaluate_now`; `external.rs` `hold_external_receiver`, `compile_js_object_create` 3, `translate_scoped_global_value`; `ffi_args.rs` `hold_in_variable`; `call.rs` `apply_with_arity`; `jsx.rs` `jsx_callee`; `import.rs` `import_of_path`, `wrap_then_path` |
| a node that is not a leaf | `rec.rs` `recursive_dummy` (an array or an object); `args.rs` `evaluate_now` and `ffi_args.rs` `hold_external_arg` (a `refill`); `konst.rs` `strict` (a constant) |

None can be reached with the flag missing: at each site the mark is
the statement after the construction, in straight-line code, before
the handle is given to anything. The eleven marks of a `var` are
no-ops left by the conversion slices; T6x-c1 (`args.rs`, `call.rs`,
`import.rs`) and T6x-c2 (`external.rs`, `ffi_args.rs`, `jsx.rs`) delete
them in their files, and each says so in its end state. The test-only
`complete` of `mod.rs` makes its `undefined` the same way in b3b.

**(e) `append_outputs`.** It keeps its value parameter and owns the
value it is given (its doc comment states the rule since pull request
357). Five of its eight calls give the value moved out of the second
output; three give `None`, because the caller has consumed that value
or keeps it for itself (`expr.rs` twice, `unit.rs` once). Not chosen:
the first probe's form, a `bool` for "the second output's value is the
result's". The function would move the value out of `second` itself,
which saves a line at five calls and leaves the other three a flag to
get right in place of a value they no longer hold. Accepted as built.

**(f) `FreePool::probe` and `ProbeInput`.** Neither has a production
caller: `rg -n 'ProbeInput|\.probe\(cx' src/bir/lower` shows the
definition, the body of `probe` and two tests of `out.rs`; the lowering
pushes `Free` records itself (`cond.rs`, `expr.rs`, `mod.rs`
`probe_leaf`). b3b deletes both, with the counter `FreePool::probes`
that only `probe` wrote, in its last commit. `FreePool<Rows>` is then
80 bytes (the size test and the cost note of `State::realize` move
from 88, by the deleted field). Not `#[cfg(test)]`: a function kept
for its tests is a second path that the tests then keep alive.

The two tests were tests of `probe`'s policy, which production has in
`cond.rs::finish_if`. They become tests of `FreePool::realize`, which
is what runs: `ten_thousand_deferred_nodes_are_realized_once` builds
the chain of 10,000 sequences with `push`, as the lowering does, and
keeps its assertions on the result, on `realized` and on the order of
the visits (it loses the one on `probes`);
`a_deferred_conditional_is_realized_after_its_branches` replaces
`nonfree_child_is_kept_without_reprobing` and asserts the order then,
else, test and that an output that is not deferred is returned without
a realization. The prompt gives both verbatim.

**(g) The turn-backs T6x-b leaves, and the slice that removes each.**
On this turn's head, the transition calls under a comment that names a
later slice, and the others the row leaves:

| File, function | The call | Because | Removed by |
| --- | --- | --- | --- |
| `call.rs` `finish_application` | `B::from_node(value)` | `call_node` and `apply_with_arity` give rows | T6x-d |
| `cond.rs` `finish_if` | `B::node(test)` | the rows of 3.6 (`effect_conditional`, `return_conditional`, `assigning_conditional`) take a row | T6x-c3 |
| `variant.rs` `bind_named_scrutinee` | `B::node(..)` twice | `Plan::value` holds a row | T6x-c3 |
| `mod.rs` `enter` | `B::from_node(self.constant(value))` | `konst.rs::constant` gives a row | T6x-d |
| `unit.rs` `lower` | `<Rows as js::Js>::node(value)` into `drop_pure_effect`. Written on `Rows` by name (the function is not generic), so `count_lowering_ids.py` does not count it | `expr.rs::drop_pure_effect` takes a row | T6x-d, with the row of `drop_pure_effect` |
| `out.rs` `take_list` | `B::list_id(list)` into `close` | `close` takes a pool list | T6x-b3b |
| `mod.rs` `complete_unit`, `complete` | `B::list_id(..)` twice, `.map(B::node)` twice, `B::stmt_from_node` | `finish` and `extract_exports` take rows | T6x-b3b |
| `mod.rs` `complete_unit` (after b3b) | `B::list_from(self.coerced_list(run))` | `export.rs::coerced_list` gives a pool list | T6x-e |
| `close.rs` `decide` (after b3b) | `NodeId(js.id(..))`; not a transition function | `scope::return_sites` takes a row | T6r ((c)) |
| `mod.rs` `finish` (after b3b) | `NodeId(js.stmt_id(..))`; not a transition function | `finish_bulk`, `replay_names` and the importer take a row | T6s ((b)) |

Every other transition call on trunk (433 after b3b) is inside the
cluster of a c slice or `export.rs`, without a comment: the counts by
file are in the table of T6x and in the probe prompt of T6x-c1.

**(i) What the probes of T6x-c1 to f start from.** Counted on this
turn's head (`python3 ../scripts/count_lowering_ids.py` from
`compiler-rust`; 437 transition calls, 433 after b3b). These counts
replace the ones in the rows of the table of T6x, which were taken
before T6x-a or after it.

| Row | Files and their transition calls | What T6x-b changed in the row |
| --- | --- | --- |
| T6x-c1 | `prim.rs` 133 (123 `from_node`), `prim_cmp.rs` 7, `prim_block.rs` 0, `konst.rs` 15, `record.rs` 7, `import.rs` 8, `args.rs` 18, `call.rs` 10: 198 | A value arrives as a handle: `sequence_arguments` takes `&mut [Out<B>]` and moves each value out, and turns it back where it pushes into `values: &mut Vec<NodeId>` (`args.rs`, three arms); `primitive_result` takes `B::E` and `call.rs` wraps `values[0]` for it. So the row starts at the push into `values`, not at the output. `probe_leaf` takes a handle, which removed five turn-backs at its callers |
| T6x-c2 | `external.rs` 33, `ffi_args.rs` 53, `jsx.rs` 19: 105, and 5 `push_list` | `hold_external_receiver`, `hold_external_arg` and `hold_external_obj_args` read an output's value in place and take it only where they hold it; what they hand on is still a row (`external_values`, the argument lists). `ffi_args.rs` fell from 64 to 53 and `external.rs` from 40 to 33 |
| T6x-c3 | `cond.rs` 35, `expr.rs` 2, `switch.rs` 5, `variant.rs` 13, `untagged.rs` 20, `location.rs` 0: 75 | `cond.rs` fell from 55 to 35 and `expr.rs` from 11 to 2: `finish_if`, `short_circuit`, `free_value`, `free_effect`, `push_s_if_empty`, `output` and `hold_effect` take or give handles. What is left in `cond.rs` is the rows of 3.6 (`effect_conditional`, `return_conditional`, `assigning_conditional`, behind the one `B::node(test)` of `finish_if`) and `Conditional`'s three fields (corrected when the row was built: they are ids of the source tree and hold no value); in `variant.rs`, `Plan::value` |
| T6x-c4 | `loops.rs` 4, `try_.rs` 1, `exit.rs` 2, `rec.rs` 6, `tail.rs` 4, `assign.rs` 0, `label.rs` 0: 17 | `recursive_block` takes a handle and `assign.rs` has nothing left. The plan fields `loops::Plan::values` hold rows |
| T6x-d | 33 rows in the callers' table of the script, 97 calls in other files. Three are not rows of this slice: `enter` (matched by name against `names.rs`), `locate_switch_run` (a source node only) and `extract_exports` (b3b) | `realize_conditional`, `append_outputs`, `leaf`, `probe_leaf` and `primitive_result` left the table. `drop_pure_effect` lost its caller in `mod.rs` (`Realizer::effect` calls `JsStmt::effect`) and has one written on `Rows` by name in `unit.rs`, which the script does not count ((g)) |
| T6x-e | `export.rs` 37 (10 `from_node`, 7 `node`, 15 `at`, 4 `stmt_from_node`, 1 `stmt_node`), 36 after b3b; and ten `NodeId(self.js.id(..))` in `export.rs` and `jsx.rs` | After b3b `extract_exports` takes the unit's value as a handle; `Tables::values` still holds rows (it turns each back with `B::node(self.js.pop())`). `coerced_list` gives a pool list that `complete_unit` wraps ((g)) |
| T6x-f | The seven transition functions of the two traits, `push_list`, and what calls them when e is merged | After b3b nothing in `close.rs` or `out.rs` calls one; `mod.rs` has two, both another slice's ((g)). `finish` reads the root by its id and needs none |

Read off the code for the design of c1, not probed (corrected in the
review of this turn, which read every use): the vector the values of an
application or a primitive are sequenced into is one field of `State`,
`argument_values`. In production it is taken and given back in two
functions, both of c1: `finish_application` (`call.rs`) and
`finish_primitive_payload` (`prim.rs`). Every other file that names it
(`konst.rs`, `import.rs`, `prim_block.rs`, `external.rs`, `ffi_args.rs`,
`jsx.rs`, `tail.rs`) reads its capacity in an allocation test and
nothing else, so the field's element type can change in c1 without a
wrap in another cluster. What crosses clusters is what is made from it:
`finish_self_call` (`tail.rs`, c4) takes `values: &[NodeId]` from
`call.rs`, a row of T6x-d, and the externals are given a pool list
(`compile_js_call`) or an iterator of rows (`compile_jsx`). Whether c1
can be built beside c2 to c4 with those calls wrapped is the first
question of c1's probe.

**(h) Changes to earlier sections of this document**, each with its
reason:

- "T6: the interface" (a), the read-back table: the read by reference
  of a statement of a list in flight, left open there and in "T6x-a:
  the statement stack, after the probe" (e), is
  `JsStmt::with_stmt_at`.
- "T6: the interface" (a), the read-back table, "`JSeq` ends in
  `complete_unit`, `extract_exports`": after b3b only `extract_exports`
  walks the spine. (Edited in the review of b3b, pull request 363.)
- "T6x: the cut", the row of T6x-b: rewritten for b3b. `close.rs`
  "takes the interface from `out.rs`" as the row said; what the row did
  not say is in (b), (c) and (f).
- "T6x-a: the statement stack, after the probe" (a), the table of the
  stack: `close(a, ListId)` is `close(js: &B, a, B::L)` after b3b.
- "T6: the cut of the interface, revisited", row T6x: `State::{leaf,
  seq, effect}` were b3a's; `complete_unit`, `complete` and `finish`
  are b3b's. (That row is left as written: it names the functions of T6x, and this
  bullet says which part converted each.)
- T6r gains one thing ((c)): the descent of a returned value. T6s
  gains the root's row in `finish` ((b)).
- "T6x-a: the statement stack, after the probe" (a), the table of the
  stack: `last`, `last_slot`, `take_run_rev` and `trim` cross a dead
  range from its end in one step, where they took one per slot. `kill`
  marks the last slot of a range of more than one slot with the
  range's length (`Slot::DeadEnd`); a slot stays 12 bytes on rows. The
  read from the end that (c) there describes for the actions of a
  switch crosses one step per run of the last switch, not one per
  slot.
- One expected value of a test of the lowering changes on trunk in
  this turn, by that change: `out.rs`,
  `the_actions_of_ten_thousand_switches_leave_only_the_slots_of_their_runs`
  counted 8 slots crossed (four dead ranges of two slots) and counts
  4. In b3b one pinned size moves by a deletion (`FreePool<Rows>`, 88
  to 80) and two tests of a deleted function are replaced ((f)).
- Tests added in this turn, each seen to fail without what it is there
  for: rule 6 of `if_head` for a run that ends in `continue` (the
  comparison with `js3_simplify_if` runs the same head on both sides
  and passed with `continue` removed from the rule); a hold of 10,000
  statements read through `statement_refs` and `take_run_rev`; a dead
  range of 10,000 slots crossed from its end; the number of merged
  guards at each size of the guard-chain test of `tail.rs`.
- `scripts/count_lowering_ids.py` stops with an error where it finds
  no file (from the repository root it printed zeros) and has a
  `--self-test`.

**Corrections after the review of this turn.** Made in place by the
reviewer's commit, or owed as said:

1. (i): `argument_values` is taken and given back in two functions of
   c1 only; the paragraph and step 1 of the probe prompt of T6x-c1 said
   it crossed three rows. Corrected in both places.
2. The prompt of T6x-b3b set `Instruction count` at most +0.02% as a
   gate. The default build does not reach the lowering, and b3a read
   +0.023% on code it cannot run: a limit the builder cannot control.
   Reworded to a report with a stop above the job's spread. The prompt
   listed the fragment as a fifth item of "four commits": it is part of
   commit 4.
3. (h) listed two lines of earlier sections as changed that this turn
   did not edit; each now says so.
4. `out.rs`: the cost note of `Runs::last` and the doc comment of
   `Slot::Dead` still described a slot-by-slot crossing; corrected. The
   invariant `Slot::DeadEnd` rests on is stated in its doc comment (no
   assertion checks it: a check would read the range it is there to
   skip).
5. `emit/builder.rs`, `S::value` gives nothing for a `switch`, where
   `JsStmt::value_of` gives the scrutinee. The builder makes no `switch`
   yet; the doc comment says who adds it.
6. The self-test of `scripts/count_lowering_ids.py` is run by the
   `script-tests` job (the reviewer's commit adds the step). It pins no
   count, by intent: it fails where the script finds no file or no
   call, not when a slice moves the number.
7. Owed by the design turn of T6v, which puts the builder behind the
   interface before T6s: the two reads of an id as a row that b3b
   leaves (`close::decide`, the `return` arm, until T6r; `finish`, the
   root, until T6s) are right on rows only. That the id is the row is
   a fact of `Rows`, not a promise of `Js::id` or `JsStmt::stmt_id`
   (on the builder the id is the `node_id` of an owned node). T6v says
   how its tests reach `finish` on the builder, or that they stop
   before it; if T6r leaves the `return` arm's turn-back in place,
   T6v's design owes the same for `decide`.
8. Owed by the next design turn, as tests: an allocation count around
   the reads of `a_statement_of_a_list_in_flight_is_read_where_it_is`
   (the doc comment of `with_stmt_at` says it allocates nothing, and no
   test would see an allocation); a `return` without a value among the
   shapes of `a_statement_reads_the_expression_it_evaluates_first`.
9. Accepted as it is: in `tail.rs` the test
   `a_block_wider_than_the_operand_stack_is_unblocked_without_growing_it`
   is renamed `a_body_wider_than_the_operand_stack_is_moved_without_growing_it`
   and its assertion message reworded; its condition is unchanged.

#### T6x-e and T6x-f: the fold reads where its rows are

Status: design, with the interface on trunk; T6x-e2 is built (pull
request 389). What the lowering's interface owes before the transition
functions can be deleted was decided from a probe that built it once
(draft pull request 383, not merged; its body is the report). The
functions this section adds are in `bir/lower/js.rs`, `js_stmt.rs` and
`out.rs` with their bodies on rows (`bir/j/rows.rs`, `rows_stmt.rs`) and
on the builder (`emit/builder.rs`). Decisions 1 to 12 are the eighth
design turn's; the ninth ("The ninth design turn: the fold built once",
below the corrections) built the remaining slices once in a throw-away
copy, replaced decision 5's deferred release (decision 13), corrected
decision 3 (decision 14) and wrote the prompts in 11.9 of the slices
whose build ran.

**What was measured.** A throw-away build (not pushed) wrote one line
per event of the export fold to a file: the rows of each unit that
reaches `build_rows`, each call of `substitute_after` with its number
of uses and the depth of each use below its row's statement, each read
of a binder in `alias_of`, each climb of `declared`, each removed row.
Run over the lowering's tests (`cargo test --lib bir::lower`) and, in
check mode (`RESCRIPT_BACKEND=check rescript clean` and `build`), over
`tests/tests`, the runtime and a 3,735-module application:

| Corpus | Units that reach the fold | With a top-level block | Calls of `substitute_after` | Reads of a binder in `alias_of` | Climbs of `declared` |
| --- | --- | --- | --- | --- | --- |
| the lowering's tests | 75 | 0 | 5, with 0, 0, 0, 1 and 10,000 uses | 0 | 0 |
| `tests/tests` | 1,148 | 0 | 0 | 0 | 0 |
| the runtime | 232 | 0 | 0 | 0 | 0 |
| the application | 3,979 | 0 | 0 | 0 | 0 |

Every use the tests replace lies two nodes below its row's statement
(the argument or callee of a call that is an expression statement):
9,997 of them were read. No unit of the three corpora removes a row,
dissolves a block or reads a declaration through a binder; the five
calls of the tests come from Lambda built by hand, not simplified (the
simplifier removes the alias the fold moves). The first run of the
tests wrote its lines in several writes and 4 of 10,161 were torn; the
figures above are from whole lines, and the corpora were run again
with one write a line.

A block statement at the top level does come from a source program,
though from none of the corpora: an untagged variant matched at the top
level with an arm that raises,

    @unboxed type u = A(array<int>) | B(dict<int>)
    @val external y: u = "y"
    switch y {
    | A(_) => throw(Not_found)
    | B(o) => Console.log(o)
    }

lowers to the guard and the other arm as two statements of one block
(`untagged.rs`, the arm `Op::Block` of the dispatch: `explicit_block`
over a run of more than one statement; `finish_untagged` unnests it only
under a `return`). `build_rows` then writes a row with `Row::BLOCK` and
one with `Row::NESTED` for each statement inside. The rows inside such
a block are guards, expression statements and assignments. A
declaration was not found there: a variable the export block reads is
bound by a `Let` of the unit's spine, `unit.rs` lowers each such `Let`
as a group of its own, and a group that declares writes `let x;` before
its block and assigns inside it. So "a removed row that stands in a
block" was reached by no program and no hand-built Lambda; it is not
argued impossible (decision 11).

**The rule.** No function of the interface takes an id in order to find
a node. An id is a key: compared, stored to say "the same node as",
read from a handle before the handle moves, or used to read a fact the
implementation keeps in a table indexed by it.

**Decisions.**

1. *A JSX element takes its callee apart.* `Js::jsx_element(a, callee,
   mark, info, has_children)`, as `call`, `new_` and `tagged` take
   theirs. One function in the end: T6x-e2 calls it from `compile_jsx`
   and deletes `Js::jsx` in the same pull request. It has a name of its
   own because `jsx` is taken until then, and a rename after the
   deletion would be a second edit of every call. On rows the callee is
   pushed and rotated below the operands since the mark
   (`slice::rotate_right(1)`): one move of 4 bytes an operand, then the
   list is written once. Not chosen: a slot reserved at the mark. The
   mark is taken through `&self`, a reserved slot needs a placeholder of
   the handle type, and the builder has no use for it: it moves the
   callee into the element and the operands off its stack. The builder
   has no JSX element: T6d owes the body (`emit/builder_program.rs`),
   which takes the callee as a handle beside the mark and moves nothing
   twice. Costs one step and one per operand, the callee counted; the
   test on rows reads 1,003 and 10,003 at 1,000 and 10,000 children.
   Probe site: `jsx.rs::compile_jsx` (commit cca7635c3 of the probe).

2. *A copy of a chain of member reads.* `Js::copy_members(a, r, made)`:
   the reads from `r` down to the first node that is not a `Dot`, and
   that node as a leaf, each with its cold data. Both callers copy down
   to exactly that node (`duplicate_jsx_key` stops its shape check at a
   reference, a module reference or a literal, and returns before any
   copy when a node above is not a `Dot` with a position;
   `copy_replacement` pushes while the kind is `Dot`), so the probe's
   removal of the proposed `depth` stands. `made` is given the id of
   each node made. That is a key under the rule: `export.rs` keeps
   `row_of`, a table indexed by id that remembers the row of an ancestor
   a site walk passed, and a node made in a slot rows had freed must not
   inherit what the slot held. It does not show that `row_of` is keyed
   by something an owning implementation cannot give: the builder gives
   ids that ascend and are never reused, so `made` clears entries that
   are already empty there. Not chosen: reading the ids off the copy
   afterwards (a second walk of a chain the first made). On rows the
   reads go above whatever the work stack `Rows::work` holds, because a
   substitution (decision 6) asks for a copy during its own walk; the
   test of that failed with the first body, which asserted an empty
   stack. One step a node made: 1,001 and 10,001 at 1,000 and 10,000
   reads, on rows and on the builder. Probe sites:
   `jsx.rs::duplicate_jsx_key`, `export.rs::copy_replacement`.

3. *The statements of a block the caller holds.* Four functions of
   `JsStmt`, each O(1): `block_len`; `with_block_stmt` (a read by
   reference, as `with_stmt_at` reads a list in flight);
   `lend_block_stmt` (the statement lent with the implementation and
   the pools); `take_block_stmt` (the statement moved out, a hole
   left). They are the probe's 3 to 6 under final names, and each is
   called by the probe's `export.rs`: `block_len` and the read by
   `add_row` and `with_row`, the lend by `has_toplevel_effect`
   (`effect_free` takes the implementation mutably) and by the copy of
   a nested row's value, the take by `coerced_list` for the statements
   of a block it dissolves. The read cannot be written with the lend:
   `same_reusable_value` reads the initialisers of two rows at once
   (`reusable_declared`), and two lends of statements the same stack
   holds cannot be alive together.

   *A hole.* On rows `Bir::detach` clears the parent link and leaves the
   entry in the block's list, so the indexes after it stay; the two
   readers and a second take panic on an entry whose parent is not the
   block. On the builder a block owns an arena vector of statements,
   which has no empty slot: the hole is an empty statement, which no
   constructor of the builder makes, so a hole is told from a statement
   and the later indexes stay. It costs one node of the arena for each
   statement taken. Not chosen: removing the element (every later index
   of the block would be wrong, or every later row rewritten); an
   `Option` in the vector (the vector is oxc's). What the final list
   does with a hole: nothing reaches it. A hole is made only where the
   fold has flattened the block (`substitute_after` sets `flattened`
   before any row is removed), and `coerced_list` then takes every
   statement that remains out of every block by its index and releases
   the blocks; a block with a hole is given to no list and no
   constructor, so no hole is printed. `Builder::release` (T6e) must
   skip an empty statement.

   *The handle of a nested statement on the builder.* A statement
   inside a block is the node alone; its row is in the table
   (`Builder::statement_row`). The builder's handle `S` carries the row
   beside the node, so a reference to a handle cannot be made for a
   statement inside a block. The builder's functions therefore give the
   node (`block_statement`, `block_statement_mut`), and this changes
   "T6: the interface" (a), the table of handles: for T6v, `B::S` on
   the builder is the oxc statement (16 bytes, where the table says
   `S<'a>`, 24), and a reader takes its row from the table, one load
   more a read. The statement stack then moves 16 bytes a statement.
   Not chosen: a block that keeps its statements as handles in the pool
   until a constructor consumes it. A block that came out of an `if`
   (`take_if`) is already an oxc vector, so two forms of block would
   exist and the read would work on one of them.

4. *The value of a statement in hand is copied with the expression
   half.* `JsStmt::value_of` gives a reference that borrows the
   statement and not the pools (its signature lost the lifetime on the
   pools; no caller changed). So `js.copy_members(a, js.value_of(a,
   s)?, ..)` and `js.copy_leaf(a, ..)` compile for a statement the
   stack, a block or the fold's tables hold, and the probe's
   `copy_value(s, cold, ..)` is dropped with its `bool`. On the builder
   `S::value` already borrows the statement only.

5. *The stack names places; nothing is taken out by one.*
   `StatementStack::placed_refs` gives each statement of a run with
   its place (a slot, or an index among the held statements with bit
   31 set), and `at_place` and `at_place_mut` read one. The probe's
   `take_place` and its change of `take_run` are not taken. Read
   against the invariant of `Slot::DeadEnd`: a slot whose statement is
   taken becomes `Dead(1)`, which every function accepts (`take` does
   the same). A held statement taken leaves `None` inside a hold whose
   span still counts it, and then `statement_refs`, `take_run_rev`,
   `slot_ref` (behind `first`, `first_single_slot`, `only`, `last`,
   `at`, `head`), `head_mut` and `take` of a hold of one panic on it,
   and `slot_len`, so `only` and `last_at`, count a statement that is
   not there. The functions that hand out statements and those that
   consume them would no longer accept the same set. So no emptied held
   entry is made. A removed row of the top level keeps its handle on
   the stack until `coerced_list` takes the run; the list's iterator is
   given it there in order, as today, and puts it with the dissolved
   blocks to be released after the list is made, where trunk dropped
   the handle unreleased. Ownership: the stack until `take_run`, then
   `coerced_list`, then `release_stmt`. No handle has two owners and
   none is dropped. A removed row inside a block is taken out by its
   index in the same pass that dissolves the block and released the
   same way. What this moves on rows: the release of a removed
   declaration happens when the list is made, not when the row is
   removed, so its initialiser's sites live through the rest of the
   fold. `mentions` must not count them: the row keeps its entry in
   `row_of` and `mentions` skips a site whose row is `REMOVED` (one
   test of bits it already loads). Not built in this turn (decision
   12).

6. *The replacement of a use (the probe's gap 2).*
   `JsStmt::substitute(a, s, var, uses, make)` replaces at most `uses`
   references to exactly `var` inside the statement `s`, which the
   caller holds at its row's place, each by what `make` gives, and stops
   at the last. The fold records, per later row that holds a use, how
   many it holds (`mentions` already finds the row of each site), and
   `Tables::later` holds rows and counts in place of site ids. On rows
   the body walks the statement on `Rows::work` and calls
   `Bir::replace`; on the builder it walks the nodes the builder makes
   with a work stack of the call.

   | Option | On rows | On the builder | Verdict |
   | --- | --- | --- | --- |
   | (i) a path of operand indexes recorded with the site, replaced along the path | the index of a node in its owner is a scan of the owner (a use in a call of n arguments costs n, n uses n squared) or a column written for every operand of every unit | the same column, 4 bytes a node, and a mutable step into operand i for every kind of node | not chosen: every unit pays for a path no unit of the corpora uses |
   | (ii) walk the statement at the row's place | one visit a node of each later row that holds a use, where trunk has one a use | the same | chosen |
   | (iii) not an edit: the variable keeps a declaration, or the fold decides before the uses are built | the moved declaration stands after its uses, so keeping it changes the program; deciding earlier needs the later rows, which do not exist yet | the same | not possible without changing the JavaScript |
   | (iv) an index from id to node on the owning side | nothing | per reference its slot, as a path from a statement, rewritten whenever the statement moves into a list | not chosen: a cost for every reference of every unit |

   The cost of (ii): one call is O(nodes of the statement up to its
   last use). k moved variables that each have a use in one statement
   of n nodes cost k times n, where trunk costs the uses: quadratic for
   a unit whose every export is a moved alias used in one large
   statement. The rows `Tables::later` names bound it (a row without a
   use is not walked) and the count stops a walk at the row's last use.
   On the corpora it is never run; the test of 10,000 references to one
   alias has one use a row and stays linear. The copies are made in the
   order of the walk, where trunk made them in the order of the sites;
   the nodes are the same. The steps on rows and on the builder are
   linear from 1,000 to 10,000 references and a reference behind n
   nodes costs n (tests on both). `Bir::replace` then has no call in
   `export.rs` after T6x-e4, and T6x-f's end state allows none.

7. *The declaration no row declares (the probe's gap 1).*
   `JsStmt::alias_at(a, id)` gives the variable a declaration binds its
   own to when its initialiser is a reference. `alias_of` reads nothing
   else of that statement (its kind, and the variable of its value).
   The id is the variable's binder, a key; on rows the body reads the
   row, on the builder a table of the declarations whose initialiser is
   a reference, pushed by `declare` in id order (8 bytes each, a binary
   search a read) and kept right by `substitute`. No unit and no test
   reaches the branch. Not chosen: a column by variable written by
   every declaration (a store a declaration for a read no unit makes);
   an index from id to node.

8. *The functions under "Reading by id".* They are served by keys on
   both sides and stay:

   | Function | Callers on trunk | Callers after T6x-e4 | On the builder |
   | --- | --- | --- | --- |
   | `Js::owner` | `declared`, `row_of`, `mentions` | the same | the column `owners` of "T6: the interface" (f), T6v |
   | `Js::kind_of` | `classify`, `declared`, `row_of` | `declared`, `row_of` (`classify` reads the row's statement) | the row table |
   | `Js::is_callee` | `mentions` | the same | a bit written with the owner, T6v |
   | `Js::id_bound` | `row_of` | the same | the length of the row table |
   | `JsStmt::alias_at` | none | `alias_of` | decision 7 |

   None hands a node out, so none breaks the rule; what they cost the
   builder is (f)'s column, one store an operand, for a walk
   (`mentions`) whose frequency this turn did not measure. T6v's design
   owes that measurement before it builds the column.

   The ids trunk hands to code a later slice owns are unchanged by this
   turn:

   | Place | The id | Removed by |
   | --- | --- | --- |
   | `names::adopt` (from `call.rs`) | the row of a node whose names are adopted | T6r |
   | `close::decide`, the `return` arm | the returned value, for `scope::return_sites` | T6r ("T6x-b" (c)) |
   | `finish` | the root block | T6s ("T6x-b" (b)) |

   Item 7 of the corrections of "T6x-b: an output's value, as built"
   stays T6v's; item 8 is paid here (decision 11).

9. *The eight calls in three test helpers.* T6x-f removes the
   transition functions from the two traits, so no generic code can
   name one, and keeps them as functions of `Rows` compiled for tests:
   the tests of `out.rs` (34 calls), `js_stmt_tests.rs` (12) and
   `js_tests.rs` (4) build rows on the arena and wrap them, and they are
   tests of rows. The three helpers are generic and go:
   `call.rs::call_node` (one use, an argument with an effect in the
   test `arity_groups_match_legacy`) becomes `call_values` over
   `out::of_row`; `cond.rs::empty_block` and `raw_if` (the hand of
   `if_statement_is_simplify_if_for_every_rule`) become two arms of that
   hand written on the arena, as its `throw` and `break` are. No test
   is deleted.

10. *The allocation counts.* `build_rows` reads a block's statements
    by recursion (`block_len`, `with_block_stmt`); it no longer pushes
    every statement of the top level through `Tables::path`. Two of the
    four counts of `unit.rs` then read one lower (switches 103 to 102,
    untagged 156 to 155: `path` is allocated by `row_of` in the other
    two units and by nothing in these). They move in T6x-e3, the slice
    that moves `build_rows`, with this reason in the test's comment.
    The recursion is as deep as blocks nest at the top level, one frame
    of `add_row` and one closure a level; a later read of a nested row
    costs one read a level. Not chosen: an explicit stack kept in the
    tables. A read of a row n blocks down would then start from the top
    each time, or the stack would hold references into blocks, which a
    table cannot keep. Not measured: the stack a unit of very deep
    blocks needs; the source program above makes one level, and an
    untagged match inside the arm of another makes one more (test of
    decision 11 at three).

11. *Tests added by this turn*, each seen to fail:

    | Test | What it is there for | Broken how |
    | --- | --- | --- |
    | `export.rs`, `a_block_of_the_top_level_is_read_and_kept_when_nothing_moves` | a unit with a top-level block through the whole lowering, against the legacy export code | the skip of a nested row removed from `coerced_list` |
    | `a_moved_alias_used_inside_a_block_dissolves_the_block`, `a_block_inside_a_block_is_dissolved_with_it` | a use inside a block replaced, one and two blocks down; the blocks dissolved | the detach of a nested statement removed |
    | `the_final_list_of_a_unit_that_dissolves_a_block_moves_each_statement_once` | `coerced_list` at 1,000 and 10,000 rows: rows walked, statements moved and interface steps grow by 9,000; the heap allocations (2) do not grow | a second visit of the rows added. It cannot see a scan that touches no counter |
    | `external.rs`, `ten_thousand_spliced_elements_and_pushed_arguments_have_linear_counts` | the spliced array and the push loop of a named external without arity at 1,000, 2,000 and 10,000 | either loop made to cost more as it goes |
    | `js_stmt_tests.rs`, `a_statement_of_a_list_in_flight_is_read_where_it_is` (edited) | no heap allocation around the read | not broken: the body is one indexed read |
    | `builder_tests.rs`, `a_return_without_a_value_reads_no_expression` | `S::value` of a `return` without one | the test is of a node the builder does not make |
    | `rows_tests.rs`, `a_release_and_a_leaf_leave_the_operand_stack_alone`; `builder_tests.rs`, `a_leaf_leaves_the_operand_stack_alone` | the sentence added to `Js::release` and the leaf constructors | the builder has no `release` until T6e |

    The Lambda of the three block tests is built by hand: an alias the
    simplifier would remove, around the untagged match of the source
    program above. A removed row inside a block has no test through the
    lowering (see "What was measured"); the take that would serve it is
    tested on rows and on the builder.

12. *The cut, and what was built.*

    | Slice | What | After | Built once in a throw-away copy |
    | --- | --- | --- | --- |
    | T6x-e2 | `jsx.rs` on `jsx_element` and `copy_members`; `Js::jsx` deleted; `State::external_values` stays for `ffi_args.rs` | this turn | yes: two commits, each with the three filters at 579, 71 and 40; clippy and `cargo doc` clean; transition calls 30 to 26; cost notes `changed/new=5; missing/generic=0`. Its prompt is in 11.9 |
    | T6x-e3 | `export.rs`, kinds 1 and 4: a row says where its statement is; reads go from there; a removed row is released when the list is made (decision 5); two allocation counts move (decision 10) | T6x-e2 | no |
    | T6x-e4 | `export.rs`, kinds 2 and 3 and the binder: positions in place of expression ids, `substitute`, `alias_at` | T6x-e3 | no |
    | T6x-f | the transition functions leave the two traits; test helpers as decision 9; `norm::jm14_push_effect_expression` compiled for tests (its five callers are tests of `norm_tests.rs` and `js_stmt_tests.rs`) | T6x-e4 | no |

    T6x-e3, e4 and f have no prompt yet: a prompt is written from a
    build that ran, and theirs did not run in this turn. What their
    design turn starts from: the probe's `export.rs` (commits
    861411754, 8f1a9c8e6, ed23e65e7) with the names of this section,
    without `take_place` and `copy_value`, and with decisions 5 and 6,
    which the probe did not build. No commit of the probe applies
    unchanged on this turn's head: each adds to the traits or to rows at
    the places this turn wrote (`git apply --check` of each of the nine
    fails in `rows.rs`, `rows_stmt.rs`, `js_stmt.rs` or `export.rs`).
    T6x-f no longer waits for T6r: `names.rs` and `globals.rs` call no
    transition function (the 30 calls are `export.rs` 18, `jsx.rs` 4
    and the helpers' 8).

**Corrections after the review of this turn** (the review of pull
request 388; items 1 to 3 are made in place, the others are owed by the
design turn that builds T6x-e3, e4 and f once and writes their prompts):

1. Made: the doc comments of `JsStmt::substitute`, `JsStmt::alias_at`
   and `StatementStack::placed_refs`, and of two tests of the builder,
   cited the decision before their own (5, 6 and 4 for 6, 7 and 5).
   Decision 9 counted 38 transition calls in the tests of `out.rs`;
   there are 34 (7 `from_node`, 5 `node`, 20 `stmt_from_node`, 2
   `stmt_node`). The one use of `call.rs::call_node` is in the test
   `arity_groups_match_legacy`.
   State: made in pull request 388; nothing owed.
2. Made: the doc comment of `JsStmt::substitute` says what the caller
   promises about an assigned variable. The two bodies differ on a
   reference that is the target of an assignment: rows replace it (it
   is a `Var` node, and a site on trunk), the builder passes it (an
   assignment target is not an expression there). The fold never asks
   (a declaration of `LetKind::Variable` is not moved, in either of the
   two functions that move one), so no test can tell; T6x-e4 checks the
   number `substitute` returns against the number of uses the fold
   recorded for the row, so that a difference stops the build instead
   of leaving a reference.
   State: the doc comment was made in pull request 388. The assertion is
   T6x-e4's: see the State line of item 5.
3. Made: the prompt of T6x-e2 names its changelog fragment and its
   search for `external_values` says what it prints.
   State: made in pull request 388; T6x-e2 is on trunk (pull request
   389).
4. Owed, decision 5 (the release of a removed row when the list is
   made). It is not final as written: it names one reader that sees the
   statement trunk had released (`mentions`), and there are others.
   - `define` reads `vars.binder(var)` of the variable it declares, and
     that variable can be the removed row's own: `move_reused_to_tail`
     removes the first declaration that carries the export's name and
     holds its value, and the arm after it tests `reused == export`, so
     the two can be one variable. On trunk `release_row` has released
     the declaration before `define` runs (`Bir::release` unbinds: the
     binder is none and the variable's fact is `Unknown`), so `define`
     binds the variable itself. With the release deferred the binder is
     still there and `define` would bind a copy: another variable in
     the exported tree.
   - The table `row_of` is filled at the first call of a unit and
     leaves out the rows removed before it. "The row keeps its entry"
     therefore holds only for a row removed after the fill. A site in a
     removed row of the top level filled later climbs to no row and is
     skipped, which is right by accident; a site in a removed row
     inside a block climbs to the block's row and is counted there.
   - What `Bir::release` does at that moment besides freeing nodes: it
     unbinds the declared variable and resets its fact, clears the
     owner of a function header, marks every site below as released,
     and runs `drain_dead`. Each needs its reader named or the sentence
     that none reads it between the removal and the list.
   The design turn builds T6x-e3 once and chooses, with the readers
   shown: (a) the removal unbinds and marks at once and only the
   handle's release waits; (b) a removed row that stands in a slot is
   taken at once (a slot left `Dead(1)` is accepted by every function
   of the stack; only an emptied HELD entry is not) and only a held one
   waits; or (c) as written, with every reader changed. A test in which
   a reused binding of the export's own variable moves is owed with it;
   if the lowering's tests have one already (they compare with the
   legacy export code), the build names it.
   State: paid in pull request 390 by decision 13 (the release is not
   deferred), with the test of the export's own variable (commit
   7f51ad14c) and `StatementStack::take_placed` (commit 4bc2aec19). The
   lowering's tests had no such unit.
5. Owed, decision 6. A test of `substitute` on a shape where the order
   of the walk and trunk's order of sites differ (uses at two depths,
   and inside a function literal), compared with trunk's replacement as
   the flat test is; the steps of a call that stops at `uses` with
   references left; and the debug assertion of item 2.
   State: owed by the ninth turn's build of T6x-e4 (L2 of pull request
   390); not reached when this line was written.
6. Owed, decision 3 and 5: a removed row that stands inside a block has
   no test through the lowering and no reason it cannot happen. The
   row of T6x-e3 owes one of the two.
   State: paid in pull request 390 by two tests through the lowering
   (commit 75470d61b): a removed row inside a block and a removed row
   that is held. Decision 13.
7. Owed, the builder (test-only until T6v; none blocks T6x-e2):
   `size_of` tests for `Property`, `Pending` and the alias entry;
   `reserve` reserves neither `members` nor `aliases`; `realias`
   removes from the middle of a vector (a shift of the entries after
   it) without a step test; an alias entry outlives the release of its
   declaration (T6e); and the push `declare` makes for every alias
   declaration is paid by every unit for a read no unit of the corpora
   makes, which T6v measures with the column of decision 8.
   State: still owed, by T6v. No build of the ninth turn needed one.
8. Owed, small: a debug assertion where a place is made that a slot
   index is below `StatementStack::HELD` (today a comment); the body of
   pull request 388 did not list three changes of built code that
   change no behaviour (`Rows::jsx` moved into `jsx_over`, the
   builder's `dot` onto `dot_row`, the constant `HELD`).
   State: the debug assertion is in `placed_refs` (commit 4bc2aec19).
   The three changes are recorded here; the merged body is not edited.
9. Not done by the turn: the probe prompt of T6r (K5).
   State: owed (L5 of the ninth turn, written only when L0 to L4 are
   complete).
10. Checked in the review beyond the turn's own runs: the source
    program of "What was measured", alone and with an alias used inside
    the match and exported, builds in check mode on trunk with no
    difference from the legacy backend and the JavaScript of the
    reference compiler. That shows the program is lowered alike, not
    which rows the fold writes for it: the block rows are known from
    the turn's instrumented build and from the three hand-built tests.
    State: a record; nothing owed.

**The ninth design turn: the fold built once** (pull request 390). The
turn converted `export.rs` in a throw-away copy, slice by slice, settled
what the review of the eighth turn left open on that build, and wrote
the prompts of the slices from the builds that ran (11.9). Seen first,
on trunk at 67070ede3d: `count_lowering_ids.py --self-test` 30
transition calls (26 once T6x-e2 was merged, 0b05ebef12); `--lib
bir::lower` 579 passed, `--lib bir::j` 71, `--lib emit::builder` 40;
the allocation counts of `unit.rs` 86, 103, 86, 156.

13. *A removed row is released at once, as on trunk* (replaces decision
    5 where it defers the release; what decision 5 says of
    `placed_refs`, `at_place` and `at_place_mut` and its refusal of an
    emptied held entry stand). When `substitute_after` has removed a
    row, `release_row` makes its holder give the statement up and
    releases it through the interface, at the moment trunk releases it:

    | Where the row stands | How it is given up | What is left |
    | --- | --- | --- |
    | a slot of the stack | `StatementStack::take_placed` | the slot `Dead(1)`, as `take` leaves one; the run gives nothing for it |
    | inside a block of the top level | `JsStmt::take_block_stmt`, the block reached with `at_place_mut` and one `lend_block_stmt` a level | a hole at its index (decision 3); the block is dissolved by `coerced_list` (`substitute_after` set `flattened` before the removal) |
    | a held statement of the stack | `take_placed` exchanges it for a stand-in | the stand-in in its entry, which the run gives in its place and `coerced_list` releases |

    *Why not deferred.* What `Bir::release` of a removed declaration
    changes, and who reads it before the final list is made:

    | What the release changes (`edit.rs`) | Readers between the removal and the list | With the release deferred |
    | --- | --- | --- |
    | the binder of the declared variable becomes none, its fact `Unknown` (`unbind`) | `define`, the first line (`vars.binder(var).is_some()`), when the variable it declares is the removed row's own: the arm `MovedReused` with `reused == export`. `declared`, `declared_now` and `alias_of` return before they read the binder for a variable a row declares (`decl[var] != 0`) | `define` binds a copy: a second variable in the exported tree. Seen: the test below fails, and only it (35 of the 36 tests of `export.rs` pass) |
    | each `Var` and module reference below is marked released in the site table, its occurrence and use counts fall (`register_kind`, `adjust_direct`) | `mentions` of the variable the initialiser reads (`let x = f` removed, then an export that asks about `f`): a later export's `move_alias_to_tail`, `move_reused_to_tail`, `is_recursive_function` | the site of a removed row counts as a later use and as a later initialiser, which blocks a move trunk makes, and `substitute_after` would replace a use inside a statement that is not printed |
    | the nodes are freed and their slots reused | `row_of` (a table by id), which `built` and `copy_members`' `made` clear for each node made | nothing, while the nodes live |
    | the entry of the statement in `row_of` is cleared (`release_row`) | `row_of` from a site below it | a site in a removed row inside a block would climb to the block's row (the review's second point) |
    | the owner of a function header is cleared (`unbind`) | none: a removed row's initialiser is a reference, a module member or a chain of static reads over one (`move_alias_to_tail` refuses the kinds `Other` and `Literal`; `reused_binding` accepts what `same_reusable_value` accepts), never a function literal |
    | `drain_dead` | none: it frees the value of a level-L `Let` only, and the lowering's arena holds none. The throw-away build counted its kills in an arena with a site table: 0 over the lowering's tests, the runtime and `tests/tests` |

    With the release where trunk has it, no row of this table has a
    reader that sees anything else than on trunk, and the table of
    readers a deferral would have to change is empty. `row_of` needs no
    entry for a removed row: nothing below it is live, so no site climbs
    to it; the fill leaves `REMOVED` rows out as on trunk.

    *The evidence.* `export.rs`,
    `a_reused_binding_of_the_exports_own_variable_moves_and_is_bound_again`:
    `let x = Other.f` with `x` exported as `Other.f`, with 0, 1 and 3
    later calls of `x`, through the whole lowering against the legacy
    export code. No source program was found for it: the simplifier
    substitutes an alias of a module member before the lowering, so the
    Lambda is built by hand, as that of the three block tests. With
    `release_row` deferred to `coerced_list` in the throw-away copy it
    fails on "a copy of the export's variable was declared" (two
    variables named `x`, one on trunk), while both printed texts still
    equal the legacy ones: a copy prints as its origin. So the test
    counts variables; the comparison of texts cannot see the
    difference.

    *The held case is real.* Instrumented, the throw-away build wrote
    one line a unit and one a removed row. The lowering's tests: 92
    units reach the fold, 19 rows removed, all in a slot. The runtime
    and `tests/tests` in check mode: 1,380 units (232 and 1,148), no row
    removed, 15 units with a held statement at the top level, one of
    them with a held declaration, none with a declaration inside a
    block. A held declaration at the top level is the temporary of an
    argument that is evaluated before a later one (`args.rs`,
    `evaluate_now`: `let tmp = value`, for a value that is not safe to
    delay; whether the fold can remove one of those was not examined).
    A declaration the fold does remove is held where a run is moved
    into a hold: the run of an argument of a static
    exit with more than one argument (`exit.rs::exit_child`,
    `hold_run`). Two tests through the whole lowering, against the
    legacy export code, remove such rows:
    `a_removed_row_that_is_held_is_released_and_the_hold_is_written`
    (`let x = Other.f` in the first argument of an exit with two) and
    `a_removed_row_inside_a_block_is_taken_out_of_the_block` (the same
    `let` in the arm of the untagged match of "What was measured"). Both
    pass on trunk and on the build of T6x-e3; item 6 of the corrections
    is paid by them.

    *The stand-in.* An empty block that is not explicit
    (`JsStmt::block_of` of a list of none). On rows one `SBlock` row and
    an empty list, made at the removal and released when the list is
    made: two steps and one. On an owning implementation one block node
    of the arena, which a bump arena does not give back before the unit
    ends: one node for each removed row that was held, none in the
    corpora. `take_placed(place, stand_in)` is O(1), one write; it
    counts no step and allocates nothing, and calls `stand_in` for a
    held statement only (test at 1,000 and 10,000 held statements).
    Read against `out.rs`: a slot left `Dead(1)` is what `take` and
    `drop_empty_blocks` leave, and `placed_refs`, `take_run`,
    `take_run_rev`, `slot_len`, `live`, `first`, `last_at`, `trim` and
    `kill` cross it as one dead slot; it is no `DeadEnd`, and nothing
    writes a statement into it. A hold keeps every entry, so the
    functions that hand out statements and those that consume them
    accept the same set (`statement_refs`, `slot_ref`, `head_mut`,
    `take`, `take_run`, `take_run_rev`: the test reads `first`, `last`,
    `only`, `has_statements`, `statement_refs`, `take_run` and
    `take_run_rev` after both kinds of take). No stand-in reaches the
    printed list: the only reader of the run after the fold is
    `coerced_list`, which takes the run in order, knows a removed row
    of the top level whose place has the `HELD` bit, and puts what the
    run gives for it with the dissolved blocks, released after the list
    is made.

    Not chosen: (i) unbinding and marking at the removal and releasing
    the handle later. It needs a function that retires a statement in
    place on both sides (on rows a release that keeps the root, and a
    husk the readers then have to refuse), for a state no reader needs.
    (iii) decision 5 as written, with `define`, `mentions` and `row_of`
    changed to test `REMOVED`: three readers changed and a statement
    kept alive for nothing. The probe's `take_place`, which empties a
    held entry, stays refused (decision 5).

14. *The final list stages the statements of a dissolved block*
    (corrects decision 3, which has `coerced_list` take each statement
    out of its block "by its index" while the list is written).
    `JsStmt::list` is given an iterator, and an iterator cannot borrow
    the implementation and the pools the list is being written with: a
    statement cannot be taken out of its block from inside it. So the
    first pass of `coerced_list`, which counts the list, also takes each
    statement of a dissolved block out (`take_block_stmt`; the block is
    reached with `at_place_mut`, or, a block inside a block, where it
    was staged) into `Tables::blocks`, and writes the index there into
    the row's place; the second pass moves it from there into the list.
    A block of the top level stays on the stack until the run is taken.
    Cost: a statement of a dissolved block is moved twice (trunk: a
    detach in place and one move); `blocks` is `Vec<Option<S>>` (8 bytes
    an entry on rows), reserved once for every row in a unit that is
    flattened and not touched in one that is not, so a unit that
    dissolves no block allocates what it did. Seen: the four counts of
    `unit.rs` read 86, 102, 86, 155 on the build (decision 10's two
    moved, the other two as they were), and
    `the_final_list_of_a_unit_that_dissolves_a_block_moves_each_statement_once`
    passes unchanged (2 allocations at 1,000 and at 10,000 rows). Not
    chosen: a `list` that hands its closure the implementation (on rows
    the list pool is borrowed while the list is written, so the body
    would buffer the statements itself); the probe's `take_place` of
    the block before the run is taken (decision 5).

**Changes to earlier sections**, each with its reason:

- "T6: the interface" (a): `jsx(a, mark, JsId, has_children)` becomes
  `jsx_element(a, callee, mark, JsId, has_children)` (decision 1); the
  read-back table gains `copy_members`; `JsStmt::value_of` borrows the
  statement only (decision 4); `B::S` on the builder is the oxc
  statement for T6v (decision 3).
- "T6x: the cut": the rows of T6x-e and T6x-f are rewritten for the cut
  of decision 12.
- `count_lowering_ids.py --self-test` prints 30 on this turn's head and
  26 after T6x-e2.

### 11.5 Worker prompt for T4b

Which form: it needs one experiment, because nothing read so far proves that
no rule of the lowering reads a list after it was copied in a way the
flatten pass would change (`nested_if`, `equal_statements`, `single_value`,
`simplify_if_head` in `bir/j/norm.rs` read copied lists). Commit 2 is that
experiment; its result selects the form, and the prompt says which result
selects which.

```text
Task T4b: the backend lowering applies the rules of the legacy flatten pass
(pass 1, apply_js_flatten_pass) where it copies a statement run to its list,
so that the new side of the `lower` gate stops running that pass. Repository:
compiler-rust/. Read first: docs/THREE_TREES.md 11.4 (finding 1 and the
re-cut table); docs/BACKEND_LOWERING.md 1.3, 7.2, 8.1;
src/lambda/js_pass_flatten_and_mark_dead.rs from `struct Flatten` to the end
of the file (flatten_block, Flatten::block_items, Flatten::statement,
flatten_sequence_statements, flatten_sequence_expressions);
src/bir/lower/out.rs (StatementStack::take_list); src/bir/j/norm.rs
(js1_exp, js2_block, je8_not, jm14_push_effect_expression, nested_if,
equal_statements, single_value, simplify_if_head); src/bir/shadow.rs
(prepare_lower, check_lower); finish_lowered_output and
compile_deps_program_with_lower_check in src/lambda/lam_compile.rs.

The rules, each from Flatten::statement, applied to one statement:
 R1 SExp of a JSeq: one statement per operand, left to right, each made by
    js1_exp and flattened again; the result goes through js2_block.
 R2 SExp of a JBlockLit: one statement per field, the same way.
 R3 SExp of a JCond: each branch whose value has an effect becomes
    [flatten(js1_exp(branch))]; both empty: the test as SExp, or an empty
    SBlock when the test is pure; only the else branch: SIf(je8_not(test),
    else, []); otherwise SIf(test, then, else). The statement's location is
    the conditional expression's.
 R4 SExp of an assignment whose right side is a JSeq: the operands before
    the last as R1, then the assignment of the last operand.
 R5 SReturn of a JCond: SIf(test, [flatten(return then)], [flatten(return
    else)]), location as R3.
 R6 SReturn of a JSeq: the operands before the last as R1, then the return
    of the last, through js2_block.
 R7 An SBlock of exactly one statement is that statement, flattened.
 R8 In a list, the statements of an SBlock take the SBlock's place.
Every other statement is left as it is: its nested lists were flattened when
they were copied.

Do exactly this, one commit each, in this order, each pushed when made:
1. src/bir/j/flatten.rs: `pub(crate) fn flatten_into(bir, statement, out:
   &mut Vec<NodeId>)` implementing R1 to R8 with an explicit work stack kept
   in a struct the caller owns (no recursion, no Vec created per statement).
   Its doc comment states the cost: one step per statement it writes plus
   one per operand of a flattened sequence. Unit tests in
   src/bir/j/flatten_tests.rs, one per rule, in the oracle form: build the
   statement in a JsArena and in a Bir, run Flatten on the first and
   flatten_into on the second, export the second with bridge_j::export_js,
   compare the two printed texts. Nothing calls flatten_into yet outside
   tests in this commit only; commit 2 follows in the same pull request.
2. The experiment. StatementStack::take_list calls flatten_into for each
   statement it copies (the scratch vector lives in StatementStack). In
   compile_deps_program_with_lower_check the new side's
   finish_lowered_output skips apply_js_flatten_pass (a const generic or a
   bool parameter; the legacy side and the default path keep all six
   passes). Run scripts/test_backend_coverage.py and RESCRIPT_BACKEND=check
   on the 3,735-module application. Also add to check_lower a comparison of
   the new side's `built` count of every variable with the count
   js_pass_tailcall_inline::UseCounts gives on the legacy side after passes
   1 and 2, as an error naming the unit and the variable.
   RESULT A: every unit of the three corpora and of the application is
   identical and no count differs. Continue with commit 3.
   RESULT B: a unit differs or a count differs. Do not try to repair it by
   changing a rule of norm.rs or by flattening later. Reduce the first
   differing unit to the smallest Lambda, add it to
   src/bir/lower/oracle_tests.rs as a test that asserts both texts (the form
   of block_substitution_and_dead_removal_do_not_commute_with_tailcall_
   inlining), revert the call in take_list and the skipped pass, keep
   flatten.rs out of the tree (delete it: nothing may be dormant), keep the
   count comparison if it passes, write under 11.4 which reader of a copied
   list saw the changed shape, and stop. T4c then reads sites through the
   reshaping (finding 1) and pass 1 stays until T6.
3. Only after RESULT A. Rule tests in src/bir/lower/oracle_tests.rs, in the
   oracle form (the same Lambda through the legacy pipeline with all six
   passes and through the new one without pass 1, texts compared), one per
   reader of a copied list with a statement of R1 to R7 inside the list it
   reads: nested_if, equal_statements, single_value, simplify_if_head. A
   failing one is RESULT B.
4. Step-count and allocation tests: a run of 10,000 statements of which
   half match R1 with two operands is copied in at most 25,000 steps of
   flatten_into's counter; a sequence of 10,000 operands in one statement
   in at most 10,001; a returned conditional nested 10,000 deep in its else
   branch without recursion (it must not overflow the stack); a zero
   allocation test in the form of src/bir/j/norm_tests.rs for a run that
   needs no rule; size_of of the work-stack entry pinned (at most 16 bytes).
5. tests/backend_coverage.txt if a count improved; docs/STATUS.md (a row
   T4b); docs/THREE_TREES.md 11.4 (the re-cut table: T4b done, which form);
   changes/lowering-flatten.internal.md, one line starting with "- ".

End state, to paste in the pull request with the output:
- `rg -n 'apply_js_flatten_pass' compiler-rust/src/lambda/lam_compile.rs`
  shows it skipped for the new side only.
- `rg -n 'lam_compile|js_exp_make|js_ir::build|js_pass_' compiler-rust/src/
  bir/j/flatten.rs` is empty.
- scripts/test_backend_coverage.py passes, stage `lower` unchanged or better
  in every corpus, no new Unsupported reason; the application: no
  difference in any unit.
- cargo test for compiler-rust; the CI instruction count within +0.02% (the
  default path is untouched); check-mode instructions on tests/tests before
  and after.

Shortcuts that count as failure: flattening in a pass over the finished unit
or a finished function body instead of at the copy; calling the legacy
Flatten from bir/; a hash map; a Vec, Box or String per statement; weakening
or deleting a test; adding an Unsupported reason; changing a rule of
norm.rs so that a unit passes; leaving flatten.rs in the tree unused.

When a unit differs: print both texts for that unit (the error of
check_lower names the first differing line), find the statement, and decide
only between "a rule R1 to R8 is implemented wrongly" (fix it, add the rule
test) and RESULT B. If you cannot tell which within the unit, it is RESULT
B: report the unit and the line.
```

### 11.6 Worker prompt for T4g

To be issued when T5 and T6 are merged, not before ("T4c design"). It takes
over what T4c could not do. Two things in it come from what T4c measured and
are not in "The design": a list is copied more than once, so the splice
needs a close that happens once; and a function copied after its runs closed
has variables whose count is split over the copies.

```text
Task T4g: the backend lowering splices a function at its single tail call
(step A of docs/THREE_TREES.md 11.4), so that the new side of the `lower`
gate stops running the legacy pass apply_js_tailcall_inline_pass.
Repository: compiler-rust/. Preconditions, check them first and stop with a
report if one fails: `rg -n 'apply_js_flatten_pass|apply_external_shadow_
pass' src/lambda/lam_compile.rs` shows both skipped for the new side (T6 and
T5 are in); `shadow::compare_decisions` reports no count, status or site
difference on the runtime, tests/tests and the application.

Read first: docs/THREE_TREES.md 1.1, 1.5 and all of 11.4 ("The design",
"T4c design" with its two counterexamples, the two count hazards, "as built
and measured", the order table); src/lambda/js_pass_tailcall_inline.rs whole
(statuses, try_inline_single_return_statement including the function literal
called in place, inline_named_call and active_decls, immutable_param_mask,
inline_tailcall_call, is_substitutable_constant, substituted_truth,
SubstituteInline and its shadowing rules); src/bir/lower/close.rs,
scope.rs (Uses, VarFacts, Decision, return_sites), out.rs (take_list),
export.rs (the top-level close); src/bir/j/logic.rs (copy_j); src/bir/
shadow.rs (compare_decisions, check_lower); the tests named in the order
table.

What exists: close::decide gives every declaration of a copied list its
status from `built` and return_sites records the site of a callee. A
declaration is decided once per copy of its statement (the last decision
stands), so a list being copied is not "the scope closing".

Do exactly this, one commit each, in this order, each pushed when made:
1. Design, in 11.4 under "T4g as built", before any code. Answer: (a) where
   the splice happens so that it happens once per declaration and after
   every use of the callee is lowered: the copy of a function body's list
   and the top-level list after coercion are the candidates; say how the
   decisions of the lists inside that body are found without walking it (a
   mark in `Scope::decisions` at function entry is the suggestion; it is not
   tested); (b) with P1 gone, what a site is: state it on the statements
   the lowering now writes and delete return_sites if the last statement of
   a list is all that remains; (c) copy_j: either the copy keeps one count
   per origin, or a function that holds a candidate is never copied after
   its body closed, or a copied candidate is not spliced; choose one, and
   turn a_copied_function_doubles_the_legacy_count_of_the_variables_
   declared_inside_it into a test of the final text; (d) the function
   literal called in place (no status, arity rule only).
2. VarFacts grows to 16 bytes: the declaration's statement node, the site,
   the head of the read sites, state bits. The late mark (a bit of a leaf's
   aux) on every node a scope-close decision creates.
3. The splice with the legacy rules: arity equal or no splice; a parameter
   never assigned in the body is renamed to an argument that is a variable,
   replaced by a substitutable constant, otherwise declared `let p = arg`
   (kind Variable); a conditional or a negation on a parameter replaced by a
   boolean or integer constant keeps one branch; shadowing by an inner
   declaration, parameter, loop or catch variable ends the substitution for
   that name. The callee's statements take the place of the `return`; the
   declaration becomes dead and pure. Late zero: a decrement that brings
   `remaining` of a variable of a closed run to zero marks its declaration
   through VarFacts. Graves: occurrences a decision removes are logged
   against the anchoring variable and subtracted from `built` when a later
   release reaches the anchor. The new side skips
   apply_js_tailcall_inline_pass; compare_decisions and
   js_pass_tailcall_inline::decisions are deleted (one path).
4. Rule tests in src/bir/lower/oracle_tests.rs in the oracle form (the same
   Lambda through the legacy pipeline with all passes and through the new
   one, texts compared): a function inlined at its single tail call; the
   call in a branch of a returned conditional and as the last operand of a
   returned sequence; count two; a count that becomes one only after a
   later pass; `pair[0](2)`; fewer, equal, more arguments; a parameter
   replaced by a variable, by a constant, declared, never read, assigned; a
   method, `async`, a directive; late zero (finding 3); a dead block binding
   (finding 5); an exported function; a candidate used inside its own
   initialiser; the two T4c counterexamples and the two count hazards, now
   with equal texts.
5. Step-count tests at 10,000: a run of 10,000 declarations of which half
   are single-use functions with a tail-call site (state the bound per
   declaration and assert it); 10,000 nested scopes each inlining into the
   next, without recursion on the native stack; a body inlined once is
   rewritten once. A zero-allocation test with warm pools in the form of
   src/bir/j/norm_tests.rs. size_of pinned: VarFacts 16, Uses 8, a read
   site 8. The counter in the lower report: sites spliced, and of those the
   number whose callee's level L use count is not one.
6. docs/STATUS.md (row T4g), the re-cut table, tests/backend_coverage.txt
   if a count improved, changes/lowering-tail-call-splice.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'apply_js_tailcall_inline_pass' src/lambda/lam_compile.rs src/bir`
  shows it skipped for the new side only.
- `rg -n 'lam_compile|js_exp_make|js_ir::build|js_pass_' src/bir/lower
  src/bir/j` matches only inside #[cfg(test)] modules.
- scripts/test_backend_coverage.py passes with stage `lower` unchanged in
  every corpus; RESCRIPT_BACKEND=check on the application: no difference in
  any unit.
- cargo test for compiler-rust; the CI instruction count within +0.02%;
  check-mode instructions on tests/tests before and after (one pass fewer:
  it should fall).

Shortcuts that count as failure: splicing where a list is copied instead of
at a close that happens once; finding a site or a parameter's occurrences by
walking a body that is not being inlined; a hash map keyed by a variable or
a node; a Vec, Box or String per declaration or per site; an Unsupported
reason; a weakened test; the legacy pass called from bir/ outside tests.

When a unit differs: reduce it to the smallest Lambda and decide only
between "a rule of the splice is implemented wrongly" (fix it, add the rule
test) and "another legacy pass reads what the splice changed" (commit the
Lambda as a test asserting both texts, keep the pass on the new side, write
which pass under 11.4, stop).
```

### 11.7 Build prompt for T5

Superseded for part B by the prompts of 11.4, "T5 part B as redesigned"
(f): the skeleton this prompt names was replaced. Kept as the record of
what was issued.

Part A of T5 is built ("T5 as built"). Part B is a skeleton: types, sizes,
signatures with their costs, and ignored acceptance tests. Verbatim prompt
for the builder:

> Task: build part B of T5 of `compiler-rust/docs/THREE_TREES.md` (the
> naming log) and close part A's open measurements. Read first: AGENTS.md;
> THREE_TREES section 2; 11.4 "T5 design" (e) and "T5 as built"; the header
> of `emit/naming.rs`; `bir/lower/names.rs` (the skeleton);
> `bir/lower/globals.rs` (how part A records nothing new and decides at
> `State::finish`); `bir/shadow.rs` and `lam_compile.rs` (the gate).
>
> Decided, not yours to change: the events (`Declare`, `Params`, `Enter`,
> `Leave`, `Binder`; a reference is no event), the free-variable list with
> one membership bit per variable, filled where a reference is built and
> finalised at `Log::leave`; the replay through the existing `Names`
> tables; the oracle is `Names::collect` run on the lowering's own program
> before the JS passes (the passes still change which statements exist, so
> the final program is not what the log describes), with its module list
> filled in; part A's decision point, bit and bridge.
>
> Commits, in order, each building without warnings
> (`cargo clippy --all-targets -- -D warnings`) and passing
> `cargo test --lib bir::` and `emit::`:
>
> 1. `Log::declare`, `binder`, `reference`, `enter`, `leave`
>    (`bir/lower/names.rs`). Turns on nothing yet (the tests also need the
>    replay); add no test of your own in place of the ignored ones.
> 2. `emit::naming::replay`. Turns on, in `bir/lower/names.rs`:
>    `a_local_takes_the_name_of_an_outer_variable_the_function_does_not_capture`,
>    `a_removed_declaration_takes_its_event_with_it`,
>    `two_variables_first_named_by_one_reservation_are_named_in_order`,
>    `a_loop_variable_is_named_before_the_declarations_of_its_body`,
>    `ten_thousand_declarations_are_logged_and_replayed_in_one_step_each`,
>    `ten_thousand_nested_functions_cost_a_constant_number_of_steps_each`.
> 3. `emit::naming::compare_with_pass`. Turns on
>    `the_comparison_counts_a_name_the_replay_gets_wrong`
>    (`emit/naming.rs`).
> 4. The lowering logs: remove `cfg(test)` from `mod names`, `replay`,
>    `compare_with_pass` and their types; a `Log` on `lower::scope::Scope`;
>    `reference` from `Bir::allocate` beside `Scope::site`; `declare` where
>    an `SDecl` is written, `binder` where loop and `try` statements are
>    built, `enter`/`leave` around a function body (K10,
>    `with_function_scope`). Add one oracle-form test per event kind in
>    `bir/lower/oracle_tests.rs`: Lambda lowered, the log replayed, the
>    table compared with `compare_with_pass` on the exported program, zero
>    differences; and the three hard examples of section 2 as Lambda.
> 5. Check mode: after `prepare_lower`, replay and `compare_with_pass` on
>    `new_before` with its modules filled in
>    (`collect_modules_from_js_block`); `NameStats` flattened into the
>    `lower` report; a difference is an error naming the unit and the
>    identifier. The printer shape tests the pass applies
>    (`walk::prints_declaration`, `omitted_expression`, `else_omitted`,
>    `tail_effect`, the eta form of `function_form`) are bits you add to
>    the event where the statement is written or tests at replay: say
>    which, per test, in "T5 as built: part B".
> 6. Part A leftovers: a test for the hazard of "T5 design" (a) (a module
>    of a global's printed name whose only reference stands in a pure
>    branch of a conditional statement: assert both complete texts, as the
>    T4c hazards are pinned); a rule test for `SForRangeExisting`.
> 7. Measurements and documents: instruction counts of a clean build of
>    `tests/tests` (release binary, `RAYON_NUM_THREADS=1`, cachegrind as
>    `scripts/compare_build_instructions.py` does) with
>    `RESCRIPT_BACKEND=check` and by default, at `be1b3a482e`, at this
>    skeleton's head and at your head; "T5 as built: part B"; STATUS.md row
>    T5; the worker prompt for T6 in the form of 11.6.
>
> End state, checkable: `rg -n 'fn replay' compiler-rust/src/emit/naming.rs`
> has one hit; `rg -n 'cfg\(test\)' compiler-rust/src/bir/lower/names.rs`
> shows the test module only; `rg -n 'T5 build' compiler-rust/src` is
> empty; `rg -n 'apply_external_shadow_pass'
> compiler-rust/src/lambda/lam_compile.rs compiler-rust/src/bir/shadow.rs`
> still shows the legacy side only; `name_differences` is zero on every
> unit the pass supports in the runtime library, tests/tests, the fixtures
> and the application, with the number of supported units per corpus
> reported; `scripts/test_backend_coverage.py` passes with the ratchet
> unchanged or risen; the default build's instruction count is within
> noise.
>
> Shortcuts that count as failure: changing a signature, a doc-comment
> cost, a pinned size or a test of the skeleton instead of meeting it (if
> one cannot be met, stop and report the function and the reason); a walk
> over a statement body or a finished tree to find references, bindings or
> free variables; a hash map keyed by a variable, node or scope in the log
> (the `Names` tables stay as they are: they are the pass's, and the pass
> is not removed in this slice); an `allow` attribute; an ignored test
> other than the ones named above before their commit; a number you did
> not measure.

### 11.8 Worker prompt for T6

Superseded by 11.9 and by 11.4, "T6 design": not to be issued. Kept as
written, as the record of what the design turn was asked.

Written by the builder of T5 part B. Reviewed in 11.4, "T5 part B as
redesigned" (g): each paragraph is kept or corrected there; issue it with
those corrections. T6 starts from a design turn.

To be issued when T5 is complete, not before: the builder prints names from
the table T5's replay fills, and part B stopped at its step 4 ("T5 as
built: part B", two design gaps). It follows T4's statements on what the
new side still runs (the flatten pass stays until this slice, "T4b").

```text
Task T6: the builder over oxc nodes (docs/THREE_TREES.md section 3): the
backend lowering writes the JavaScript tree as oxc nodes through a thin
builder of our own, and RESCRIPT_BACKEND=new prints from it. Repository:
compiler-rust/. Preconditions, check them first and stop with a report if
one fails: `rg -n 'cfg\(test\)' src/bir/lower/names.rs` shows the test
module only and check mode reports name_differences 0 on the runtime,
tests/tests, the fixtures and the application (T5 is complete); `rg -n
'apply_external_shadow_pass' src/lambda/lam_compile.rs src/bir/shadow.rs`
shows the legacy side only.

Read first: docs/THREE_TREES.md sections 2, 3 and 7, all of 11.4 (T4b's
RESULT B, "T5 design", both "T5 as built" parts); the header of
src/emit/naming.rs; src/emit/build.rs and src/emit/walk.rs (the printer
decisions the oxc path takes today, from the JS IR); src/bir/j/ whole (the
constructors of rows J-E1 to J-E10, J-S1 to J-S5 and J-M0 to J-M13 of
BACKEND_LOWERING 6); src/bir/bridge_j.rs (deleted by this slice) and the J
opcodes of src/bir/node.rs; src/bir/lower/out.rs; the gate in
src/lambda/lam_compile.rs and src/bir/shadow.rs; in oxc 0.158,
`Expression`, `oxc_allocator::Box`, the `node_id` cell, and
`Codegen::with_scoping`.

Do exactly this, one commit each, in this order, each pushed when made:
1. Design, in 11.4 under "T6 design", before any code. Answer: (a) the
   handle a constructor takes and returns (the oxc `Expression` by value,
   its flags, a J kind tag; its size, at most 24 bytes, and why) and the
   facts table indexed by `node_id` (2 bytes a node; the side pool for
   block shapes, call information and `undefined`); (b) per row of J-E,
   J-S and J-M, what it reads of a child and how it reads it from the
   handle or the table; (c) where each printer decision of
   BACKEND_REDESIGN A.7 is taken: when the node is attached, or when the
   function's scope closes (unit return, eta form, arrow or `function`);
   (d) identifiers: the symbol id a binding and a reference carry, how ids
   are allocated, and how the name table of T5's replay reaches
   oxc_codegen; (e) each rule of the flatten pass (`Flatten` in
   js_pass_flatten_and_mark_dead.rs) that the builder now applies where it
   writes a statement, with the T4b result for the copied-branch reader.
2. src/emit/builder.rs: the handle and the facts table with size_of
   pinned; the leaf and expression constructors, each with its cost in its
   doc comment.
3. The statement and block constructors, and the flatten rules of 1(e).
4. bir::j writes through the builder; bir/lower changes types only;
   RESCRIPT_BACKEND=new prints the builder's program; check mode compares
   that text with the legacy text on every supported unit.
5. Delete src/bir/bridge_j.rs, the J opcodes of src/bir/node.rs and the
   Bir view of src/emit/walk.rs (one path); the new side runs no flatten
   pass.
6. Rule tests in the oracle form for every row of 1(b) and every flatten
   rule of 1(e); step-count tests at 10,000 for a long statement list, a
   deep expression and a long string concatenation; a zero-allocation test
   with a warm allocator in the form of src/bir/j/norm_tests.rs.
7. docs/STATUS.md (row T6), tests/backend_coverage.txt if a count
   improved, changes/lowering-oxc-builder.internal.md.

End state, to paste in the pull request with the output:
- `rg 'JSeq|JBlockLit' src/bir/node.rs` is empty; `rg bridge_j src` is
  empty; `rg -n 'apply_js_flatten_pass' src/lambda/lam_compile.rs` shows
  the legacy side only.
- The reformat-and-compare suites pass; RESCRIPT_BACKEND=check: no text
  difference in any supported unit of the four corpora, with the number
  of supported units per corpus reported; scripts/test_backend_coverage.py
  passes with the ratchet unchanged or risen.
- Instruction counts of a clean build of tests/tests (release binary,
  RAYON_NUM_THREADS=1, cachegrind as scripts/compare_build_instructions.py
  does): RESCRIPT_BACKEND=new below the default; the default within the
  CI threshold.

Shortcuts that count as failure: a JS IR built and converted to oxc
nodes; a pass over the finished oxc tree for a fact the builder could
have recorded when it attached the node; a hash map keyed by a node, a
variable or a symbol; a Vec, Box or String per node outside the oxc
allocator; an Unsupported reason added to make a unit pass; a weakened or
ignored test; bridge_j kept as a fallback.

When a unit differs: reduce it to the smallest Lambda and decide only
between "a builder rule is implemented wrongly" (fix it, add the rule
test) and "a legacy pass reads what the builder changed" (commit the
Lambda as a test asserting both texts, write which pass under 11.4,
stop).
```

### 11.9 Build prompts for T6

Supersedes 11.8. The design is 11.4, "T6 design" and "T6: the cut". One
prompt per slice, issued verbatim; a slice without a prompt here is not
ready to issue (its skeleton and tests come from a design turn). The
skeleton names (`Builder::statements_of`, `Mark`) are those of
`emit/builder.rs` as committed with this section.

Common to every T6 prompt (part of each):

```text
Repository: compiler-rust/. Read first: AGENTS.md; docs/THREE_TREES.md
section 3 and 11.4 "T6 design" (all of it) and "T6: the cut";
src/emit/builder.rs and src/emit/builder_tests.rs whole.

You build bodies. You change no signature, no doc-comment cost, no pinned
size, no flag of the table in the header of builder.rs, and no test. If
one cannot be met, stop: commit what passes, and report the function, the
test, and the smallest input that shows it. Adding a private helper or a
private field, and the layout of the code, are yours; say what you added
in the commit message, with its cost in its doc comment.

Counts as failure: an `allow` attribute; a hash map or set; a Vec, Box,
String or format! per node, per operand or per statement (the builder's
own vectors grow, and only through `reserve` and `reserve_statements` in a
warm unit); a walk over an expression or a statement list other than the
loop over the operands or statements a function is given; a rule of
BACKEND_LOWERING 6 applied in a constructor (a constructor builds the
node it is asked for); a second place that computes a flag; an ignored
test other than those of a later slice; a number you did not measure;
`unsafe`.

A step bound in a test is a relation between two sizes. If the body that
meets the doc comment's cost fails one, do not adjust the body to the
test or the test to the body: report the two measured counts and stop.

Every commit: `cargo check --all-targets --manifest-path
compiler-rust/Cargo.toml` and `cargo clippy --all-targets --manifest-path
compiler-rust/Cargo.toml` print no warning; `cargo test --manifest-path
compiler-rust/Cargo.toml --lib emit::builder` passes. Never run the whole
test suite: a checkout without the built runtime fails tests that have
nothing to do with this slice (for one, `emit::oracle_tests::remaining_
expressions_source_oracle`); CI judges those. Push after every commit.
Changelog: a fragment under changes/ ending in `.internal.md`, one line
starting with "- ".

When a test of the oracle form fails: the two texts are in the message.
Reduce to the smallest description (`T` or `St` in builder_tests.rs) and
decide only between "the body is wrong" (fix it) and "the legacy printer
does something the design does not say" (do not change the test: report
the description and both texts, and stop).
```

T6a:

```text
Task T6a: the bodies marked todo!("T6a") in src/emit/builder.rs: the
leaves and the expression constructors of the builder over oxc nodes.
Nothing outside src/emit/builder.rs, src/emit/builder_tests.rs (removing
ignore attributes only) and the changelog fragment changes.

What exists: the types, `Builder::new`, `clear`, `nodes`, `mark`,
`stage_mark`, and 14 tests ignored as "T6a build". The module is compiled
for tests only (`#[cfg(test)] mod builder` in src/emit/mod.rs): leave that.

How a node gets its facts: every constructor builds the oxc node, gives
it the next `node_id` (the index its row will have in `rows`; entry 0 is
unused), pushes the row, adds one to `steps`, and returns the node with
the same row. The flags of each kind are the table in the header of
builder.rs; `aux` and `payload` of each kind are in the doc comments of
`Kind`. The printer's spellings are those of src/emit/build.rs today,
which you read and do not change: `Build::number` (a float through
`normalize_float_literal_for_js`; `NaN` and `Infinity` as identifiers; a
negative number as a negation of its absolute value; a bigint that is not
decimal is Unsupported("non-decimal bigint")), `Build::string`
(`literal::arena_string`), `Build::member` (`walk::member_form`,
`walk::numeric_member`), `Build::bin` (the operator table;
`walk::negation_form`; `walk::nullish_target`, whose two outcomes are a
loose comparison with `null` and Unsupported("nullish comparison target
equality"); an assignment's target is a member, a computed member or an
identifier, else Unsupported("assignment target"); `BinOp::Bnot` is
Unsupported("binary bitwise-not")). `&&` and `||` are logical
expressions, as given: do not rebuild a chain.

Do exactly this, one commit each, in this order, each pushed when made:
1. `reserve`, `row`, `reference`, `named`, `undefined`, `null`, `boolean`,
   `string`, `int`, `number`. Remove the ignore from
   `leaves_print_as_the_legacy_printer_prints_them`: it passes.
2. `not`, `bnot`, `typeof_`, `is_nullish`, `in_`, `str_append`, `bin`,
   `cond`, `seq`, `dot`, `length`, `index`, `push`, `call`, `new_`. Remove
   the ignore from the other 13 tests: they pass.
3. The changelog fragment changes/builder-expressions.internal.md.

Relations to hold (asserted by the tests): steps and nodes are exactly
linear between 1,000 and 10,000 elements for a wide call, a deep member
chain under negations and a long concatenation; steps are at least the
nodes and at most twice the nodes; a warm builder (arena with capacity,
`reserve` called) performs no heap allocation for 10,000 calls and a
chain of 10,000.

End state, to paste in the pull request with the output:
- `rg -c 'todo!\("T6a"\)' src/emit/builder.rs` prints nothing (no match).
- `rg -n 'T6a build' src` is empty; `rg -c 'T6b build' src/emit/
  builder_tests.rs` prints 7.
- `rg -n 'mod builder' -B1 src/emit/mod.rs` shows `#[cfg(test)]`.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  emit::builder`: 18 passed, 7 ignored.
- The CI job `Instruction count` within +0.02% (the release binary does
  not contain the module).

Shortcuts that count as failure, beside the common list: taking a flag
from the oxc node instead of the operand's row; reading the table for an
operand that is in a handle; a `match` on the oxc node where the row's
kind answers; building an argument list in a Vec and copying it (drain the
operand stack into an arena vector of the exact length); printing a
variable's name into the node (`reference` writes no text: the reference
id is the variable's index).
```

T6b:

```text
Task T6b: the bodies marked todo!("T6b") in src/emit/builder.rs:
statements and statement lists of the builder over oxc nodes.
Precondition, check it first and stop with a report if it fails:
`rg -c 'todo!\("T6a"\)' src/emit/builder.rs` prints nothing and `cargo
test --manifest-path compiler-rust/Cargo.toml --lib emit::builder` shows
18 passed. Nothing outside src/emit/builder.rs, src/emit/builder_tests.rs
(removing ignore attributes only) and the changelog fragment changes.

What a statement in flight is: the oxc statement in the form the
lowering's rules read, not the print form. A `return` always has its
value, `undefined` too. An `if` always has two block statements, an empty
one too. A declaration always has the value it was given. A `while` is
one statement (the legacy printer writes a `;` after it: that, a dropped
`else`, an omitted declaration and a block's braces are the seal's, T6e,
and not yours). A statement's row has the kind, `HAS_FUN` and `SEAL` of
what it holds (its expression and its lists) and no other flag; a
declaration's `payload` is the variable's index and its `aux` the kind
given. A declaration's binder is a binding identifier without text whose
symbol id is the variable's index.

What a list in flight is: the caller takes `stage_mark`, stages
statements, and `list` moves the statements staged since the mark into a
run of `pool` and returns the run. Lists nest: a list finished while
another is being staged takes only its own statements. A statement is
taken out of a list at most once (`take`, and the constructors that
consume a list); reading or taking it again panics with "a statement
taken twice".

Do exactly this, one commit each, in this order, each pushed when made:
1. Every body marked todo!("T6b"). Remove the ignore from the 7 tests of
   `emit::builder::tests::statements`: they pass.
2. The changelog fragment changes/builder-statements.internal.md.

Relations to hold (asserted by the tests): steps and nodes are exactly
linear between 1,000 and 10,000 for a long list, for a nest of that depth
and for both; steps are at most four times the nodes; a warm builder
performs no heap allocation for a list of 10,000 statements and a nest of
10,000.

End state, to paste in the pull request with the output:
- `rg -c 'todo!\(' src/emit/builder.rs` prints nothing.
- `rg -n 'T6b build' src` is empty.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  emit::builder`: 25 passed, 0 ignored.
- The CI job `Instruction count` within +0.02%.

Shortcuts that count as failure, beside the common list: a print-form
decision in a constructor (omitting an `else`, a value or a statement);
a Vec per list (a list is a run of the pool); copying a statement instead
of moving it; a statement constructor that reads the table for a
statement it was given in a handle.
```

Common to every prompt of phase C (T6k to T6x; part of each, in place of
the common block above):

```text
Repository: compiler-rust/. Read first: AGENTS.md; docs/THREE_TREES.md
11.4 "T6: the interface", "T6: the cut of the interface, revisited" and
"T6k: the skeleton"; src/bir/lower/js.rs and src/bir/j/rows.rs whole
(the header of rows.rs says what every body is).

You build bodies and convert call sites. You change no signature of the
trait, no doc-comment cost, no pinned size and no test other than what
the task names. If one cannot be met, stop: commit what passes, and
report the function, the test and the smallest input that shows it.
Adding a private helper is yours; say what you added in the commit
message, with its cost in its doc comment.

Converting a file means: every construction, read, release and detach of
a J or S node in it goes through `self.js` with `&self.arena` or `&mut
self.arena`, and the functions of the file take and return `B::E` where
they took and returned the `NodeId` of a J node (a `NodeId` of the source
tree stays). A call of a converted function from a file that is not
yours is wrapped at the call and nowhere else: `B::from_node(x)` for an
argument, `B::node(...)` around the result. A call from your file to a
function that is not converted is wrapped the other way. You change
nothing else in a file that is not yours. Where the code calls `plain::`
it calls the plain function; where it calls `norm::` it calls the rule
function named for that rule in "T6: the interface" (c): the family is
never changed.

Counts as failure: an `allow` attribute; `#[cfg(test)]` on a function of
the trait; a hash map or set; a Vec, Box, String or format! per node or
per operand; a walk over an expression; a `View::J`, `Op::J`, `plain::`
or `norm::` left in a converted file outside its tests; a new function
of the trait (stop and report the call that needs it); a changed
expected value in a test of the lowering; an ignored test other than
those of a later slice; a number you did not measure; `unsafe`.

Every commit: `cargo check --all-targets --manifest-path
compiler-rust/Cargo.toml` and `cargo clippy --all-targets --manifest-path
compiler-rust/Cargo.toml` print no warning; `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower` and `--lib bir::j` pass.
Never run the whole test suite: a checkout without the built runtime
fails tests that have nothing to do with this slice; CI judges those.
Push after every commit. Changelog: a fragment under changes/ ending in
`.internal.md`, one line starting with "- ".

The generated JavaScript does not change and the default build does not
run this code: the CI job `Instruction count` stays within +0.02%. If it
does not, stop and report the number.
```

T6k:

```text
Task T6k: the first implementation of the lowering's interface, and the
first two files on it.
Precondition, check it first and stop with a report if it fails:
`rg -c 'todo!\("T6k"\)' src/bir/j/rows.rs` prints 85, and `cargo test
--manifest-path compiler-rust/Cargo.toml --lib bir::lower::js::` shows 4
passed and 11 ignored.
Yours: src/bir/j/rows.rs; src/bir/lower/prim_cmp.rs and prim_block.rs
whole; the `State` struct, `State::new` and the three module lines named
below; the `impl` header lines of every file of src/bir/lower; the four
numbers of src/bir/lower/unit.rs named below; the 22 call expressions
named in commit 3; src/bir/lower/js_tests.rs (removing ignore attributes
only); the changelog fragment. Nothing else.

Do exactly this, one commit each, in this order, each pushed when made:

1. Every body marked todo!("T6k") in src/bir/j/rows.rs, as the table in
   its header says. Remove the ignore from the 11 tests of
   `bir::lower::js::tests`: 15 pass. The modules stay compiled for tests
   only in this commit.

2. The lowering holds the implementation.
   - Remove `#[cfg(test)]` from `pub mod js;` (src/bir/lower/mod.rs),
     `pub mod rows;` (src/bir/j/mod.rs) and `pub mod row;`
     (src/emit/mod.rs).
   - `struct State<'a>` becomes
     `struct State<'a, B: js::Js = crate::bir::j::rows::Rows>` with a
     first field `js: B`.
   - Every `impl State<'_> {` in src/bir/lower becomes
     `impl<B: super::js::Js> State<'_, B> {` (in mod.rs: `js::Js`); the
     same for `impl ProbeRules for State<'_>` and `impl Realizer for
     State<'_>`.
   - `State::new(input)` becomes, in the generic impl, `fn with(input,
     js: B) -> Self` with the same body and `js` stored; and a second
     impl block `impl<'a> State<'a> { fn new(input) -> Self }` that makes
     `Rows::default()`, calls `reserve(64)` on it and calls `with`. No
     caller of `State::new` changes.
   - In src/bir/lower/unit.rs the four allocation counts 85, 102, 85, 155
     become 86, 103, 86, 156: the one allocation is the operand stack
     (say so in the comment there). If any of the four is another number,
     stop and report it.
   No call site changes in this commit and no test changes its result.

3. prim_cmp.rs and prim_block.rs converted.
   - `comparison_constant`, `primitive_bool_comparison`,
     `primitive_int_comparison`, `primitive_literal_comparison`,
     `primitive_object_comparison`, `primitive_min_max`, `primitive_field`
     and `primitive_set_field` take and return `B::E`;
     `flat_make_field` keeps its source `NodeId` and returns
     `Option<B::E>`.
   - Their 22 calls outside the two files are wrapped: 20 in prim.rs
     (lines found by `rg -n 'primitive_(int|bool|literal|object)_comparison\(|primitive_min_max\(|primitive_field\(|primitive_set_field\(' src/bir/lower/prim.rs`),
     1 in rec.rs (`primitive_set_field`), 1 in mod.rs (`flat_make_field`:
     `.map(B::node)`). The two reads `self.primitive_bool(values[i])` in
     prim.rs are not touched.
   - `State::primitive_bool(&self, node: NodeId)` stays in prim_cmp.rs
     for those two reads, as the readers on `B::at(node)`; T6m deletes
     it. `State::primitive_string` and `primitive_bigint` are deleted:
     their reads are `text` and `bigint`. `primitive_literal_copy` is
     `copy_leaf` then `copy_cold`.
   - `primitive_int_comparison` strips `compare(l, r) <cmp> 0` so: the
     test is `kind` is `Call`, `arity` is 3 and `qualified_of` of
     operand 0 is a member "compare" of a runtime module; then
     `release` of the right operand, `unpack_rev` of the call, and three
     `pop`s: the callee (released), the new left, the new right.
   - `strictly_pure(..)` is `has(.., flag::STRICT)`. A `matches!` on two
     views is a `matches!` on two kinds.
   - `primitive_runtime` and `static_member` are T6m's: a call of
     `primitive_runtime` is wrapped; `flat_make_field` builds its member
     with `var`, `intern_text` and `dot(.., FieldPos::new(None), false)`
     and does not call `static_member`.
   The tests of both files pass unchanged.

4. The changelog fragment changes/lowering-interface-rows.internal.md.

Relations to hold (asserted by the tests): through the interface and
with today's calls the arena dumps alike, for every leaf, every plain
function, every list constructor and every rule function on 11 operands
in every pair; steps at 10,000 minus steps at 1,000 are nine times the
step from 1,000 to 2,000; a warm `Rows` allocates less for a call of
10,000 arguments than today's argument vector does.

End state, to paste in the pull request with the output:
- `rg -c 'todo!\("T6k"\)' src/bir` prints nothing; `rg -n 'T6k build'
  src` is empty.
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace)\('
  src/bir/lower/prim_cmp.rs src/bir/lower/prim_block.rs` matches only
  below `mod tests` of each file.
- `rg -n 'cfg\(test\)' -A1 src/bir/lower/mod.rs src/bir/j/mod.rs
  src/emit/mod.rs` shows none of `mod js;`, `mod rows;`, `mod row;`.
- `rg -c 'B::from_node|B::node\(|B::at\(' src/bir/lower` pasted (it
  may only fall from here to T6x).
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  bir::lower::js::`: 15 passed, 0 ignored.
- The CI job `Instruction count` within +0.02%.

Shortcuts that count as failure, beside the common list: a body of
rows.rs that does something other than its row of the header's table
(for one, a rule applied in a plain function); a reader that counts a
step; `Rows` holding anything but the operand stack and the step count;
an allocation pin moved by more than one; converting a function of
prim.rs because a wrapper looked untidy.
```

T6l (with the common block of phase C; read also "T6l: the skeleton",
src/bir/lower/js_stmt.rs and src/bir/j/rows_stmt.rs whole):

```text
Task T6l: the statement half of the lowering's interface on rows, and
the first three files on it.
Precondition, check it first and stop with a report if it fails: T6k is
merged (`rg -c 'todo!\("T6k"\)' src/bir` prints nothing), `rg -c
'todo!\("T6l"\)' src/bir/j/rows_stmt.rs` prints 29, and `cargo test
--manifest-path compiler-rust/Cargo.toml --lib bir::lower::js_stmt::`
shows 3 passed and 11 ignored.
Yours: the bodies marked todo!("T6l") of src/bir/j/rows_stmt.rs (the four
marked T6m, T6n and T6o are not yours); in src/bir/j/rows.rs the visibility of
three fields named in commit 1 and nothing else; src/bir/lower/assign.rs,
loops.rs and try_.rs whole; the bound of `State` and of every `impl`
header of src/bir/lower; the two module lines named in commit 2;
src/bir/lower/js_stmt_tests.rs (removing ignore attributes only); the
changelog fragment. Nothing else.

Do exactly this, one commit each, in this order, each pushed when made:

1. In src/bir/j/rows.rs: `pub struct E(NodeId)` becomes
   `pub struct E(pub(super) NodeId)`, and the fields `operands` and
   `steps` of `Rows` become `pub(super)`. Then every body marked
   todo!("T6l") in src/bir/j/rows_stmt.rs, as the table in its header
   says. Remove the ignore from the 8 tests of
   `bir::lower::js_stmt::tests` that are ignored as "T6l build": 11 pass
   and 3 stay ignored. The modules stay compiled for tests only in this
   commit.

2. The lowering holds both halves.
   - Remove `#[cfg(test)]` from `pub mod js_stmt;` (src/bir/lower/mod.rs)
     and `pub mod rows_stmt;` (src/bir/j/mod.rs).
   - Every `B: super::js::Js` in src/bir/lower becomes
     `B: super::js_stmt::JsStmt`; in mod.rs every `B: js::Js` becomes
     `B: js_stmt::JsStmt` (the struct `State` and its impls).
   The four allocation counts of src/bir/lower/unit.rs stay 86, 103, 86,
   156. No call site changes in this commit and no test changes its
   result.

3. assign.rs, loops.rs and try_.rs converted. No function of these files
   takes or returns the `NodeId` of a J node, so no caller is wrapped.
   What these files call in files that are not yours stays a `NodeId`
   call, wrapped here: `self.leaf(cx, B::node(unit))`,
   `self.if_statement(B::node(negated), yes, no)` (its result is pushed
   as it is), `self.statements.push(B::stmt_node(statement))`. An
   `out.value` is a `NodeId` until T6x: `B::from_node(value)` where it is
   given to the interface; `self.drop_pure_effect(value)` and
   `self.declare_empty(..)` are not touched.
   - `self.pure_expression(View::JUndefined, 0)` is
     `self.js.undefined(&mut self.arena, false)`; of a `View::Var` it is
     `self.js.var`.
   - assign.rs: `bir::j::assign` is `self.js.assign`.
   - loops.rs: `loops::Plan` keeps its fields. `push_loop_list` is
     `B::list_from`, `len` and `take_at` for every index, each statement
     pushed. A list's emptiness is `len`. `finish_loop` builds `while_`,
     `for_of` (its last argument is `op == Op::ForAwaitOf`) and
     `for_range` with the list of the body (`B::list_from`), never a
     block: there is no `block_from_list` left in the file. In the
     `while` with a prelude the condition `true` is made before
     `while_` is called. The range loop holds its start in a declaration
     when the end has statements and the start does not have
     `flag::DELAY_SAFE`; then `Range::init` is `None`.
   - try_.rs: `try_::Plan::blocks` becomes `[Option<ListId>; 3]` and
     `try_child` stores the list `take_list` returns (no block).
     `finish_try`: the lists are stored in the order the children
     returned, so with an exception variable the second is the handler
     and the third, if any, the finaliser; without one the second is the
     finaliser. `try_(body, handler with its variable, finaliser)`.
   The tests of the three files pass unchanged.

4. The changelog fragment
   changes/lowering-interface-statements.internal.md.

Relations to hold (asserted by the tests): through the interface and
with today's calls the arena dumps alike, for every statement, for every
constructor on six list shapes and for the three rules on 11 values;
steps at 10,000 minus steps at 1,000 are nine times the step from 1,000
to 2,000; a list and its block allocate exactly what today's two calls
allocate; J-M14 through a warm operand stack allocates less than with an
empty vector.

End state, to paste in the pull request with the output:
- `rg -c 'todo!\("T6l"\)' src/bir` prints nothing; `rg -n 'T6l build'
  src` is empty.
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace)\(|block_from_list|new_node\(|pure_expression|lists\.get'
  src/bir/lower/assign.rs src/bir/lower/loops.rs src/bir/lower/try_.rs`
  matches only below `mod tests` of each file.
- `rg -n 'cfg\(test\)' -A1 src/bir/lower/mod.rs src/bir/j/mod.rs` shows
  neither `mod js_stmt;` nor `mod rows_stmt;`.
- `rg -c 'B::from_node|B::node\(|B::at\(|B::stmt_node|B::stmt_from_node|B::list_from|B::list_id'
  src/bir/lower` pasted.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  bir::lower::js_stmt::`: 11 passed, 3 ignored (T6m, T6n, T6o).
- The CI job `Instruction count` within +0.02%.

Shortcuts that count as failure, beside the common list: a body of
rows_stmt.rs that does something other than its row of the header's
table; a second vector in `Rows`; a block built in a converted file; an
allocation pin that moves; a field of `Rows` or of `E` made more visible
than `pub(super)`; a reader that counts a step.
```

Common to T6m, T6n, T6o, T6p, T6w and T6q, built side by side (part of
each prompt, after the common block of phase C; read also "T6m to T6q:
the probes, and slices built side by side"):

```text
Six slices are built at the same time on one trunk. You touch only the
files listed under "Yours". These replace two rules of the common block:

- No signature changes. Every function keeps its parameters and result:
  a J node crosses a function boundary as a `NodeId`. Inside a body make
  a handle at the first interface call (`B::from_node(x)`,
  `B::stmt_from_node(x)`, `B::list_from(x)`; `B::at(x)` to read) and turn
  it back (`B::node`, `B::stmt_node`, `B::list_id`) only where it is
  stored in a field or a vector, returned, or passed to a function of
  the lowering. Between two interface calls in one body the handle is
  passed as it is: `B::from_node(B::node(..))` is a failure. You wrap no
  call in a file that is not yours and you edit no such file.
- No shared file: js.rs, js_stmt.rs, rows.rs, rows_stmt.rs, mod.rs,
  out.rs, unit.rs and the tests of the interface are not yours, unless
  "Yours" names one function of one of them. If a call you need is not
  in the trait, stop and report the site; do not add it.
- Storage stays: no field of `State`, of `Out` or of a plan changes its
  type; `values: &mut Vec<NodeId>` stays.

After converting, remove the imports the compiler reports unused; an
import only the tests of the file use moves below `mod tests`.

Hold in every commit: the four allocation counts of
src/bir/lower/unit.rs stay 86, 103, 86, 156; no expected value of a
test of the lowering changes. Hold in the pull request: the CI job
`Backend bridge coverage` at zero differences; `Instruction count`
within +0.02%; the check-mode build within +0.1% of its base (measure
with scripts/compare_build_instructions.py on Linux and paste the line;
if you cannot run it, say so: do not write a number).

Merging: another slice may land first. Merge trunk, do not rebase. A
conflict in a file that is yours is yours to resolve; a conflict in any
other file means one of the two slices broke the rule above: stop and
report.

Rulings of the reviews of T6m to T6p, part of every later conversion
prompt:

- A NEW private helper of a file that is yours may take or return a
  handle when every caller is in that file. A function that exists on
  trunk keeps its signature.
- Where "leave the calls an earlier slice wrapped as they are" would
  make a body turn a handle back and wrap it again, the outer wrapper
  goes, and the pull request says where.
- When your conversion removes the last production caller of a function
  in a file that is not yours (`cargo clippy --all-targets -- -D
  warnings` names it), delete exactly that function, and a helper only
  it used, one level at a time; or put `#[cfg(test)]` on one that only
  tests call. A commit of its own, listed in the pull request. No
  `allow`.
- `Instruction count` above +0.02%: rerun it once and report both
  figures.
- The check-mode figure: scripts/compare_build_instructions.py with its
  default build and five runs a side, pasted with its command. The
  script cleans tests/tests and removes the committed .mjs files for a
  moment; they come back with the build: check `git status` after it.
```

T6m (with both common blocks):

```text
Task T6m: prim.rs, konst.rs, record.rs and import.rs on the interface.
Precondition, check it first and stop with a report if it fails: `rg -c
'todo!\(' src/bir/j/rows.rs src/bir/j/rows_stmt.rs` prints nothing or
only lines of T6o, and `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower::js` shows no test ignored.
Yours: src/bir/lower/prim.rs, konst.rs, record.rs, import.rs whole; the
changelog fragment. Nothing else.

Do exactly this, one commit each, in this order, each pushed when made:

1. konst.rs, record.rs, import.rs.
   - A literal is the function of its kind: `plain::string` is
     `self.js.str`, `plain::int` is `self.js.int_literal`, a number is
     `self.js.number`, `View::JBool` is `self.js.boolean`,
     `View::JUndefined` is `self.js.undefined(.., false)` (`true` where
     `aux` was 1), `View::JNull` is `self.js.null`.
   - A node built from a slice of operands (`plain::node(View::JBlockLit
     { values, info }, aux)`, an object, an array, a call) is: `let mark
     = self.js.mark();`, `self.js.push(B::from_node(v))` for each operand
     in order, then `self.js.block(.., mark, info, aux)`, `object`,
     `array`, `call`. Where the code forced `NodeFlags::STRICT` on the
     result (`bir::j::pure_expression`), call `self.js.assume_strict` on
     the handle.
   - konst.rs: the comment of a constant is `self.js.comment(&mut
     self.arena, &mut handle, comment)`; the test for `undefined` under
     an option is `self.js.kind(.., B::at(value)) == Kind::Undefined`.
   - record.rs: the location of a record is `self.js.locate`.
   - import.rs: the callback is `self.js.list(&mut self.arena, 1,
     std::iter::once(B::stmt_from_node(ret)))` and `self.js.function(..,
     header, body)`: no block is built in the file.

2. prim.rs.
   - The wrapped calls T6k left (`B::node(self.f(B::from_node(x)))` for
     the functions of prim_cmp.rs and prim_block.rs) stay as they are:
     `values` holds `NodeId`s.
   - `primitive_int(node)` is `self.js.int(&self.arena, B::at(node))`.
     `primitive_bool` is a function of prim_cmp.rs, already converted:
     its two calls stay.
   - `primitive_statement`: the location of a statement is
     `self.js.locate_stmt`.
   - A runtime call and every call built from a slice: mark, push each,
     `self.js.call(.., callee, mark, info)`.
   - `Pmakedict`: when the one value has `Kind::Array`, `let count =
     self.js.unpack_rev(.., array)` and `count` times `self.js.pop()`.
     For each item: its key is `self.js.str_of(.., self.js.operand(..,
     r, 0))` when the item has `Kind::BlockLit` and `arity` 2, else
     none; with a key push `PropertyKey::Literal(text)` and keep
     `self.js.keep_operand(.., item, 1)` in the scratch (as a `NodeId`);
     without one `self.js.release(.., item)`. Then build the object from
     the scratch with mark and push. `primitive_steps` counts as today.
   - `PdictSpread`: an argument is flattened when it has `Kind::Object`
     and every key of `self.js.info_of(.., r)` is `Literal` or `Symbol`;
     then `unpack_rev` and `pop` each value into the scratch.
   - `Psome`, `PisNotNone`, `PvalFromOption` and the null conversions:
     the tests are `self.js.kind` and `self.js.aux`; the payload of an
     optional is `self.js.keep_operand(.., value, 0)`; the copy of a
     variable, `undefined` or `null` is `self.js.copy_leaf`.
   - `Ptemplate`: mark, push every value, `self.js.template(..,
     segments, mark)`; `PtaggedTemplate`: push `values[1..]`,
     `self.js.tagged(.., values[0], mark, info)`.
   - `PcreateExtension`: `self.js.comment`. A function value is
     recognised with `self.js.function_of`. The location of a
     primitive's value is `self.js.located` and `self.js.locate`.
   The tests of the four files pass unchanged.

3. The changelog fragment changes/lowering-interface-primitives.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes'
  src/bir/lower/prim.rs src/bir/lower/konst.rs src/bir/lower/record.rs
  src/bir/lower/import.rs` matches only below `mod tests` of each file.
- `git diff --stat origin/ocaml-to-rust-rewrite` names the four files
  and the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base, none ignored that the base
  did not ignore.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of these four files:
`--lib bir::lower` 546 passed, `--lib bir::j` 58 passed, the four pins
unchanged. Not run: the corpus gates, `Instruction count`, check mode.
The probe wrapped handles at each call, so it did not check the rule on
`B::from_node(B::node(..))`.

Shortcuts that count as failure, beside the common lists: a signature
changed; `text` or `intern_text` where `str_of` gives the id; a vector
made per primitive (the scratch of `object_scratch` is reused); a
second `unpack_rev` of one node; a file outside "Yours" in the diff.
```

T6n (with both common blocks; read also "T6n: the guard merge" and "T6n:
what stays on rows"):

```text
Task T6n: cond.rs and expr.rs on the interface.
Precondition, check it first and stop with a report if it fails: `rg -n
'fn (is_empty_block|branch_last_kind|release_stmt|if_blocks|take_if|function_of_block)'
src/bir/j/rows_stmt.rs` shows six functions, none with a `todo!` body,
and `cargo test --manifest-path compiler-rust/Cargo.toml --lib
bir::lower::js_stmt::` shows no test ignored for T6n.
Yours: src/bir/lower/cond.rs and expr.rs whole; the changelog fragment.
Nothing else. In cond.rs two things stay exactly as they are and are not
yours to convert: the `impl norm::IfLists for
super::out::StatementStack` block, and the call of
`norm::simplify_if_head` in `if_in_place` (T6x converts both).

The kinds of the interface are `crate::emit::row::Kind`; cond.rs has its
own `enum Kind { If, And, Or }`. Import `crate::emit::row::{self, flag}`
and write `row::Kind::Return`; do not rename either.

Do exactly this, one commit each, in this order, each pushed when made:

1. cond.rs.
   - `place`, `free_effect`: an empty block is
     `self.js.is_empty_block(&self.arena, &handle)`. `block_statement`:
     `self.js.explicit_block`, then `is_empty_block` of the result (no
     read of the list).
   - `empty_block` (tests only): `self.js.list(.., 0,
     std::iter::empty())`, `self.js.explicit_block`. `raw_if` (tests
     only): `self.js.if_plain`.
   - `single_return`: `stmt_kind == row::Kind::Return`, the value is
     `self.js.value_of`; its `NodeId` for the result is
     `NodeId(self.js.id(&self.arena, value))`.
   - `single_assignment`: `stmt_kind == Exp`; `value_of`; the value has
     `kind` `Bin`, `aux` `BinOp::Eq as u8`, and `var_of(operand(value,
     0)) == Some(target)`; the result is the id of `operand(value, 1)`.
   - `terminal`: `stmt_kind` is `Return`, `Throw`, `Break` or
     `Continue`.
   - `positive`: when `kind` is `Not`, `self.js.keep_operand(.., test,
     0)`.
   - `release_run`: `self.js.release_stmt` for each statement.
   - `unnest`: when `stmt_kind` is `Block`, clear the slot and
     `self.js.unblock(.., block, |s| statements.push(B::stmt_node(s)))`
     with `let statements = &mut self.statements;` taken before the
     call.
   - `effect_output`: a lone `Exp` statement gives
     `self.js.take_value`.
   - `push_s_if_empty`: `self.js.effect_if_impure(.., test, sink)` with
     the same sink; `self.scratch` is not used.
   - A declaration without a value: `self.js.declare(.., kind, target,
     None)` (`LetKind::Strict` in R1).
   - `merge_assignments`: for each of the two assignment statements,
     `let assignment = self.js.take_value(.., statement)` and
     `self.js.keep_operand(.., assignment, 1)`; then `self.js.cond`.
   - A strict test (`effect_run`): `self.js.has(.., B::at(value),
     flag::STRICT)`.
   - `tail_return_conditional`: the conjunction test is `kind == Bin`
     and `aux == BinOp::And as u8`; the last statements are read with
     `stmt_kind`. The guard is `self.js.if_blocks(.., not(test), then_,
     else_)` with `else_` `self.js.block_of` of the empty list.
   - `merge_tail_guard`: the guard merges when `stmt_kind == If`,
     `branch_last_kind(.., true)` is `None`,
     `branch_last_kind(.., false)` is `Return`, `Throw`, `Break` or
     `Continue`, and it is not the last statement of the run. Then
     `let (condition, then_, empty) = self.js.take_if(..)`;
     `self.js.release_stmt` of `empty` when there is one; `block_of` the
     rest; `if_blocks(condition, then_, else_)`; `self.js.list(.., 1,
     std::iter::once(statement))` and `block_of`. The then-block is
     never turned into a list.
   - `returns_after_effects`, `fold_return_tail`: `stmt_kind`; each
     value is `self.js.take_value`; the comma is `seq_rule`.

2. expr.rs.
   - Strict tests: `self.js.has(.., flag::STRICT)`.
   - `Resume::Fun`: `self.js.function_of_block(.., header,
     B::stmt_from_node(body))`, then `names::close`, then
     `self.js.locate` when there is a source location. `body` is still
     made with `block_of` and still goes through `loop_function_body`
     unchanged.
   - `hold_effect`: `self.js.effect(.., value, |s|
     held.push(B::stmt_node(s)))` into the scratch as today.
     `drop_pure_effect`: `self.js.effect` with a sink that pushes on
     `self.statements`; `self.scratch` is not used.
   The tests of the two files pass unchanged.

3. The changelog fragment changes/lowering-interface-conditional.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes|arena\.lists'
  src/bir/lower/cond.rs src/bir/lower/expr.rs`, outside `mod tests`,
  matches exactly three lines, all in cond.rs: `use
  crate::bir::j::norm;`, `impl norm::IfLists for
  super::out::StatementStack {` and the `norm::simplify_if_head(` of
  `if_in_place`.
- `git diff --stat origin/ocaml-to-rust-rewrite` names the two files and
  the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of these two files
(with T6m's probe in place): `--lib bir::lower` 546 passed, `--lib
bir::j` 58 passed, the four pins unchanged. The six functions have
tests of their own that run now (`a_guard_is_taken_apart_and_rebuilt_
over_its_blocks` and three more). Not run: the corpus gates,
`Instruction count`, check mode; no test measures that a chain of merged
guards stays linear (the functions are O(1) by construction).

Shortcuts that count as failure, beside the common lists: converting
`simplify_if_head` or the `IfLists` impl; a then-block taken apart into
a list in `merge_tail_guard`; `self.scratch` given to a rule; a
signature changed (`if_statement`, `unnest`, `place`,
`single_assignment`, `merge_assignments`, `assignment_statement` and
`drop_pure_effect` are called from other builders' files).
```

T6p (with both common blocks; read also "T6p: a node over other
operands", "T6p: operand lists in the pool" and "T6p: what stays on
rows"):

```text
Task T6p: args.rs, call.rs, ffi_args.rs, external.rs and jsx.rs on the
interface.
Precondition, check it first and stop with a report if it fails: `rg -n
'fn (take_operands|refill|push_list)' src/bir/j/rows.rs` shows three
functions, none with a `todo!` body, and `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower::js::` shows
`a_node_keeps_its_row_over_other_operands` passing.
Yours: src/bir/lower/args.rs, call.rs, ffi_args.rs, external.rs and
jsx.rs whole; the changelog fragment. Nothing else. In jsx.rs the free
functions `printed_form` and `jsx_tag` stay exactly as they are (T6r).

Operand lists: a `ListId` of operands in the arena's list pool is
storage. `self.arena.lists.get`, `push`, `push_iter`, `set`, `truncate`
and `slice` on such a list stay as they are, and so do the `ListId`
parameters and results. What goes is every constructor from a list:
`let mark = self.js.mark(); self.js.push_list(&self.arena, list);` and
then the constructor.

Do exactly this, one commit each, in this order, each pushed when made:

1. args.rs.
   - `delay_safe`: `self.js.has(.., B::at(value), flag::DELAY_SAFE)`.
     `runs_no_code`: `self.js.runs_no_code`.
   - Add the private function `declares_pure(&self, statement: NodeId)
     -> bool`: `stmt_kind == Kind::Declare` and `value_of` is none or
     runs no code; `defines_pure_values` and the closure in
     `sequence_arguments` call it.
   - `evaluate_now`, `Work::Enter`: read `self.js.kind` once.
     A `Seq`: `self.js.unpack_rev`, `pop` the first, `pop` the second;
     the first is released when it `has` `flag::STRICT`, else it is
     `exp_rule`; the second is entered.
     A literal is `Optional`, `Array`, `BlockLit`, or an `Object` whose
     keys (`self.js.info_of`, `self.arena.javascript`) are all `Literal`
     or `Symbol`. For a literal: `let mut shell = B::from_node(value);
     let count = self.js.take_operands(.., &mut shell);` push
     `Work::Rebuild(B::node(shell), count)`; then `let at = work.len();`
     push `Work::Enter(B::node(self.js.pop()))` `count` times and
     `work[at..].reverse()` (the first operand is entered first).
   - `Work::Rebuild(old, count)`: mark; push the `count` values;
     `self.js.refill(.., B::from_node(old), mark)`;
     `self.js.assume_strict`. No read of `aux`, of cold data or of the
     view.
   - `sequence_arguments`, the member callee: when `kind` is `Dot`,
     `take_operands`, `pop` the object, `evaluate_now` it, mark, push
     the result, `refill`.

2. call.rs.
   - The location of a call: `self.js.locate`.
   - The strict test of the remaining arguments: `self.js.has`.
   - The eta function: `self.js.list(.., 1,
     std::iter::once(B::stmt_from_node(ret)))` and `self.js.function`.

3. ffi_args.rs.
   - `literal_polyvar_block`: `kind == BlockLit`, `arity == 2`, the tag
     of `info_of` is `PolyVar`, and `kind` of `operand(r, 0)` is `Str`.
   - `hold_external_arg`: `wrapped` is `label == ArgOptional` and
     `kind == Optional`; the target read for the decision is `operand(r,
     0)` when wrapped. To hold: when wrapped, `take_operands` and `pop`
     give the target; `declare`; then mark, push the variable, `refill`
     and `assume_strict`. When not wrapped the value itself is declared
     and the variable replaces it.
   - `hold_external_obj_args`: the tests are `kind` (`Undefined`,
     `Optional`) and `has` (`DELAY_SAFE`, `STRICT`).
   - `external_optional_to_undefined_expr`,
     `external_option_unwrap_expr`: match on `kind`; the payload of an
     optional is `self.js.keep_operand(.., arg, 0)`; a copy is
     `self.js.copy(.., B::at(arg))`.
   - `optional_duplicable`: a loop over a `B::Ref`: `Var` reads
     `var_of`; `Named`, `Bool`, `Str`, `Template`, `Number` are
     duplicable; a `Dot` whose `member_of` has a position continues at
     `operand(r, 0)`.
   - `external_polyvar_unwrap_expr`: a `BlockLit` of arity 2 whose first
     operand is a `Number` gives `keep_operand(.., arg, 1)`.
   - `external_dispatch`: its parameter becomes `value: impl Fn(&mut B,
     &mut Bir, &T) -> B::E` and the two callers pass `|js, arena, v|
     js.string(arena, v)` and `|js, arena, v| js.int_literal(arena, *v
     as i32)` (the function is private to the file). The actions are
     collected in `self.scratch` (taken and put back; not
     `self.external_values`, which a caller holds): for each case
     `return_`, `list` of one, `block_of`, pushed as a `NodeId`. Then
     `self.js.list(.., count, actions.drain(..).map(B::stmt_from_node))`,
     `self.js.switch(.., arg, list, header, true)`, `list` of the one
     switch and `self.js.function`. No list is reserved for the actions.
   - `external_polyvar_string_expr`, `external_polyvar_int_expr`: the
     literal's text is `self.js.text` when `kind` is `Str`.
   - `external_polyvar_event_exprs`: `unpack_rev` and two `pop`s; the
     copy is `self.js.copy`.
   - `assemble_external_args_with_splice`: an `Array` last argument is
     `unpack_rev` and `count` `pop`s into `values`; `primitive_steps`
     counts one per element as today.

4. external.rs.
   - `hold_external_receiver`: the loop over a `B::Ref` (`Dot`
     continues at `operand(r, 0)`).
   - `compile_js_object_create`: the optional argument is matched on
     `kind` and its payload is `keep_operand`. The object is
     `self.arena.js_info(JsPayload::Object(keys))`, mark,
     `push_list(values)`, `self.js.object`. The copy for the test is
     `self.js.copy`. The two branches of the `if_` are `self.js.list` of
     one statement and of none.
   - `external_call_from_list`: mark, `push_list`, `self.js.call`.
     The two `call_from_list(target, args, None)`: mark, `push_list`,
     `self.js.new_`.

5. jsx.rs.
   - `compile_jsx`: the header goes through
     `self.arena.js_info(JsPayload::Jsx(..))`; mark, `push_list(values)`,
     `self.js.jsx(.., mark, info, jsx.jsx_children.is_some())`. The
     reserved list and its `set` and `truncate` stay.
   - `jsx_key`: match on `kind`; `keep_operand`.
   - `duplicate_jsx_key`: the loop reads `kind`, `member_of`, `var_of`
     and `aux`; the leaf is `self.js.copy_leaf` and `self.js.copy_cold`;
     each member is `self.js.dot` with the `member_of` of the original
     and `aux != 0` as its tag, then `copy_cold`.
     `copy_jsx_key_decoration` is deleted.
   The tests of the five files pass unchanged.

6. The changelog fragment changes/lowering-interface-calls.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes|NodeFlags::'
  src/bir/lower/args.rs src/bir/lower/call.rs src/bir/lower/ffi_args.rs
  src/bir/lower/external.rs src/bir/lower/jsx.rs`, outside `mod tests`,
  matches only lines of `printed_form` and `jsx_tag` in jsx.rs.
- `rg -c 'self\.js\.push_list' src/bir/lower` prints 4 for external.rs
  (`compile_js_object_create`, `external_call_from_list` and the two
  `new_`) and 1 for jsx.rs, and no other file.
- `git diff --stat origin/ocaml-to-rust-rewrite` names the five files
  and the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of these five files
(with the probes of T6m and T6n in place): `--lib bir::lower` 550
passed, `--lib bir::j` 58 passed, the four pins unchanged, the
allocation tests of the five files among them. Not run: the corpus
gates, `Instruction count`, check mode. Not measured: what the one more
copy of an external call's operands costs.

Shortcuts that count as failure, beside the common lists: a signature
changed (`call_node`, `compile_js_call`, `compile_js_object_create`,
`compile_jsx` and `sequence_arguments` are called from prim.rs,
`printed_form` from names.rs); a location, comment or `aux` read to
carry it across a rebuild (that is `refill`); `new_` replaced by a call
with invented information; a vector made per call or per case; the
callee of a JSX element built before its properties (the order of the
rows would change); converting `printed_form` or `jsx_tag`.
```

T6w (with both common blocks):

```text
Task T6w: tail.rs, rec.rs and exit.rs on the interface.
Precondition, check it first and stop with a report if it fails: `rg -c
'todo!\(' src/bir/j/rows.rs src/bir/j/rows_stmt.rs` prints nothing, and
`cargo test --manifest-path compiler-rust/Cargo.toml --lib
bir::lower::js` shows no test ignored.
Yours: src/bir/lower/tail.rs, rec.rs and exit.rs whole; the changelog
fragment. Nothing else. label.rs builds no J node (its one match of the
search below reads a flag of the source tree) and is not edited.

Do exactly this, one commit each, in this order, each pushed when made:

1. tail.rs.
   - `finish_self_call`: a value that is dropped is `self.js.release`;
     the test for the parameter itself is `self.js.var_of(.., B::at(value))
     == Some(param)`; an assignment is `self.js.assign`; the jump is
     `self.js.continue_(.., None)`.
   - `loop_function_body` keeps its signature: it takes and returns the
     `NodeId` of a block statement (expr.rs calls it). The aliases are
     `self.js.var` and `self.js.declare(.., LetKind::Alias, param,
     Some(value))`. The body's statements move with one call:
     `let (statements, moved) = (&mut self.statements, &mut
     self.tail_body_statements);` and `self.js.unblock(..,
     B::stmt_from_node(body), |s| { *moved += 1;
     statements.push(B::stmt_node(s)); })`. Then `take_list`, the
     condition `self.js.boolean(.., true)` (made before the loop),
     `self.js.while_(.., condition, B::list_from(list), None)`,
     `self.js.list(.., 1, std::iter::once(loop_))` and
     `self.js.block_of`. No block is built from a list by hand.

2. rec.rs.
   - `recursive_dummy`: `let mark = self.js.mark();` then
     `self.js.array(.., mark, 1)` or `self.js.object(.., mark, info)`,
     and `self.js.assume_strict` on either.
   - `recursive_block`, mode `Update`: `self.js.var`, and the
     placeholder is `self.js.declare(.., LetKind::Variable, var,
     Some(dummy))` stored as a `NodeId`.
   - `recursive_block`, the self block: assert `kind == BlockLit`;
     `let mut shell = B::from_node(value); let count =
     self.js.take_operands(.., &mut shell);` then for each index
     `self.js.pop()` is the field's value and `self.js.var` the target,
     both given to `primitive_set_field` as handles; after the loop
     `self.js.release(.., shell)`. Not `unpack_rev`: the block is
     released after its fields are written, as today.
   - `recursive_child`: the missing value is `self.js.undefined(..,
     false)`. A member's code is read with `B::list_from(list)`,
     `self.js.len` and `self.js.take_at`; a statement after a finished
     member is `self.js.release_stmt`.

3. exit.rs.
   - `declare_empty`: `self.js.declare(.., kind, var, None)`.
   - The exit variable: `self.js.int_literal(.., 0)` and `declare`.
   - A handler's block: `self.js.block_of(.., B::list_from(list))`,
     stored in `switch_output_nodes` as a `NodeId`. A dropped one is
     `self.js.release_stmt`.
   - `finish_catch`: `self.js.var` and `self.js.undefined(.., false)`.
   - `exit_dispatch`, one handler: `self.js.var`, `int_literal`,
     `self.js.bin(.., BinOp::EqEqEq, exit, order)`.
   - `exit_dispatch`, several: the reserved list of actions and its
     `self.arena.lists.push_iter` and `set` stay (a list assembled in
     the pool is storage, see the common block on operand lists; the
     same holds for statements). A shared case's empty action is
     `self.js.list(.., 0, std::iter::empty())` and `block_of`. The
     scrutinee is `self.js.var`, and the statement is
     `self.js.switch(.., scrutinee, B::list_from(actions), header,
     false)`.
   - `exit_child`: `int_literal` and `self.js.assign`; `undefined` and
     `declare`.
   The tests of the three files pass unchanged.

4. The changelog fragment changes/lowering-interface-exits.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes'
  src/bir/lower/tail.rs src/bir/lower/rec.rs src/bir/lower/exit.rs
  src/bir/lower/label.rs` matches only below `mod tests` of each file.
- `rg -n 'arena\.lists' src/bir/lower/exit.rs`, outside `mod tests`,
  shows the `push_iter` and the `set` of `exit_dispatch` and nothing
  else; tail.rs and rec.rs have none.
- `git diff --stat origin/ocaml-to-rust-rewrite` names the three files
  and the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of these three files
on trunk: `--lib bir::lower` 551 passed, `--lib bir::j` 58 passed, the
four pins unchanged. Every interface function the probe called had a
caller before. Not run: the corpus gates, `Instruction count`, check
mode.

Shortcuts that count as failure, beside the common lists: a signature
changed (`loop_function_body`, `finish_self_call`, `catch_children`,
`exit_children` and `recursive_children` are called from expr.rs and
call.rs); `unpack_rev` on the self block; a vector (a scratch of
`State` or a new one) for the actions of the dispatch: it grows with
the widest dispatch of the unit, which the reserved pool list does not;
an edit of label.rs.
```

T6o (with both common blocks; read also "T6w and T6o: the actions of a
switch stay a pool list" and "T6o: the copy"):

```text
Task T6o: switch.rs, variant.rs, untagged.rs and location.rs on the
interface.
Precondition, check it first and stop with a report if it fails: `rg -n
'fn (copy_stmt|copy_fresh|copy_recording|reserve_copy|copy_capacities)'
src/bir/j/rows.rs src/bir/j/rows_stmt.rs` shows five functions, none
with a `todo!` body, and `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower::js_stmt::` shows
`a_copy_costs_one_step_per_node_and_allocates_nothing_in_a_warm_unit`
passing.
Yours: src/bir/lower/switch.rs, variant.rs, untagged.rs and location.rs
whole; the changelog fragment. Nothing else.

Lists: `self.arena.lists.push_iter`, `set` and `truncate` on the
reserved list of a switch's actions stay as they are (storage). The
switch takes the list with `B::list_from(actions)`. Do not collect
actions in a vector.

Do exactly this, one commit each, in this order, each pushed when made:

1. location.rs. `locate_switch_run`: the test is
   `!self.js.stmt_located(.., &B::stmt_from_node(first))`; the location
   is `self.js.locate_stmt` on a handle made from `first`. No read of
   cold data or of a flag.

2. variant.rs.
   - A declaration without a value: `self.js.declare(.., kind, var,
     None)`.
   - `switch_key_expression`: `self.js.str(.., *text)` for a string key,
     `self.js.number(.., value)` for a numeric constant,
     `self.js.int_literal`, `self.js.string`, `self.js.boolean`,
     `self.js.null`, `self.js.undefined(.., false)`. Its result stays a
     `NodeId`.
   - `bind_named_scrutinee`: the test is `kind != Kind::Var`; `declare`
     with the value; `self.js.var`.
   - `named_scrutinee`: `self.js.var_of(.., B::at(value))` and
     `self.js.var`.
   - `advance_variant`: the tag read is `self.js.dot(.., value,
     plan.tag_name, FieldPos::NONE, false)`; a value that is not used is
     `self.js.release`.
   - `named_literal_test`: `null`, `undefined`, `self.js.bin` for every
     comparison and disjunction, `self.js.typeof_plain`,
     `self.js.string(.., "object")`.
   - `finish_variant`: `self.js.is_empty_block`, `release_stmt` for the
     statement, `release` for the scrutinee, `var`, `undefined`.

3. switch.rs.
   - Declarations without a value: `declare(.., None)`.
   - `switch_child`: the explicit break is `self.js.break_(.., None)`;
     the body's block is `self.js.block_of(.., B::list_from(list))`,
     stored as a `NodeId`.
   - `finish_switch`: the emptiness of the bodies is
     `self.js.is_empty_block`; a dropped body is `release_stmt`; the
     scrutinee alone is `self.js.exp_rule`; a shared case's empty action
     is `self.js.list(.., 0, std::iter::empty())` and `block_of`; the
     statement is `self.js.switch(.., scrutinee, B::list_from(actions),
     header, plan.kind != Kind::Integer)`.
   - `switch_result`: a lone assignment that becomes the declaration:
     `let assignment = self.js.take_value(.., statement);` then
     `self.js.keep_operand(.., assignment, 1)` and `declare` with it
     (`single_assignment` is cond.rs's and keeps returning two
     `NodeId`s; the second is not used here any more). `var`,
     `undefined`.
   - `finish_small_switch`: `release`, `self.js.bin(.., EqEqEq, ..)`,
     `is_empty_block`, `release_stmt`.

4. untagged.rs.
   - Delete the fields `copy_scratch` and `copied_labels` of
     `untagged::Storage`; `copied_vars` stays.
   - `copy_dispatch_output` keeps its signature and copies a statement:
     take `copied_vars`, `self.js.copy_stmt(..,
     &B::stmt_from_node(root), &mut vars)`, then the loop that gives
     each fresh variable its identifier and its order, unchanged; put
     the vector back. Move that loop into a private function
     `name_fresh(&mut self, vars: &mut Vec<(VarId, VarId)>)` (O(fresh
     binders); it drains the vector).
   - `untagged_scrutinee`: a variable is `var_of` and `var`; any other
     value is `self.js.copy_fresh(.., B::at(value), &mut vars)` with the
     same vector and `name_fresh`.
   - `emit_cached_action`: the cached block is staged with
     `self.js.unblock(.., root, |s| statements.push(B::stmt_node(s)))`.
   - Blocks: `block_of` and `explicit_block` over `B::list_from(list)`.
   - `untagged_clause`: the last statement is read with `stmt_kind`
     (`Return`, `Throw`, `Continue`, `Break`).
   - `untagged_switch` and `untagged_child`: a declaration without a
     value is `declare(.., None)`; the scrutinee that is not a variable
     is held with `declare` and read with `self.js.var` (the test is
     `kind != Kind::Var`).
   - `untagged_switch_statement`: `typeof_plain` for the scrutinee of a
     typeof switch; `self.js.switch(.., scrutinee, B::list_from(actions),
     header, true)`.
   - `untagged_test` and its helpers: `typeof_plain`, `string`, `str`,
     `number`, `boolean`, `null`, `undefined`, `bin`, `not`.
   - `untagged_instance`: each member is `self.js.dot(.., class,
     property, FieldPos::NONE, false)`; the `isArray` call is `mark`,
     `push(value)`, `self.js.call(.., callee, mark, info)`.
   - `finish_untagged`: `release`, `var`, `undefined`.
   - In the test helper `assert_mixed_allocation_free` (the one that
     reads `copy_scratch`): `state.untagged_storage.copy_scratch
     .reserve_arena(&state.arena)` becomes
     `state.js.reserve_copy(&state.arena)`; both reads of
     `state.untagged_storage.copy_scratch.capacities()` become
     `state.js.copy_capacities()`; the line `d.copied_labels.capacity(),`
     of the capacity list goes. No expected number changes.
   The other tests of the four files pass unchanged.

5. The changelog fragment changes/lowering-interface-switches.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes'
  src/bir/lower/switch.rs src/bir/lower/variant.rs
  src/bir/lower/untagged.rs src/bir/lower/location.rs` matches only
  below `mod tests` of each file.
- `rg -n 'copy_scratch|copied_labels' src/bir/lower` is empty.
- `git diff --stat origin/ocaml-to-rust-rewrite` names the four files
  and the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of these four files
(with T6w's probe in place): `--lib bir::lower` 550 passed and 1 failed,
the failure being the pin of `size_of::<Rows>()` that the design turn
then moved to 392; `--lib bir::j` 58 passed; the four allocation counts
unchanged, the untagged one among them. The probe kept one
`copy_dispatch_output` with a flag for statement or expression; the
form above (`name_fresh` and `copy_fresh` in `untagged_scrutinee`) was
not compiled. Not run: the corpus gates, `Instruction count`, check
mode.

Shortcuts that count as failure, beside the common lists: a signature
changed (`switch_children`, `variant_children`, `untagged_children`,
`group_switch_cases` and `grouped_bodies` are called from expr.rs and
exit.rs); a vector for the actions of a switch; `Js::copy` where the
copy has binders; a copy storage or a label vector kept in the
lowering; a parameter that says "statement or expression".
```

T6q (with both common blocks, the rulings included; read also "T6q: the
export coercion"):

```text
Task T6q: export.rs on the interface.
Precondition, check it first and stop with a report if it fails: `rg -n
'fn (equal|id_bound|declared|block_ids|effect_free)\b'
src/bir/j/rows.rs src/bir/j/rows_stmt.rs` shows five functions, none
with a `todo!` body, and `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower::js_stmt::` shows
`a_statement_is_effect_free_when_everything_below_it_is` passing.
Yours: src/bir/lower/export.rs whole; the changelog fragment; and, in a
commit of their own, the two functions that lose their last caller
(below). Nothing else: close.rs and scope.rs are not yours.

Ids: `Row::stmt`, the `NodeId` in `Init`, `Replacement`, the sites and
every table of `Tables` stay `NodeId`s. A read makes
`B::stmt_from_node(stmt)` or `B::at(node)` and goes through the
interface; a statement's or an expression's kind by id is
`self.js.kind_of(&self.arena, id.0)`. The kinds are
`crate::emit::row::Kind`; export.rs has its own `enum Kind`: import
`crate::emit::row::{self, flag}` and write `row::Kind::Declare`.

Three edits stay exactly as they are (T6x): `self.arena.replace(node,
copy)` in `substitute_after`; the `parents` test, the `detach` and the
`release` of `release_row`; the `parents` test, the `detach`, the
`release` of the blocks and the `lists.push_iter` of `coerced_list`.

Do exactly this, one commit each, in this order, each pushed when made:

1. Reading the exports and the rows.
   - `extract_exports`: `undefined` is `kind == Undefined`; the end of
     the comma spine is found with `operand(r, 1)` while `kind == Seq`;
     the export block is `kind == BlockLit` whose `info_of` is a
     `ModuleExport`. Each comma is taken apart with `unpack_rev` and
     two `pop`s (the first is `push_effect`, the second goes on); the
     block with `unpack_rev` and `count` `pop`s into `values`. A value
     dropped for a finished unit is `self.js.release`, then
     `self.js.undefined(.., false)`.
   - `push_effect`: `self.js.effect(.., value, |s|
     statements.push(B::stmt_node(s)))` with `let statements = &mut
     self.statements;`. `self.scratch` is not used.
   - `build_rows`: `stmt_kind` of the row. `Block`:
     `self.js.block_ids(.., &handle, |id| nested.push(NodeId(id)))`.
     `Declare`: `self.js.declared` and `self.js.value_of`; the function
     bit is `kind == Fun` of the value. `Rest`: `self.js.declared`.
   - `declared_by`: `stmt_aux & 3` for the kind of `let`; the variable
     is `self.js.declared`; a `Declare` gives the id of `value_of`
     (`NodeId(self.js.id(..))`), a `Rest` its own id.
   - `is_literal`, `classify`: `kind_of`; a reference's variable is
     `var_of`.
   - `replacement`, `member_of`, `move_alias_to_tail`, `coerce_exports`
     (the variable of an export's value), `alias_of`: `var_of`,
     `qualified_of`, `stmt_kind` and `value_of`.

2. The climbs and the effect.
   - `declared`: the binder's kind is `Declare` or `Rest`
     (`kind_of`); the climb is `self.js.owner`, through `If` and
     `Block` only.
   - `has_toplevel_effect`: a declaration row is `stmt_kind ==
     Declare` and a value that does not `has` `flag::STRICT`, any other
     declaration row has an effect; any other row counts one step and
     is `!self.js.effect_free(&self.arena, &handle)`. The work stack
     and the match on the statements go.
   - `row_of`: the table is sized by `self.js.id_bound`; the climb is
     `owner`; a function literal on the way is `kind_of == Fun`.
   - `mentions`: the owner of a site is `self.js.owner`; `safe` is
     `self.js.is_callee(&self.arena, site.node.0)`.
   - `equivalent_later`: `self.js.equal(&self.arena, B::at(initialiser),
     B::at(value), &mut 0)`.
   - `same_reusable_value`, `reusable_candidate`: `kind`, `var_of`,
     `qualified_of`, `member_of`, `aux` and `operand(r, 0)`.

3. What the fold builds.
   - `copy_replacement`: a variable is `self.js.var`; a module member
     is `self.js.copy_leaf(.., B::at(node))` and
     `self.js.assume_strict`; a chain of static reads is `copy_leaf`
     and `copy_cold` of its leaf, then for each read `self.js.dot` with
     the `member_of` of the original and `aux != 0` as its tag, and
     `copy_cold`. Every node made goes through `self.built` as today.
   - `define`: read whether the value is a function (`kind_of == Fun`)
     before the statement takes it; the statement is
     `self.js.declare(.., kind, var, value.map(B::from_node))`.
   The tests of the file pass unchanged.

4. What lost its last production caller: `Bir::copy_leaf`
   (src/bir/edit.rs) and `bir::j::member` (src/bir/j/mod.rs). Delete
   `Bir::copy_leaf`: nothing calls it any more. Put `#[cfg(test)]` on
   `bir::j::member`: tests of src/bir/j/mod.rs and of
   src/bir/lower/args.rs still call it, and those tests are not yours
   to change. Exactly these two, in this commit, listed in the pull
   request; run `cargo clippy --manifest-path compiler-rust/Cargo.toml
   --all-targets -- -D warnings` after it (an import only `member`
   used gets the same `#[cfg(test)]`).

5. The changelog fragment changes/lowering-interface-exports.internal.md.

End state, to paste in the pull request with the output:
- `rg -n 'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|copy_leaf|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes|arena\.lists|arena\.parents|NodeFlags::'
  src/bir/lower/export.rs`, outside `mod tests`, matches exactly eight
  lines: one in `substitute_after` (`replace`), three in `release_row`
  (`parents`, `detach`, `release`), four in `coerced_list` (`parents`,
  `detach`, `release`, `lists.push_iter`).
- `rg -n 'fn copy_leaf' src/bir/edit.rs` is empty, and `rg -n -B1
  'fn member\b' src/bir/j/mod.rs` shows `#[cfg(test)]` on the line
  before the function.
- `git diff --stat origin/ocaml-to-rust-rewrite` names export.rs, the
  two files of commit 4 and the fragment only.
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib bir::lower`
  and `--lib bir::j`: the counts of the base.
- The three CI numbers of the common block.

Run by the design turn against a probe conversion of export.rs on
trunk: `--lib bir::lower` 557 passed and 1 failed, the failure being
the pin of `size_of::<Rows>()` that the design turn then moved to 416;
`--lib bir::j` 58 passed; the four allocation counts unchanged. The
probe did not delete the two dead functions (`cargo check` reported
them). Not run: the corpus gates, `Instruction count`, check mode.

Shortcuts that count as failure, beside the common lists: converting
one of the three edits; a walk of a statement's parts in export.rs; a
field of `Row` or of `Tables` that changes its type; `Js::copy` for a
replacement (it is a leaf and a chain of reads: `copy_leaf` and `dot`);
an edit of close.rs or scope.rs; `text` comparisons where `equal` is
called today.
```

Common to T6x-a1, T6x-a2, T6x-a3 and T6x-a4, built one after the other
(part of each prompt, after the common block of phase C; read also 11.4
"T6x: the cut" and "T6x-a: the statement stack, after the probe"):

```text
Four slices put the statement stack of the lowering on statement
handles. Each starts from a trunk that has the slice before it merged.
These replace rules of the common block of phase C:

- Signatures and storage change, but only the ones your task names.
  Everything else keeps its parameters, its result and the type of its
  fields. Where a handle meets a function or a field your task does
  not change, wrap at that place and nowhere else: `B::stmt_from_node`
  and `B::stmt_node` for a statement, `B::list_from` and `B::list_id`
  for a list. `B::stmt_from_node(B::stmt_node(..))`, in either order
  and for lists too, is a failure: where both meet, both go.
- You add no function to the traits `Js` and `JsStmt`. If a call you
  need is not there, stop and report the site.
- A test is edited only where the task says so, and only so that it
  compiles: a wrap, a type argument, an argument added. No expected
  value changes. If one would, stop and report the test.

The probe. This row was converted once as a throw-away, on the branch
`bir-lower-js-interface-2`. You may read its code for a file as a
starting point: `git show
origin/bir-lower-js-interface-2:compiler-rust/src/bir/lower/FILE`. It
is unreviewed, it has no cost notes, and it predates the functions
`JsStmt::stmt_id` and `JsStmt::if_head`: where your task gives code or
a signature, the task is right and the probe is not. Merge nothing and
cherry-pick nothing from that branch.

Cost notes. Every function whose body or signature you change, and
every function inside an `impl` whose header you change, has a doc
comment that states its cost in words the checker knows: `Cost:`,
`O(...)`, "one step" or "one write". Say what one call costs, not
"cheap". From the repository root run `python3
scripts/check_lowering_cost_docs.py --base
origin/ocaml-to-rust-rewrite`: its last line must read
`missing/generic=0; removed=0`. CI runs it (job `script-tests`).

Every commit, beside the commands of the common block: `cargo clippy
--manifest-path compiler-rust/Cargo.toml --all-targets -- -D warnings`
prints nothing, and the cost-note check passes. A function that loses
its last caller in a commit is deleted in that commit, unless the task
names another one.

Hold in every commit: the four allocation counts of
src/bir/lower/unit.rs stay 86, 103, 86, 156; every `size_of` assertion
keeps its number.

Gates of the pull request, each pasted with its command or its CI job:
- `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  bir::lower` and `--lib bir::j`: the counts your task states, none
  ignored.
- `RUSTDOCFLAGS="-D warnings" cargo doc --locked --manifest-path
  compiler-rust/Cargo.toml --all-features --no-deps`: no warning.
- CI `Backend bridge coverage`: zero differences.
- CI `Instruction count`: at most +0.02%. Above it: rerun once and
  report both figures.
- Check mode: `scripts/compare_build_instructions.py` with its default
  build and five runs a side, pasted with its command; the budget is
  +0.1%. You report the figure; you do not change code to move it. If
  you cannot run it, say so and write no number. Check `git status`
  after it.
- `python3 ../scripts/count_lowering_ids.py | grep '^| total'` from
  compiler-rust, first line: paste it beside the line your task gives,
  and explain any difference.

Merging: trunk may move. Merge it, do not rebase.

Counts as failure, beside the lists of the common block: a `Clone` or
`Copy` bound on `B::S`; a `Default` bound on `B::S` or `B::L`; a
placeholder statement kept in a slot or a field (`Option` is the
form); a `Vec` made per call; a second statement stack or a staging
vector beside it; a signature changed that the task does not name; a
change in src/bir/j other than the one T6x-a2 names.
```

T6x-a1 (with both common blocks):

```text
Task T6x-a1: the statement stack owns statement handles.

Precondition, check it first and stop with a report if it fails: `rg -n
'fn (stmt_id|if_head)\b' compiler-rust/src/bir/lower/js_stmt.rs` shows
two functions and `rg -n 'fn row\b' compiler-rust/src/bir/j/rows_stmt.rs`
one; `--lib bir::lower` reads 568 passed and `--lib bir::j` 58.

Yours: src/bir/lower/out.rs from its start to `pub struct FreeId`
(the stack) and the tests of the stack below; in src/bir/lower/mod.rs
the type of the field `statements` and the six calls named below; in
every other file of src/bir/lower only the lines that call the stack;
the changelog fragment.

First edit, out.rs:

    enum Slot<S> { Statement(S), Held(Span), Dead(u32) }
    pub struct StatementStack<B: JsStmt> {
        slots: Vec<Option<Slot<B::S>>>,
        /// Held statements; one that was moved out leaves `None`.
        held: Vec<Option<B::S>>,
        // pushed, copied, scanned, empties: as they are
    }

`Default` is written out (`derive` would ask `B: Default`). Imports:
`super::js::Pools`, `super::js_stmt::JsStmt`.

The stack after this slice:
- `push(&mut self, statement: B::S)`, `fill(&mut self, slot: u32,
  statement: B::S)`.
- `fill_held(&mut self, slot: u32, statements: impl
  IntoIterator<Item = B::S>)`.
- `hold_run`: moves each statement (`Option::take` of the slot; a hold
  inside the run is moved entry by entry).
- `take_list(&mut self, js: &mut B, a: &mut Pools, span: Span) ->
  B::L`: counts the statements of the run, calls `js.list(a, count,
  ..)` with the statements moved out of their slots in order (a
  private `take_run(span) -> impl Iterator<Item = B::S>`), then
  `kill`, then `self.close(a, B::list_id(id))`. `close` keeps its
  signature (T6x-b).
- `drop_empty_blocks(&mut self, js: &mut B, a: &mut Pools, span:
  Span)`: `js.is_empty_block` and `js.release_stmt` in place of the
  `View` match and `Bir::release`.
- The reads keep their results, as rows: `first -> Option<NodeId>`,
  `first_single_slot` and `only -> Option<(u32, NodeId)>`, `last ->
  Option<NodeId>`, `statements(&mut self, span)` and
  `statements_rev(&mut self, span) -> impl Iterator<Item = NodeId>`.
  They read the row of a statement in place through one private
  function, which T6x-a3 deletes:

      /// The row of a statement the stack holds, the handle staying
      /// in place. O(1). Transition: deleted by T6x-a3.
      fn peek(s: &mut B::S) -> NodeId {
          let id = B::stmt_node(std::mem::replace(s, B::stmt_from_node(NodeId(u32::MAX))));
          *s = B::stmt_from_node(id);
          id
      }

- `statement_refs(&self, span) -> impl Iterator<Item = &B::S>`: the
  statements of a run read in place, in order (new; `args.rs` reads
  the runs of the arguments with it).
- `note_empty_block`, `clear`, `kill`, `trim`, `mark`, `since`,
  `reserve`, `has_statements`, `remove_empty`, `append`: results and
  parameters as they are.
Every function of the stack gets its cost note: the `impl` header
changes, so the checker reads all of them as new.

The callers, by one rule each:
- a push, a fill or a `place` whose argument was `B::stmt_node(x)`
  gives `x`; one whose argument is a row gives
  `B::stmt_from_node(row)`;
- `fill_held(slot, &rows)` gives the rows wrapped one by one, in
  order;
- `take_list(&mut self.arena, run)` is `take_list(&mut self.js, &mut
  self.arena, run)`: where its result went into `B::list_from`, that
  wrap goes; where it is stored, returned or passed on as a `ListId`,
  it is `B::list_id(..)`;
- `drop_empty_blocks(&mut self.arena, run)` is `drop_empty_blocks(&mut
  self.js, &mut self.arena, run)`;
- `cond.rs`: `impl norm::IfLists for StatementStack` becomes an
  implementation for a private struct of the stack and the
  implementation, with the same six bodies over them (the probe's
  `StackLists`); T6x-a3 deletes it.
- mod.rs: `statements: StatementStack<B>`; the three pushes of the
  realisation and the push of `seq` wrap their row; the two lists that
  go into `finish` and into the comma are `B::list_id(..)`.
No function outside out.rs changes its signature, but
`args.rs::declares_pure`, which takes `&B::S` (private, one file).

Tests you edit, only so that they compile:
- out.rs: `use crate::bir::j::rows::Rows;`; `StatementStack::default()`
  is `StatementStack::<Rows>::default()`; a pushed or filled
  `NodeId(n)` is `Rows::stmt_from_node(NodeId(n))`, also inside the
  expected `Slot::Statement(..)`; `take_list(&mut bir, span)` is
  `take_list(&mut Rows::default(), &mut bir, span)`; the two size
  assertions get their type argument and keep 96 and 12. This
  includes
  `the_actions_of_ten_thousand_switches_leave_only_the_slots_of_their_runs`.
- args.rs (two tests), cond.rs (the `Hand` helper: four pushes),
  oracle_tests.rs (one push, one `take_list`): the same wraps.

Commits, in this order, each pushed when made:
1. The stack and every caller, with the cost notes. It is one commit:
   the type cannot change without its callers.
2. changes/statement-stack-on-handles.internal.md.

End state, pasted with the output:
- `rg -n 'struct StatementStack<B: JsStmt>' src/bir/lower/out.rs`: one
  line.
- `rg -n 'B::stmt_node\(|B::stmt_from_node\(' src/bir/lower/out.rs`
  above `mod tests`: three matches, all inside `peek`; `rg -n
  'B::list_id\(' src/bir/lower/out.rs`: one, in `take_list`.
- `rg -n '(push|fill)\(B::stmt_node\(' src/bir/lower`: empty.
- `rg -n 'bir\.(view|release)\(' src/bir/lower/out.rs` above `mod
  tests`: empty.
- The totals line of count_lowering_ids.py. The probe read `| total |
  15647 | 213 | 108 | 621 | 270 | 142 | 68 | 54 | 36 | 28 | 23 | 1 | 5
  | 165 |` (trunk: 628 transition calls, 38 `stmt_from_node`, 82
  `stmt_node`, 28 `list_from`, 0 `list_id`).
- `--lib bir::lower` 568 passed, `--lib bir::j` 58.

Run by the design turn: the probe's first commit is this slice, 511
changed lines, and the lowering's tests pass on it.

Shortcuts that count as failure, beside the common lists: a read that
returns a reference or a slot in this slice (T6x-a3); a field of a plan
or of `State` other than `statements` that changes its type (T6x-a2,
T6x-a4); a second `peek` or a transition call in the stack outside it;
`unsafe` or `MaybeUninit` for `held`.
```

T6x-a2 (with both common blocks):

```text
Task T6x-a2: the statement-holding fields of one file, and the body of
a tail-loop function as a list.

Precondition: `rg -n 'struct StatementStack<B: JsStmt>'
compiler-rust/src/bir/lower/out.rs` shows one line (T6x-a1 is merged).

Yours: src/bir/lower/args.rs, loops.rs, try_.rs, rec.rs, tail.rs,
prim.rs, expr.rs; in mod.rs the types of the five fields below; in
out.rs three new functions; for commit 4 the one function of
js_stmt.rs and rows_stmt.rs and two tests of js_stmt_tests.rs; the
changelog fragment.

Commits, in this order, each pushed when made:

1. Fields of one file. Each struct takes the handle types as type
   parameters (`S`, `L`), `State` names them `B::S` and `B::L`, and
   the wraps a1 put where these fields are written and read go.
   - args.rs: `Evaluation<S>` with `statements: Vec<S>` (`Default`
     written out); `defines_pure_values(&self, &[B::S])`; the held
     statements of an argument are moved into the stack with
     `self.evaluation.statements.drain(range)`.
   - loops.rs: `Plan<L>` with `blocks: [Option<L>; 3]`;
     `push_loop_list(&mut self, list: B::L)`.
   - try_.rs: `Plan<L>` with `blocks: [Option<L>; 3]`.
   - rec.rs: `Member<S, L>` with `code: Option<L>` and `placeholder:
     Option<S>`.
   - tail.rs: `State::tail_assignments: Vec<B::S>`.
   - prim.rs: `primitive_statement(&mut self, statement: B::S, loc)`.
   - mod.rs: `tail_assignments: Vec<B::S>`, `rec_members:
     Vec<rec::Member<B::S, B::L>>`, `evaluation:
     args::Evaluation<B::S>`, `tries: Vec<try_::Plan<B::L>>`, `loops:
     Vec<loops::Plan<B::L>>`.
   One line of loops.rs keeps its wrap: the guard that
   `if_statement` returns is pushed as `B::stmt_from_node(guard)`
   (T6x-a3).
   Tests: the size assertions of loops.rs, try_.rs and rec.rs get
   their type arguments (`Plan<crate::bir::ListId>`; `Member<<Rows as
   JsStmt>::S, ListId>`) and keep 96, 72 and 32; one test of args.rs
   wraps the row it pushes into `evaluation.statements`.

2. A hold filled by a sink. out.rs gets:

       /// Where the statements given to `hold` start: a mark for
       /// `fill_held_since`. O(1).
       pub(super) fn held_mark(&self) -> usize
       /// One statement for the hold `fill_held_since` places. O(1).
       pub(super) fn hold(&mut self, statement: B::S)
       /// `fill_held` with the statements given to `hold` since
       /// `mark`. O(1).
       pub(super) fn fill_held_since(&mut self, slot: u32, mark: usize)

   and `expr.rs::hold_effect` is: take the mark, `self.js.effect(..,
   |s| statements.hold(s))`, `fill_held_since(slot, mark)`.
   `State::scratch` is not used there any more. Nothing may push a
   hold between the mark and the fill; `hold_effect` makes one
   interface call.

3. `loop_function_body` on lists: `tail.rs::loop_function_body(&mut
   self, frame: LoopRef, header: FuncId, body: B::L) -> B::L`. It
   returns `body` when the frame did not trigger. Otherwise it pushes
   the aliases as today, then moves the statements of the body with
   `for index in 0..self.js.len(&self.arena, body)` and
   `self.js.take_at(&mut self.arena, body, index)` (counting
   `tail_body_statements` as today), takes the run as a list, builds
   `while_` over it and returns `self.js.list(.., 1,
   std::iter::once(loop_))`. Its one caller, in expr.rs, keeps the
   list `take_list` gives, passes it through `loop_function_body`
   when there is a frame, and builds the function with
   `self.js.function(&mut self.arena, header, body)`. No `block_of`,
   `unblock` or `function_of_block` is left in the two functions.

4. `JsStmt::function_of_block` has no caller: delete it from the
   trait (js_stmt.rs), its body and its row of the header table
   (rows_stmt.rs), and the two tests of js_stmt_tests.rs that call
   it, with the helper `loop_function` only the second uses:
   `a_function_over_a_block_is_the_function_over_its_list` and
   `a_loop_function_over_a_list_is_the_one_over_a_block_in_fewer_steps`.
   Check with `rg -n 'function_of_block' compiler-rust/src`: empty.
   This is the one change you make to the trait and to src/bir/j.

5. changes/statement-fields-on-handles.internal.md.

End state, pasted with the output:
- `rg -n 'function_of_block' compiler-rust/src`: empty.
- `rg -n 'B::(stmt_node|stmt_from_node|list_from|list_id)\('` over
  args.rs, loops.rs, try_.rs, rec.rs, tail.rs, prim.rs, expr.rs above
  their tests: the lines that are left, each with the function or
  field of another slice it meets.
- The totals line of count_lowering_ids.py. The probe read `| total |
  15661 | 209 | 104 | 586 | 270 | 142 | 68 | 46 | 27 | 16 | 17 | 0 | 5
  | 165 |`.
- `--lib bir::lower` 566 passed (two tests deleted in commit 4),
  `--lib bir::j` 58.

One thing this slice changes that no test of the lowering reads: a
function through the tail loop makes one block fewer, so the rows
built after it have other ids, and it counts `statements + 3` steps
fewer. `Backend bridge coverage` at zero differences is the check:
read it in CI before you mark the pull request ready, and stop with
the job's summary if it is not zero.

Run by the design turn: the probe's commits of these files applied on
T6x-a1, 154 changed lines, 562 passed.

Shortcuts that count as failure, beside the common lists: a signature
of cond.rs changed (T6x-a3); `switch_output_nodes` or
`ActionState::cached` changed (T6x-a4); collecting the statements of
`hold_effect` in a vector; a block made of the body in
`loop_function_body`.
```

T6x-a3 (with both common blocks):

```text
Task T6x-a3: the stack's reads give references, and the functions of
cond.rs that place and return statements take and give handles.

Precondition: `rg -n 'fn held_mark' compiler-rust/src/bir/lower/out.rs`
shows one line and `rg -n 'function_of_block' compiler-rust/src` none
(T6x-a2 is merged).

Yours: src/bir/lower/out.rs (the stack), cond.rs, location.rs; one
line each of export.rs and mod.rs (below); in exit.rs, loops.rs,
switch.rs, untagged.rs and variant.rs only the reads of the stack and
the calls of the five functions of commit 1; the changelog fragment.

Commits, in this order, each pushed when made:

1. The reads by reference, `take`, and the five signatures of
   cond.rs, with every reader and every caller.
   The stack:
   - `first(&mut self, run) -> Option<&B::S>`;
     `first_slot(&mut self, run) -> Option<u32>`;
     `first_single_slot(&mut self, run) -> Option<(u32, &B::S)>`;
     `only(&mut self, run) -> Option<(u32, &B::S)>`;
     `last(&mut self, run) -> Option<&B::S>`;
     `last_slot(&mut self, run) -> Option<u32>`. The scans and what
     they add to `scanned` are today's.
   - `at(&self, slot) -> &B::S` (a slot that holds one statement;
     panics otherwise); `head(&self, slot) -> &B::S` and
     `head_mut(&mut self, slot) -> &mut B::S` (the first statement of
     a slot, a hold included).
   - `take(&mut self, slot: u32) -> B::S`: the statement of a slot
     that holds one, moved out; the slot becomes `Dead(1)`. One
     write. Panics on any other slot.
   - `take_run(run)` becomes `pub(super)`; `take_run_rev(&mut self,
     run) -> impl Iterator<Item = B::S>` gives the statements last
     first. Both leave holes; the caller kills the run.
   - `note_empty_block(&mut self, slot: u32, id: u32)` and `empties:
     Vec<(u32, u32)>`: `id` is `JsStmt::stmt_id` of the block, read by
     the caller before the block is pushed or filled.
     `drop_empty_blocks` compares `js.stmt_id(a, held)` with it.
   - Deleted: `peek`, `clear`, `statements_rev`, and `statements` as a
     production function. In its place, for the tests that release a
     run row by row (23 of them, in 19 files, which you do not edit):

         #[cfg(test)]
         impl StatementStack<crate::bir::j::rows::Rows> {
             /// The rows of the statements of a run. One step per
             /// slot of the run.
             pub(super) fn statements(&self, span: Span) -> impl Iterator<Item = NodeId> + '_ {
                 self.statement_refs(span).map(|s| s.row())
             }
         }

   The readers:
   - cond.rs: `single_return(&mut self, run) -> bool`; `unnest` and
     `effect_output` read the kind by reference and then `take(slot)`
     where they called `clear`; `merge_assignments` takes its two
     statements with `take`; `merge_tail_guard` reads the guard
     through `first_single_slot`, compares `last_slot(run)` with the
     guard's slot where it compared two rows, and takes the guard;
     `effect_conditional` writes the terminal test out over
     `self.statements.last(yes)` (`terminal` is deleted: a `&self`
     method cannot run while the reference lives);
     `returns_after_effects` walks `statement_refs(run).peekable()`,
     stops at the statement after which there is none, and drops the
     iterator before it adds to `scanned`; `fold_return_tail` uses
     `take_run_rev`; `release_run` uses `take_run`.
   - The three places that note an empty block (`place`,
     `block_statement`, `free_effect`) read the id first:

         let empty = self.js.is_empty_block(&self.arena, &statement)
             .then(|| self.js.stmt_id(&self.arena, &statement));
         self.statements.fill(slot, statement); // or push
         if let Some(id) = empty {
             self.statements.note_empty_block(slot, id);
         }

   - location.rs::locate_switch_run: `first_slot(run)`, then
     `stmt_located` of `head(slot)`, then `locate_stmt` on
     `head_mut(slot)`.
   - export.rs::build_rows: `for stmt in
     self.statements.statement_refs(run).map(|s|
     NodeId(self.js.stmt_id(&self.arena, s)))`.
   - mod.rs::append_outputs: the dropped run is released with `for
     statement in self.statements.take_run(second.stmts) {
     self.js.release_stmt(&mut self.arena, statement); }`.
   - exit.rs (one `first`), untagged.rs (one `last`): the reference
     goes straight to the reader.
   The five signatures change in the same commit (a function that
   returns a statement cannot give a row once `peek` is gone), each
   with all its callers:
   - `place(&mut self, slot: u32, statement: B::S)`: switch.rs 1,
     untagged.rs 2, variant.rs 1.
   - `if_statement(&mut self, test: NodeId, yes: Span, no: Span) ->
     B::S`: exit.rs 1, loops.rs 1, switch.rs 1, untagged.rs 1,
     variant.rs 1. The test stays a `NodeId` (T6x-d).
   - `unnest(&mut self, start: u32) -> Option<u32>`, the slot of the
     only statement: exit.rs 1, switch.rs 1, untagged.rs 4,
     variant.rs 1. Only `untagged.rs`, `Op::Block`, reads the result:
     it takes the statement with `self.statements.take(slot)` and
     then kills the run.
   - `single_assignment(&mut self, run: Span, target: VarId) ->
     Option<u32>`, the slot: switch.rs 1 (the declaration fold of the
     small switch: `take(slot)`, `take_value`, `keep_operand`, then
     `kill` of the run).
   - `assignment_statement(..) -> B::S`: switch.rs 1.
   `merge_tail_guard -> B::S` (private). A caller that only pushes,
   fills or places the result loses its wrap.

   In the same commit, `if_head`: the adapter T6x-a1 left in cond.rs
   gives rows through `peek`, `last_row` and `only_row`, which this
   commit deletes, so it cannot outlive them and the two do not
   compile apart. out.rs gets `impl<B: JsStmt> super::js_stmt::Runs<B> for
   StatementStack<B>` with `type Run = Span`: `trim` is
   `drop_empty_blocks`, `empty` a span of no slot, `last` the stack's
   `last`, `only` the statement of the stack's `only`, `release`
   `take_run` with `js.release_stmt` for each and then `kill`, `take`
   `take_list`. cond.rs:

       fn if_in_place(&mut self, head: u32, test: NodeId, mut yes: Span, mut no: Span) {
           let mut condition = B::from_node(test);
           if let Some(result) =
               self.js.if_head(&mut self.arena, &mut self.statements, &mut condition, &mut yes, &mut no)
           {
               if let Some(statement) = result.statement {
                   self.place(head, statement);
               }
           } else {
               let statement = self.if_statement(B::node(condition), yes, no);
               self.place(head, statement);
           }
       }

   The implementation of `norm::IfLists` in cond.rs and its struct
   are deleted. `use crate::bir::j::norm;` moves below `mod tests`;
   the `#[cfg(test)]` helper `raw_if` names `crate::bir::ListId` in
   full. `norm.rs` is not yours: `IfLists` and `simplify_if_head`
   stay, `Rows::if_head` and `js3_simplify_if` call them.
   Tests: the `Hand` helper of cond.rs passes the row's id to
   `note_empty_block` (`statement.0`).

2. changes/statement-stack-reads.internal.md.

End state, pasted with the output:
- `rg -n 'fn (peek|clear|statements_rev|terminal|only_row|last_row)\b'
  src/bir/lower/out.rs src/bir/lower/cond.rs`: empty.
- `rg -n 'IfLists|simplify_if_head' src/bir/lower` outside tests: one
  line, a comment of close.rs.
- `rg -n 'B::stmt_node\(|B::stmt_from_node\(' src/bir/lower/out.rs`:
  empty; in cond.rs above `mod tests`: two lines, in the
  `#[cfg(test)]` helpers `empty_block` and `raw_if`.
- `rg -n 'fn (place|if_statement|unnest|single_assignment|assignment_statement)\b'
  src/bir/lower/cond.rs`: the five signatures above.
- The totals line of count_lowering_ids.py. The probe read `| total |
  15681 | 193 | 99 | 527 | 271 | 143 | 68 | 15 | 12 | 10 | 8 | 0 | 5 |
  161 |` (it kept a value in the result of `single_assignment`, which
  this task drops; report yours).
- `--lib bir::lower` 566 passed, `--lib bir::j` 58. The tests of
  cond.rs that run every rule of J-S3 in place
  (`if_in_place_then_block_is_simplify_if_for_every_rule` and its
  neighbours) now run through `JsStmt::if_head`: they pass unchanged.

Run by the design turn: the probe's commits of these files with
`stmt_id` and `if_head` in place of its two gaps, about 475 changed
lines; the lowering's tests pass on it.

Shortcuts that count as failure, beside the common lists: a read that
returns an id where a reference serves; a statement read by reference
twice where one read and a slot serve (location.rs reads `scanned`
once); `stmt_id` used to find a statement again; a copy of a rule of
J-S3 in cond.rs; an edit of norm.rs; the tests that call
`statements(..)` edited; an action list touched (T6x-a4).
```

T6x-a4 (with both common blocks):

```text
Task T6x-a4: the actions of a switch are a run of the statement stack.

Precondition: `rg -n 'impl<B: JsStmt> super::js_stmt::Runs<B> for
StatementStack<B>' compiler-rust/src/bir/lower/out.rs` shows one line
(T6x-a3 is merged).

Yours: src/bir/lower/exit.rs, switch.rs, ffi_args.rs, untagged.rs; in
mod.rs the types of three fields; in out.rs one new function and the
body of `take_list`; the changelog fragment.

Commits, in this order, each pushed when made:

1. The fields. `State::switch_output_nodes: Vec<Option<B::S>>`
   (reserved with `resize_with(.., || None)`, written `Some(block)`,
   read with `.take().expect(..)` or `.as_ref()`): switch.rs and
   exit.rs. `untagged::ActionState<S>` with `cached: Option<S>`, not
   `Copy`; `untagged::Storage<S>` (`Default` written out),
   `untagged::Plan<S>`, `prepare<S>`; a by-reference read of a pool
   entry (`Pool::get_ref`) where `get` copied an `ActionState`;
   `copy_dispatch_output(&mut self, p: &Plan<B::S>, action: usize) ->
   B::S` copies the cached statement in place with `copy_stmt`;
   `untagged_clause -> (B::S, ClauseMeta)`. mod.rs:
   `switch_output_nodes`, `untagged: Vec<Option<untagged::Plan<B::S>>>`,
   `untagged_storage: untagged::Storage<B::S>`. The two size
   assertions of untagged.rs get their type argument and keep 120 and
   16. Where an action is written into the reserved pool list it is
   turned back with `B::stmt_node` until commit 2. The design turn did
   not build this commit on its own: if it cannot compile alone, make
   commits 1 and 2 one commit and say so in the pull request.

2. The action lists, with the function they are taken with. out.rs:

       /// The actions of a switch, pushed or filled above the runs
       /// they were made from, as one list: `take_list` without the
       /// close. An action is a block, and `close::decide` reads
       /// `return`s and declarations only. One step per slot of the
       /// run and per statement, each moved once.
       pub(super) fn take_actions(&mut self, js: &mut B, a: &mut Pools, span: Span) -> B::L

   Its body is the body of `take_list` up to and without the close;
   `take_list` calls it and then closes.
   - exit.rs (the dispatch of a catch), switch.rs (`finish_switch`)
     and ffi_args.rs (the string switch): take `let mark =
     self.statements.mark();` before the first action, push each
     action where it was written into the pool list or into
     `scratch`, and build the list with
     `self.statements.take_actions(&mut self.js, &mut self.arena,
     self.statements.since(mark))`. The reserved pool list, its
     `Lists::set` and `truncate`, and the use of `State::scratch` in
     ffi_args.rs go.
   - untagged.rs (`untagged_switch_statement`): the runs of the
     clauses are taken while the actions are assembled, so a push
     would land below the mark. Take the mark, reserve one hole per
     action (`action_count` times `self.statements.reserve()`), fill
     hole `i` with the body of clause `i` and the last hole with the
     default, then `take_actions` of the holes' run. Keep the order
     in which the clause runs and the default are taken: clauses
     first, in order, then the default.

3. changes/switch-actions-on-the-stack.internal.md.

End state, pasted with the output:
- `rg -n 'lists\.(set|truncate|push_iter)\(' src/bir/lower/exit.rs
  src/bir/lower/switch.rs src/bir/lower/ffi_args.rs
  src/bir/lower/untagged.rs` above their tests: empty.
- `rg -n 'take_actions\(' src/bir/lower`: one definition, its call in
  `take_list`, and four calls, one in each of the four files.
- `rg -n 'B::stmt_node\(|B::stmt_from_node\(' src/bir/lower` outside
  tests: cond.rs 2 (test helpers), export.rs 5, mod.rs 4.
- The totals line of count_lowering_ids.py. The probe read `| total |
  15689 | 191 | 97 | 498 | 271 | 143 | 68 | 8 | 3 | 2 | 3 | 0 | 5 |
  161 |`.
- `--lib bir::lower` 566 passed, `--lib bir::j` 58.

The gate of this slice. untagged.rs is the one place in T6x-a where a
slice changes where statements sit on the stack: the run of the last
clause becomes a dead range where it was popped, and the holes sit
above it while the switch is assembled. The lowering's tests pass on
it; no parity suite has run. Before you mark the pull request ready,
read in CI: `Backend bridge coverage` at zero differences, and the
parity jobs for JavaScript, the standard library and genType green.
Paste the four results. If one is not clean, stop and report the
first difference; do not change the layout to fix it.

Run by the design turn: the probe's commits of these files with
`take_actions`, about 210 changed lines; the lowering's tests, the
allocation counts and every size test hold on it.

Shortcuts that count as failure, beside the common lists: the actions
staged in `switch_output_nodes` or in any vector (tried: five
allocation tests fail); `take_list` for an action list (it closes a
list that has nothing to decide); the clause runs of untagged.rs
taken in another order; a hole left unfilled; a signature of cond.rs
or of another file changed.
```

T6x-b3b (with the common block of phase C and the common block of
T6x-a1 to T6x-a4, read with "T6x-b3b" for the four slices; the
paragraph "The probe" of that block is replaced by the one in the task;
read also 11.4 "T6x-b: an output's value, as built"):

```text
Task T6x-b3b: the close of a list and the unit's finish go through the
lowering's interface. One slice, one pull request against
ocaml-to-rust-rewrite.

Precondition, check it first and stop with a report if it fails: `rg -n
'fn with_stmt_at' compiler-rust/src/bir/lower/js_stmt.rs` shows one
line (the design turn of T6x-b is merged); `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower` reads 572 passed, `--lib
bir::j` 58, `--lib emit::builder` 28, none ignored; from compiler-rust,
`python3 ../scripts/count_lowering_ids.py | grep '^| total' | head -1`
prints `| total | 15834 | 174 | 87 | 437 | 241 | 126 | 57 | 5 | 3 | 2 |
3 | 0 | 5 | 162 |` (the first number may differ by lines trunk added;
the fourth must be 437).

Yours: src/bir/lower/close.rs whole; in src/bir/lower/out.rs
`StatementStack::take_list` (one line), `StatementStack::close`,
`FreePool::probe`, the field `FreePool::probes`, the imports and the
tests named below; in src/bir/lower/mod.rs `complete_unit`, `complete`,
`finish` (the one that takes `list`), the enum `ProbeInput` and one
number in the doc comment of `realize`; in src/bir/lower/export.rs
`extract_exports` and the one test line that calls it; in
src/bir/node.rs the deletion of `set_block_info`; the changelog
fragment. Nothing else. You add no function to a trait: the one this
slice needs, `JsStmt::with_stmt_at`, is on trunk.

The probe. This part was converted once as a throw-away (branch
`bir-lower-statement-probe`; `git fetch origin
bir-lower-statement-probe`). You may read `git show e1e5175130` and
`git show 6b6be5b6e2 -- compiler-rust/src/bir/lower/mod.rs` as a
starting point. They are unreviewed, they have no cost notes, and they
leave four places marked `// PROBE-GAP`: where this task gives code,
the task is right and the probe is not. Merge nothing and cherry-pick
nothing from that branch.

Commits, in this order, each compiling and passing the three filters on
its own (the design turn built them in this order), each pushed when
made:

1. The close. close.rs, with these imports in place of the three it
   has (`super::scope`, `strictly_pure`, `crate::bir::{..}`):

       use super::js::{Js, Pools};
       use super::js_stmt::JsStmt;
       use super::scope::{Decision, VarFacts};
       use crate::bir::{FuncHeader, NodeId};
       use crate::emit::row::{Kind, flag};

   and this body (the doc comment of `decide` stays; add to its cost
   paragraph, after "have their capacity.": "A statement is read where
   it is (`JsStmt::with_stmt_at`, O(1)): the list is not turned into
   rows and no statement leaves it."):

       pub(super) fn decide<B: JsStmt>(js: &B, bir: &mut Pools, list: B::L) {
           let count = js.len(bir, list);
           let mut steps = 0;
           for at in (0..count).rev() {
               steps += 1;
               match js.kind_at(bir, list, at) {
                   Kind::Return => {
                       // `scope::return_sites` takes a row until T6r: the returned
                       // value is named by its id.
                       let value = js.with_stmt_at(bir, list, at, |statement| js.value_of(bir, statement).map(|value| js.id(bir, value)));
                       let value = NodeId(value.expect("a return has a value"));
                       super::scope::return_sites(bir, value, at + 1 == count)
                   }
                   Kind::Declare => {
                       let decision = js.with_stmt_at(bir, list, at, |statement| {
                           let var = js.declared(bir, statement).expect("a declaration declares");
                           let kind = u16::from(js.stmt_aux(bir, statement));
                           let value = js.value_of(bir, statement);
                           // From here to `inline`: the lines of trunk, with
                           // `js.has(bir, value, flag::STRICT)` for
                           // `strictly_pure(bir, value)` and
                           // `inlinable_function(js, bir, value)`.
                           Decision::new(var, status, inline, built)
                       });
                       bir.js_scope.as_mut().expect("lowering scope").decisions.push(decision);
                   }
                   _ => {}
               }
           }
           bir.js_scope.as_mut().expect("lowering scope").close_steps += steps;
       }

       /// `inline_function_decl_from_variable` of the legacy pass: a function
       /// literal that is not a method, not `async` and has no directive. O(1):
       /// the header of the literal and its attributes, two reads.
       fn inlinable_function<B: Js>(js: &B, bir: &Pools, value: B::Ref<'_>) -> bool {
           let Some(header) = js.function_of(bir, value) else { return false };
           // the two lines of trunk
       }

   The decision is computed inside the closure, which only reads, and
   pushed after it: a reference into the statement (`value_of`) does
   not leave the closure. `inlinable_function` stays behind the three
   tests of `inline` that come before it, as on trunk: it is not
   called for every declaration.
   out.rs: `close(&mut self, js: &B, a: &mut Pools, list: B::L)`,
   calling `super::close::decide(js, a, list)` under `a.js_scope
   .is_some()`; in `take_list` the two lines of the close become
   `self.close(js, a, list);`; `use crate::bir::{Bir, ListId};` goes
   from the head of the file and the tests import `crate::bir::{Bir,
   NodeId}`. mod.rs, `complete_unit`: the close of the coerced list
   becomes

       let list = self.coerced_list(run);
       // `coerced_list` gives a pool list until T6x-e.
       self.statements.close(&self.js, &mut self.arena, B::list_from(list));

   The test of close.rs: make `let rows = Rows::default();` before the
   first `decide`, pass `&rows` to both calls, and import
   `crate::bir::j::rows::Rows` and `crate::bir::{Bir, ListId, View}` in
   the test module. It reads what it read: 10,004 steps (`10_001 + 3`),
   20,000 decisions, no allocation in the second close. Those numbers
   do not change; if one does, stop and report.

2. The export block's payload. export.rs, `extract_exports`: the
   parameter is `value: Option<B::E>` and the first line `let mut value
   = value?;`; the filter of the block literal is `.filter(|&info|
   matches!(self.arena.block_tag(info), TagInfo::ModuleExport(_)))`;
   the identifiers are copied where they were taken out:

       let TagInfo::ModuleExport(exports) = self.arena.block_tag(info) else { unreachable!("checked above") };
       let exports = exports.clone();

   In its doc comment, "No allocation: the identifiers are moved out
   of the block's payload." becomes "One allocation: the identifiers
   are copied out of the block's payload, which is the shape's and is
   shared with every other block of that shape and with the source
   (`Bir::block_info`)." `use crate::bir::JsPayload;` goes. The test
   `rows_and_references_are_read_without_allocation_once_the_tables_
   are_warm` calls `state.extract_exports(out.value, out.finished)`.
   mod.rs, `complete_unit`: from `let value = out.value.map(B::node);`
   to the call of `extract_exports` (the comment, the walk of the
   comma spine, the copy of the payload and the write) becomes one
   line, `let exports = self.extract_exports(out.value,
   out.finished);`. src/bir/node.rs: `Node::set_block_info` and its
   doc comment are deleted (`rg -n 'set_block_info' compiler-rust/src`
   must then be empty; no test calls it).

3. The finish. mod.rs: `fn finish(mut self, list: B::L, _finished:
   Finished, coerced: export::Coerced) -> Lowered`, its doc comment
   "The root block over the top-level list in flight, which is
   consumed. One step per statement of the list and one write per
   catch of the unit.", and the root made so:

       // The rest of the unit's finish reads the root by its id: the bulk
       // finish and the importer take a row until T6s, the replay of the
       // names until T6r.
       let root = self.js.block_of(&mut self.arena, list);
       let root = NodeId(self.js.stmt_id(&self.arena, &root));

   `complete_unit` gives `finish` a `B::L`: `let list =
   B::list_from(self.coerced_list(run));` under the comment of commit
   1, then `self.statements.close(&self.js, &mut self.arena, list);`,
   and the other arm is `self.statements.take_list(&mut self.js, &mut
   self.arena, run)` without `B::list_id`. `complete` (tests only):

       let value = out.value.unwrap_or_else(|| {
           let mut undefined = self.js.undefined(&mut self.arena, false);
           self.js.assume_strict(&mut self.arena, &mut undefined);
           undefined
       });
       let statement = self.js.exp(&mut self.arena, value);
       self.statements.push(statement);

   and its list is the result of `take_list` as it is.
   `State::pure_expression` stays `#[cfg(test)]`: tests of args.rs,
   call.rs and cond.rs call it.

4. The probe function that nothing calls. out.rs: delete
   `FreePool::probe` with its doc comment, the field `probes` with its
   doc comment (and `probes: 0` in `Default`), and `ProbeInput` from
   the import. mod.rs: delete the enum `ProbeInput` with its doc
   comment; in the doc comment of `realize`, "two moves of its 88
   bytes" becomes "two moves of its 80 bytes". out.rs tests:
   `size_of::<FreePool<Rows>>()` is 80 (the field is gone: the one
   size this slice moves), and the last two tests of the file
   (`ten_thousand_deferred_nodes_are_probed_and_realized_once`,
   `nonfree_child_is_kept_without_reprobing`) are replaced by these
   two, verbatim:

       /// A chain of 10,000 deferred sequences over one leaf, pushed as the
       /// lowering pushes them (`Free` records, the tail first), is realized
       /// once per record on the explicit stack: the leaf, then each head.
       #[test]
       fn ten_thousand_deferred_nodes_are_realized_once() {
           let mut pool = FreePool::default();
           let mut oracle = Oracle::default();
           let cx = Cx::value();
           let mut free = pool.push(Free::Leaf(Rows::from_node(NodeId(0))));
           for n in 1..=10_000 {
               free = pool.push(Free::Seq { first: Rows::from_node(NodeId(n)), second: free });
           }
           assert!(oracle.visits.is_empty());
           let out = pool.realize(cx, Probed::Free(free), &mut oracle);
           assert_eq!(out.value.map(Rows::node), Some(NodeId(0)));
           assert_eq!(pool.realized, 10_001);
           assert_eq!(oracle.visits, (0..=10_000).collect::<Vec<_>>());
       }
       /// A deferred conditional is realized after its branches, the then
       /// branch first; an output that is not deferred is returned as it is
       /// and realizes nothing.
       #[test]
       fn a_deferred_conditional_is_realized_after_its_branches() {
           let mut pool = FreePool::default();
           let mut oracle = Oracle::default();
           let cx = Cx::returning();
           let then_ = pool.push(Free::Leaf(Rows::from_node(NodeId(1))));
           let else_ = pool.push(Free::Leaf(Rows::from_node(NodeId(3))));
           let free = pool.push(Free::Cond { test: Rows::from_node(NodeId(2)), then_, else_ });
           let out = pool.realize(cx, Probed::Free(free), &mut oracle);
           assert_eq!(out.value.map(Rows::node), Some(NodeId(1)));
           assert_eq!(pool.realized, 3);
           assert_eq!(oracle.visits, vec![1, 3, 2]);
           let kept = pool.realize(cx, Probed::Out(output(Span { start: 0, len: 1 }, None, Finished::True)), &mut oracle);
           assert_eq!(kept.finished, Finished::True);
           assert_eq!(pool.realized, 3);
       }

The fragment changes/three-trees-t6x-b3b.internal.md, one bullet, is
part of commit 4: the slice is four commits.

Tests. You edit only what is named above: the two calls and the
imports of the test of close.rs, the import line of the tests of
out.rs, one line of a test of export.rs, the size of `FreePool<Rows>`,
and the two replaced tests. No other expected value changes; the
replaced tests keep every assertion that does not name the deleted
counter. `--lib bir::lower` reads 572 passed after every commit (two
tests replaced by two), `--lib bir::j` 58, `--lib emit::builder` 28.
The tests that guard commit 2 exist and you do not edit them:
unit.rs `export_consumption_does_not_empty_shared_block_metadata`,
`supported_unit_exercises_both_texts_and_shared_export_coercion` and
the four `full_unit_allocation_boundary_*` (86, 103, 86, 156).

End state, each command run from compiler-rust and pasted with its
output. A command is one line, however long. The design turn ran each
on trunk and on its own build of this slice; "now" is what trunk
prints, "then" what you must print:

    rg -n 'B::(from_node|node|at|stmt_from_node|stmt_node|list_from|list_id)\(|\.map\(B::node\)' src/bir/lower/close.rs src/bir/lower/out.rs src/bir/lower/mod.rs

  Now seven lines: out.rs `take_list` (`B::list_id`); mod.rs
  `complete_unit` 2, `complete` 3, `enter` 1. Then two: mod.rs
  `complete_unit` (`B::list_from(self.coerced_list(run))`, T6x-e) and
  `enter` (`B::from_node(self.constant(value))`, T6x-d).

    rg -n 'fn decide|fn close\(|fn finish\(mut self|fn inlinable_function' src/bir/lower/close.rs src/bir/lower/out.rs src/bir/lower/mod.rs

  Then: `pub(super) fn decide<B: JsStmt>(js: &B, bir: &mut Pools,
  list: B::L)`; `fn inlinable_function<B: Js>(js: &B, bir: &Pools,
  value: B::Ref<'_>) -> bool`; `pub(super) fn close(&mut self, js: &B,
  a: &mut Pools, list: B::L)`; `fn finish(mut self, list: B::L,
  _finished: Finished, coerced: export::Coerced) -> Lowered`.

    rg -n -A2 'pub\(super\) fn extract_exports' src/bir/lower/export.rs

  Then the second line after it reads `value: Option<B::E>,`.

    rg -n 'set_block_info|ProbeInput|\.probes\b|pub probes' src/bir

  Now 16 lines; then empty.

    rg -n 'View::|\.view\(|lists\.get|strictly_pure' src/bir/lower/close.rs

  Now 13 lines; then five, all inside `mod tests` (the rows the test
  builds).

    rg -n 'with_stmt_at\(' src/bir/lower --glob '!*_tests.rs' --glob '!js_stmt.rs'

  Now empty; then two lines, both in close.rs.

    rg -n 'js_info\(|block_from_list|new_node\(|pure_expression\(' src/bir/lower/mod.rs

  Now nine lines; then five: the definition of `pure_expression` (two
  lines) and three `source.new_node` of a test.

    rg -n 'mem::take\(exports\)|block_tag\(' src/bir/lower/export.rs src/bir/lower/mod.rs

  Now two lines (the take in export.rs, `block_tag` in mod.rs); then
  two, both `block_tag` in export.rs.

    python3 ../scripts/count_lowering_ids.py | grep '^| total' | head -1

  The design turn's build read `| total | 15775 | 169 | 86 | 433 | 240
  | 126 | 57 | 4 | 3 | 3 | 0 | 0 | 5 | 148 |`: `from_node` 241 to 240
  (export.rs), `stmt_from_node` 5 to 4 and `list_id` 3 to 0 (mod.rs
  and out.rs), `list_from` 2 to 3 (mod.rs, until T6x-e). Paste yours
  beside it and explain any difference in columns four to thirteen.

Cost notes. From compiler-rust: `python3
../scripts/check_lowering_cost_docs.py --base
origin/ocaml-to-rust-rewrite`. It reports every function whose
signature or body changed (the design turn's build: `changed/new=8;
missing/generic=0; removed=0`) and its last line must read
`missing/generic=0`. The notes this task gives (`decide`,
`inlinable_function`, `extract_exports`, `finish`) are the ones to
write; `close`, `take_list`, `complete_unit` and `complete` keep
theirs, which still say what a call costs.

Gates of the pull request, beside those of the common blocks: the
three filters with the counts above; clippy with `-D warnings`; `cargo
doc` with warnings denied; CI `Backend bridge coverage` at zero
differences and the parity jobs for JavaScript, the standard library
and genType green, read before the pull request is marked ready (after
commit 2 the payloads made after the export fold have ids one lower on
rows, which no decision reads: these jobs are the check, and if one is
not clean you stop and report the first difference); the four
allocation counts; CI `Instruction count` read and reported, with one
rerun and both figures. For this slice that replaces the limit of the
common block: the default build does not reach the lowering, so the
figure is the job's spread (the three parts of this row on trunk read
+0.014%, -0.039% and +0.023%). If both runs read above +0.05%, stop and
report the functions the job lists.

Run by the design turn, in a copy that was not pushed: these four
commits one after the other; after each, the three filters passed; on
the last, rebased on the design turn's final head, they read 572, 58
and 28, with clippy and `cargo doc` clean, the cost-note check
at zero, the allocation counts and the close test unchanged; 117 lines
added and 188 removed in five files. Not run: `Backend bridge
coverage`, the parity suites, `Instruction count`, check mode.

Shortcuts that count as failure, beside the common lists: `B::list_id`,
`B::stmt_from_node` or `B::stmt_node` in close.rs; `take_at` in
`decide` (it moves the statement out); a `Vec` of the statements or of
their ids; `inlinable_function` called before the tests that precede
it on trunk; a second `with_stmt_at` for the same statement; the
payload copied in `complete_unit` or written into a node
(`set_block_info`, `js_info` in mod.rs); `std::mem::take` of the
identifiers (it empties a payload other blocks share: six tests fail);
the root turned back with `B::stmt_node`; `FreePool::probe` or
`ProbeInput` kept under `#[cfg(test)]`; an edit of scope.rs, of
`coerced_list`, of `coerce_exports` or of any function of export.rs
other than `extract_exports`; an edit of js.rs, js_stmt.rs, rows.rs,
rows_stmt.rs or src/emit.
```


T6x-e2 (with the common block of phase C and the common block of
T6x-a1 to T6x-a4; read also 11.4 "T6x-e and T6x-f: the fold reads where
its rows are", decisions 1 and 2). T6x-e3, e4 and f have no prompt: no
build of them ran.

```text
Task T6x-e2: jsx.rs builds a JSX element with its callee apart and
copies a key with the interface. One slice, one pull request against
ocaml-to-rust-rewrite.

Precondition, check it first and stop with a report if it fails: `rg -n
'fn jsx_element' compiler-rust/src/bir/lower/js.rs` shows one line (the
design turn of T6x-e and f is merged); `cargo test --manifest-path
compiler-rust/Cargo.toml --lib bir::lower` reads 579 passed, `--lib
bir::j` 71, `--lib emit::builder` 40, none ignored; from compiler-rust,
`python3 ../scripts/count_lowering_ids.py --self-test` prints `32
files, 30 transition calls` and `python3
../scripts/count_lowering_ids.py | grep '^| total' | head -1` prints
`| total | 16062 | 89 | 15 | 30 | 3 | 2 | 15 | 6 | 2 | 2 | 0 | 0 | 0 |
146 |` (the first number may differ by lines trunk added; the fourth
must be 30).

Yours: in src/bir/lower/jsx.rs the functions `compile_jsx` and
`duplicate_jsx_key`; in src/bir/lower/js.rs the deletion of `Js::jsx`
and three sentences of the doc comment of `Js::jsx_element`; in
src/bir/j/rows.rs the body of `jsx_element`, the deletion of `jsx` and
of `Rows::jsx_over`, and two cells of the module's table; in
src/bir/lower/js_tests.rs the two places that call `r.jsx(`; the
changelog fragment `changes/three-trees-t6x-e2.internal.md`. Nothing
else. You add no function to a trait.

The probe. This file was converted once as a throw-away (draft pull
request 383, commit cca7635c3). You may read it. Copy nothing from it:
its functions are named `jsx_apart` and `copy_members` with other
bodies on rows, and its commit does not apply. Where this task gives
code, the task is right.

Commits, in this order, each compiling and passing the three filters on
its own (the design turn built them in this order), each pushed when
made:

1. jsx.rs. First edit: `compile_jsx`, whole, doc comment included:

           /// X: compile_jsx. O(props + children + spelling bytes), after shared
           /// argument sequencing. Optional undefined props are consumed and omitted.
           /// Property keys go directly into the unit's pool. The operands after
           /// the callee are pushed on the operand stack as they come, and the
           /// callee, built after them, is given apart (`Js::jsx_element`): one
           /// move each, nothing allocated once the stack has its capacity.
           pub(super) fn compile_jsx(
               &mut self,
               jsx: &JsxElement,
               args: impl IntoIterator<Item = B::E>,
           ) -> B::E {
               let mut args = args.into_iter();
               let mut props = PropertySpan {
                   start: crate::bir::pools::index(self.arena.pools.property_keys.len()), len: 0,
               };
               // The callee is built last (built earlier, its module and variable
               // would be registered before the key's runtime module), so it is
               // given to `Js::jsx_element` apart from the operands pushed here.
               let mark = self.js.mark();
               let tag = args.next().expect("JSX tag");
               self.js.push(tag);
               if jsx.jsx_spread {
                   let spread = args.next().expect("JSX spread");
                   self.js.push(spread);
               }
               for (name, optional) in &jsx.jsx_props {
                   self.primitive_steps += 1;
                   let value = args.next().expect("JSX prop");
                   if *optional && self.js.kind(&self.arena, B::of(&value)) == Kind::Undefined {
                       self.js.release(&mut self.arena, value);
                   } else {
                       let key = PropertyKey::Literal(self.arena.intern_text(name));
                       self.arena.pools.property_keys.push(key);
                       props.len += 1;
                       self.js.push(value);
                   }
               }
               for _ in 0..jsx.jsx_children.unwrap_or(0) {
                   self.primitive_steps += 1;
                   let child = args.next().expect("JSX child");
                   self.js.push(child);
               }
               if jsx.jsx_key {
                   let key = self.jsx_key(args.next().expect("JSX key"));
                   self.js.push(key);
               }
               assert!(args.next().is_none(), "JSX argument count");
               let callee = self.jsx_callee(&jsx.jsx_ffi);
               let info = self.arena.js_info(crate::bir::JsPayload::Jsx(JsxHeader {
                   spread: jsx.jsx_spread,
                   props,
                   children: jsx.jsx_children.unwrap_or(0) as u32,
                   key: jsx.jsx_key,
                   multi: jsx.jsx_multi,
                   fragment: jsx.jsx_fragment,
               }));
               self.js.jsx_element(&mut self.arena, callee, mark, info, jsx.jsx_children.is_some())
           }

   Then `duplicate_jsx_key`, whole, doc comment included (it is the
   last function of the `impl`; the closing brace of the `impl` stays):

           /// A: is_okay_to_duplicate(false), then the copy. O(d) for a d-deep
           /// member spine: the walk here reads the shape, and the copy
           /// (`Js::copy_members`) reads the chain again and makes its d + 1
           /// nodes. A failed shape leaves the original key untouched and creates
           /// no nodes. A reference is read with `var_of` before the kind
           /// (THREE_TREES 11.4, "For T6v: a dotted global").
           fn duplicate_jsx_key(&mut self, key: &B::E) -> Option<B::E> {
               let mut r = B::of(key);
               loop {
                   self.primitive_steps += 1;
                   let reference = self.js.var_of(&self.arena, r).map(|var| {
                       !self
                           .arena
                           .vars
                           .flags(var)
                           .contains(crate::bir::VarFlags::JS_GLOBAL)
                           || !self.arena.vars.name(var).as_str().contains('.')
                   });
                   match (reference, self.js.kind(&self.arena, r)) {
                       (Some(true), _) => break,
                       (None, Kind::Dot)
                           if self
                               .js
                               .member_of(&self.arena, r)
                               .is_some_and(|(_, position)| position.get().is_some()) =>
                       {
                           r = self.js.operand(&self.arena, r, 0);
                       }
                       (None, Kind::Qualified | Kind::Bool | Kind::Str | Kind::Number) => break,
                       (None, Kind::Template) if self.js.aux(&self.arena, r) == 1 => break,
                       _ => return None,
                   }
               }
               // The shape ends at the first node that is not a member read, which
               // is where the copy of the chain ends too.
               Some(self.js.copy_members(&mut self.arena, B::of(key), |_| {}))
           }
       }

   After this commit: the three filters read 579, 71 and 40; the
   self-test prints `32 files, 26 transition calls`.

2. `Js::jsx` is deleted. In js.rs remove the method `jsx` with its doc
   comment; in the doc comment of `jsx_element` the sentences that
   refer to `Js::jsx` say what they mean without it ("one per operand,
   the callee counted as one."; "Panics when the operands are not the
   tag and what the header counts."; the reference to the decision ends
   "decision 1: `jsx.rs::compile_jsx`.)"). In rows.rs remove `jsx` and
   `jsx_over`, and `jsx_element` is:

           fn jsx_element(&mut self, a: &mut Pools, callee: E, mark: Mark, info: JsId, has_children: bool) -> E {
               let start = self.since(mark);
               self.operands.push(callee.0);
               self.operands[start..].rotate_right(1);
               let JsPayload::Jsx(header) = a.javascript(info) else { panic!("a JSX header") };
               // The callee and the tag, then what the header counts.
               let expected = 2 + usize::from(header.spread) + header.props.len as usize + header.children as usize + usize::from(header.key);
               assert_eq!(self.operands.len() - start, expected, "the operands the JSX header counts");
               let id = plain::node(
                   a,
                   View::JJsx {
                       values: &self.operands[start..],
                       info,
                   },
                   u16::from(has_children),
               );
               self.cut(start, id)
           }

   In the table at the top of rows.rs the cell of `jsx_element` ends
   "then `plain::node` with the operands since the mark as the list and
   the children bit as `aux`: one step and one per operand, the callee
   one of them", and the cell of "a list constructor" loses "the
   children bit of `jsx`,". In js_tests.rs the two calls of `r.jsx(`
   (the JSX case of the read-back test and
   `a_jsx_element_without_the_operands_of_its_header_is_refused`)
   build the callee `u.f` with `r.var`, push only the tag `u.x`, and
   call `r.jsx_element(&mut u.b, callee, mark, info, ..)`; their
   expected values and the panic message do not change.

End state, run from compiler-rust and paste the output. On the design
turn's throw-away head each printed what is given; on trunk before the
slice, what is in brackets:
- `rg -n 'B::at\(|external_values|self\.scratch' src/bir/lower/jsx.rs`
  prints nothing [11 lines].
- `rg -c 'fn jsx\(' src/bir/lower/js.rs src/bir/j/rows.rs` prints
  nothing [`rows.rs:1` and `js.rs:1`].
- `rg -n 'jsx_element\(' src/bir/lower src/bir/j | wc -l` prints 7 [4].
- `rg -n 'copy_members\(' src/bir/lower/jsx.rs` prints one line [none].
- `rg -n 'external_values' src/bir/lower/*.rs` prints lines of
  `ffi_args.rs`, `external.rs` and `mod.rs` only [and of `jsx.rs`]. The field
  stays: the splice of `ffi_args.rs` uses it.
- `python3 ../scripts/count_lowering_ids.py | grep '^| total' | head
  -1` printed `| total | 16033 | 89 | 15 | 26 | 3 | 2 | 11 | 6 | 2 | 2
  | 0 | 0 | 0 | 146 |`, and the row of `jsx.rs` `| 273 | 2 | 0 | 0 | 0
  | 0 | 0 | ...` (its `at` 4 to 0). Paste yours and explain any
  difference in columns four to thirteen.

Tests. You edit the two places of js_tests.rs and nothing else in a
test; no expected value changes, in particular not in the tests of
jsx.rs, of oracle_tests.rs and of unit.rs (allocation counts 86, 103,
86, 156; `size_of::<Rows>()` 416; `Row` of export.rs 8 bytes). The
filters stay at 579, 71 and 40: this slice adds no test, because
`jsx_element` and `copy_members` have theirs (rows_tests.rs,
builder_tests.rs), and the tests of jsx.rs and the JSX cases of
oracle_tests.rs run the two converted functions against the legacy
code. If a JSX test fails with ids or runtime modules in another
order, the callee was built before the key: stop and compare with the
code above.

Cost notes. From compiler-rust: `python3
../scripts/check_lowering_cost_docs.py --base
origin/ocaml-to-rust-rewrite`; the design turn's build read
`changed/new=5; missing/generic=0; removed=0`, and the last figure
before `removed` must be 0.

Every commit: `cargo clippy --manifest-path compiler-rust/Cargo.toml
--all-targets -- -D warnings` and `RUSTDOCFLAGS="-D warnings" cargo doc
--manifest-path compiler-rust/Cargo.toml --no-deps`, both clean.

Gates of the pull request, beside those of the common blocks: the
three filters with the counts above; CI `Backend bridge coverage` at
zero differences and the parity jobs for JavaScript, the standard
library and genType green, read before the pull request is marked
ready; CI `Instruction count` read and reported (the default build
does not reach the lowering, so the figure is the job's spread; above
+0.05% on two runs, stop and report). The body of the pull request
lists the two edited tests and says that no attribute was added.

Run by the design turn, in a copy that was not pushed: these two
commits one after the other; after the first the lowering filter read
579 and the self-test 26; after the second the three filters read 579,
71 and 40, with clippy and `cargo doc` clean and the cost-note check at
zero; 54 lines added and 100 removed in four files. Not run: `Backend bridge
coverage`, the parity suites, `Instruction count`, check mode, and so
the order of the runtime modules a keyed element registers was checked
by the lowering's tests only.

Shortcuts that count as failure, beside the common lists: `B::at`,
`B::node` or `B::from_node` in jsx.rs; `Js::jsx` kept, or kept under
`#[cfg(test)]`; a `Vec` of the operands in `compile_jsx`, or
`State::external_values` or `State::scratch` used there; the callee
built before the key or before the operands; a slot reserved at the
mark; a second walk of the key's chain to copy it, or `copy_leaf` and
`copy_cold` called from jsx.rs; `duplicate_jsx_key` copying before its
shape check has passed; `jsx_element` renamed to `jsx`; an edit of
`jsx_tag`, `printed_form`, `jsx_key`, `jsx_callee`, of ffi_args.rs,
export.rs, js_stmt.rs, rows_stmt.rs, out.rs or src/emit; the field
`external_values` removed.
```


Probe of T6x-c1 (a throw-away conversion; issued verbatim, with the
common block of phase C; no build prompt for T6x-c1 to f exists until
each has its probe and its design turn):

```text
Task: probe row T6x-c1 of the cut of T6x (compiler-rust/docs/
THREE_TREES.md 11.4, "T6x: the cut" and "T6x-b: an output's value, as
built" (i)). This is a measurement, not a slice: its pull request is a
draft that is never merged, and its body is the report.

Start from trunk with T6x-b3b merged (`rg -n 'fn decide<B: JsStmt>'
compiler-rust/src/bir/lower/close.rs` shows one line). Branch from it;
open the draft pull request against ocaml-to-rust-rewrite after the
first push, titled "Probe: T6x-c1 (not for merge)".

Convert the row: in prim.rs, prim_cmp.rs, prim_block.rs, konst.rs,
record.rs, import.rs, args.rs and call.rs a value is a `B::E` from the
place it is made to the place it is consumed. `values` holds handles
from `sequence_arguments` on. A function of these files that only
these files call takes and returns handles. A function another file
calls keeps its signature (it is T6x-d's) and you wrap at the call,
unless keeping it forces a turn-back and a wrap of the same value in
one function: then change it, with its callers, and list it in (3).

Rules of a probe:
- You add nothing to the traits `Js` and `JsStmt` and nothing to
  src/bir/j or src/emit. Where the conversion needs something the
  interface does not give, write the turn-back that works today under
  a comment `// PROBE-GAP n: <what is needed, in one line>` and go on.
  Number the gaps in order of appearance.
- No cost notes, no changelog discipline beyond one fragment, no `allow`
  attribute. A test is edited only so that it compiles; no expected
  value changes. If one would, leave the test failing and report it.
- One commit per step below, pushed when made. After each: `cargo
  check --all-targets --manifest-path compiler-rust/Cargo.toml`, and
  `cargo test --manifest-path compiler-rust/Cargo.toml --lib
  bir::lower` and `--lib bir::j` (never the whole suite). A step that
  does not compile alone is merged with the next and the report says
  so.
- Do not run `Instruction count`, check mode or the parity suites, and
  do not wait for CI.

Steps:
1. The storage: `State::argument_values` and the `values` parameter of
   `sequence_arguments` and of `finish_primitive_values` hold `B::E`
   (`Vec<Option<B::E>>` if a value is moved out of the middle, `Vec<
   B::E>` if not: say which and why). The field is taken and given
   back in call.rs and prim.rs only; the other files read its capacity
   in a test. What is made from it leaves the row (the `values` slice
   `finish_self_call` of tail.rs takes, the pool list `compile_js_call`
   and the iterator `compile_jsx` take): wrap at those calls and count
   the wraps by file.
2. prim.rs: the reads `B::from_node(values[i])` become moves or reads
   in place; `push_values`, `bin_of`, `first_value`.
3. konst.rs (`constant_children`, `constant_values`), record.rs,
   import.rs, prim_cmp.rs, prim_block.rs.
4. args.rs (`Evaluation::values`, `evaluate_now`) and call.rs
   (`call_reversed`, `eta_arguments`, the wrap of `values[0]`).

The report (the body of the draft pull request), with these sections:
(1) Size: `git diff --stat` against trunk; changed lines per commit,
    production and test apart; whether the row is under 600 lines and,
    if not, the cut the commits give, each part compiling and passing
    at its place.
(2) PROBE-GAPs: for each, the file, function and line, what is needed,
    what you wrote instead, and the signature you would propose with
    its cost on rows and on a builder that owns its nodes.
(3) Signatures: every function whose signature changed, before and
    after, with its callers in other files; which changes the row
    could not avoid and which you made to remove a turn-back.
(4) `values`: what its element type became and why; every place a
    value is read from it more than once (an index read twice, a value
    read and then moved, a slice passed on while an element is used),
    with the line on trunk and what you did there. This is the table
    of "one value, two consumers" for this row.
(5) The shared field: for `argument_values`, `external_values`,
    `constant_values` and `scratch`, the files that use each and
    whether step 1 could change the type without editing a function of
    a file that is not of this row. Say plainly whether c1 can be
    built beside c2 to c4, or what must come before them.
(6) Counts: `python3 ../scripts/count_lowering_ids.py | grep '^|
    total' | head -1` from compiler-rust before and after, and the row
    of each file of this row before and after; the marks
    `assume_strict` after `Js::var` in args.rs, call.rs and import.rs
    that you deleted (they write a flag the node has).
(7) Tests: the counts of the two filters on trunk and after each
    commit; every test edited to compile, with what changed; the four
    allocation counts of unit.rs and every `size_of` assertion, held
    or not.
(8) What surprised you: anything the row's description or this prompt
    says that the code contradicts.
(9) What you did not run.
```


## 12. Risks and what was not measured

Not measured:

- The cost of the result tables and of the builder's facts table. Both are
  written per node; the savings of section 9 that depend on them are ranges
  for that reason.
- The cost of replaying naming events (section 2).
- How often the JavaScript count differs from the level L count at a
  tail-call site (1.1). One example exists (tested); the frequency on the
  corpora decides between the splice and the simpler form. T4 counts it.
- Filling typed-tree nodes inside the checker (section 6).
- Anything on the 3,735-module application. Every figure of this document is
  from `tests/tests`.
- Memory. The typed tree's size per module was not counted.
- Wall time. Only instructions.

Risks:

1. **Scope-close decisions reorder what the lowering creates.** The legacy
   passes create identifiers (`x_0`, the record-rest binders) after lowering;
   T1 creates them during it. Names depend on first print and, in one case,
   on creation order (section 2, third case). The gate compares printed text,
   so a difference shows; the fix may need the fresh identifiers' `order` to
   be assigned at scope close.
2. **The builder's facts drift from the nodes.** A rule that changes a node
   in place must update its row. The validator has to recompute the flags of
   every node of a unit in debug builds and compare.
3. **Two producers in the checker.** From T8 to T11 the checker writes the
   tree and the tables. The agreement check of T8 is what keeps them equal;
   T11 must not land before every batch reader is switched.
4. **Order of diagnostics** in T2 and T7: frontend errors precede type errors
   today because the frontend runs first. Keeping the validation walks keeps
   that; a direct rule that raises a frontend error from the checker would
   not.
5. **Editor tooling keeps the old path longest.** Until T12 a tooling session
   builds the typed tree, so the checker keeps both outputs. If T12 is never
   done, the typed tree's code stays for tooling only.
6. **oxc's `node_id` and the scoping hook** are internals of version 0.158
   (pinned in `Cargo.toml`). An upgrade that removes either breaks sections 2
   and 3; the fallback is a parallel index assigned by the builder and names
   written into the nodes at scope close through the slots the log records.
7. **The pattern port (T10) may not pay.** Patterns are a part of 1.28%; the
   port touches 14,500 lines. It is last but two for that reason.

## 13. Where documents and code disagree

| Document | Says | Code |
| --- | --- | --- |
| AGENTS.md, "Running Rewatch Directly" | builds write `.cmi`, `.cmt`, `.cmti` | none is written: `rewatch/src/build/tooling.rs`, `plan.rs`; tooling type-checks on demand |
| The task's background | the rewrites produce a rewritten copy of the parse tree | the mapper appends to the same `ParseArena` and rebuilds the ancestors of each rewritten node; the nodes as parsed stay (section 5) |
| BACKEND_REDESIGN C.3, row J4 | shake is `uses == 0` with a cascade | `live_idents` is reachability from exports and effectful statements; an unused cycle is removed (1.4) |
| BACKEND_REDESIGN C.3, row J1 | reads `uses` and `PURE` | the count is of JavaScript occurrences before the pass, which level L does not have (1.1, tested) |
| BACKEND_REDESIGN 0.2 item 5 and E.3 | names are chosen by a scope walk over the finished tree | pull request #175 measured that walk at 56 M to 68 M on `tests/tests`, against 23 M for code generation |
| FRONTEND_REWRITES, inventory | nine rows name the parser as a candidate destination | with one tree for the formatter and the compiler no rewrite can go there (section 5) |
| CHECKER_REDESIGN A.7 | genType reads "the typed tree, the saved signature and the raw signature" | correct; in addition `unit_reads` walks the whole typed tree in every build that collects reads (1.16%), which A.7 lists under incremental build without naming the walk |
| Section 5 and the prompt of T2 (11.2), step 6 | the unused-attribute sweep needs a predicate "this attribute is consumed by a built-in" computed from the tree as written | the sweep resolves each expression through `ParseArena::expanded`, so it walks the expansions, where a consumed attribute is absent as it was in the rebuilt tree; no predicate exists |
| The prompt of T2 (11.2), step 3 | `type_expect` and `type_exp` resolve in their expression entry | both take `&Expression`, not a handle; the checker resolves where it reads a handle (`ParseArena::get_expanded_expr`) |
| Section 11, row T2 | the instruction count falls by at least 1% | it falls by 0.97% on `tests/tests` and 0.69% on a 3,735-module application; the rebuild alone was 0.70% of the build (FRONTEND_REWRITES, "Expansions instead of rebuilt ancestors") |
| Section 5 | every ancestor of a rewritten construct is new | also every expression without a certificate was cloned and pushed again, rewritten construct below it or not; and a node still gets a copy when its pattern, type, module or attribute child changes its handle, because those mappers still rebuild |
| Section 5, direct rows and row T7 | direct rows need matching arms in the core IR builder | T7 retains the existing typed conditional, match, constant and application nodes, so A–D require no core IR builder change |
| FRONTEND_REWRITES, attribute handling | integer `l` expressions/patterns ignore attributes | the pattern mapper already rewrote attributes; T7 now uses the ordinary attribute traversal for both and retains the source literal |
| T7 deletion check and shared helper names | row-specific mapper code is deleted | `rewrite_expr`, `rewrite_pattern` and `rewrite_fun` are shared traversals, not row-specific helpers; delete their direct-row arms, not unrelated rewrites. The record-let helper also handled `let?`, which remains as `rewrite_unwrap_binding_let` |
| T7 async/await direct rule | the existing checker can construct the same typed tree without per-node storage or synchronization | the previous full-location ghost-copy API boxed a location under a write lock; T7 adds an immutable ghost-index view and returns a 12-byte location value, so promise typing needs neither allocation nor locking |
| T7 expansion measurement | direct-arm visits measure independently removable expansion entries | 358 arm visits overlap with 12 record-rest/type rewrites and 24 async parameter/type rewrites; removing await also removes 7 brace copies. The measured net reduction is 329, and all 3,038 unrelated entries are unchanged (FRONTEND_REWRITES, same-base census) |
| Section 1.3 | hoisting and substitution happen while lowering, removal when the statements are copied | the tail-call pass drops a dead block binding before it is materialised, and record rest reads the field reads substitution would replace; both tested or read in 11.4 (findings 5 and 6), so they happen at the close |
| Section 1.1 | the site is a final `return f(args)` of a statement-stack run | the pass finds sites on the tree the flatten pass wrote: inside a returned conditional the lowering writes no such statement (11.4, finding 1, tested) |
| Section 1.3, 1.5 | a declaration with no remaining use is removed at scope close | inlining from an outer scope can take the last use later (11.4, finding 3, tested) |
| 11.4, "The design" and the re-cut table | step A runs in the lowering, before P1 and P2, and the new side then drops P3 | P2 reads the bindings around a reference and P1 maps the predicate of an `if` it did not create: the text differs in both cases (11.4, "T4c design" (c), tested), and a copied function doubles C0 of its variables after their runs closed ((b), read) |
| Row T4 and the T4 prompt | export coercion on rows is the sixth step, after the scope-close decisions | every top-level status reads the export set and counts taken after coercion (11.4, finding 2); it is the first step |
| 11.4, finding 2 and "The design" | per reference, the statement it is in and whether its position is safe are recorded where the reference is lowered | a reference is built before its parent and before its statement has a slot (reserved slots and held runs are filled later), so only the site (node, next) is recorded there; the row and the position are read through the parent links at the end of the top level ("T4a as built") |
| BACKEND_LOWERING 8.1 step 4 and 8.2 | export extraction and coercion are in the shared tail; the unit's last value is the export block, carried for `extract_toplevel_exports` | the lowering extracts, coerces and resolves the exports itself; the shared tail is the six passes; S3.9b is done as T4a, first of the T4 slices, not last |
| `move_same_name_export_alias_to_export_tail` (`js_shake.rs`) | several conditions block a literal binding in particular cases | two of them together block every literal binding, so the others are unreachable ("T4a as built") |
