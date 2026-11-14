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
include the statements hoisted out of it. This is the only place where an
expression is read for a reference, and `adopted_nodes` reports what it
costs. The replay reads statement lists and scope rows, never an
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
copies left out) is required to be zero as well: a wrong free list changes a
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
- `names::adopt`: the one read of an expression (G10), at `apply_with_arity`
  and `external_dispatch`.
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
   fragment. Cost, only in such a unit: one read of the parent per
   reference, one step per member above it, and per JSX element one step
   per property key (twice for a fragment). Not a walk below a node: the
   reference's ancestors and the element's own keys. The application:
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
8. *The comparison* (`compare_with_pass`) is unchanged. `compare_oracle`
   compares each rule test in both ways of printing JSX.

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
units are those the naming pass rejects, for its own reasons. Two were
seen on these corpora: the runtime's `Stdlib_Dict.res` ("delete call
syntax") and `jsx_preserve_cases.res` of tests/tests ("JSX sequence
container").

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
