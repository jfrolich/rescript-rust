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

#### Re-cut: one legacy step leaves the new side per slice

The commit order of the T4 prompt (block facts, dead declarations, record
rest, inlining, rows, gate) cannot be gated step by step: a decision moved
ahead of a legacy pass that still runs changes that pass's input (the
boundary finding; findings 1, 2, 5, 6). In legacy order every step can: the
new side drops exactly the pass whose decisions moved, and the two printed
texts stay equal.

| Slice | Moves into the lowering | New side stops running | Needs |
| --- | --- | --- | --- |
| T4a | Export extraction and coercion on top-level rows (`bir/lower/export.rs`, S3.9b), with the position facts of finding 2 | `coerce_lowered_output` | - |
| T4b | P1 as rules applied where a run is copied; or the proof that sites can be read through P1's reshaping and that P1 commutes with T4c to T4e | `apply_js_flatten_pass`, or nothing | - |
| T4c | Step A, late marks, late zero, graves, the counter | `apply_js_tailcall_inline_pass` | T4a, T4b |
| T4d | Step B | `apply_js_record_rest_pass` | T4c |
| T4e | Steps C and D | `apply_js_flatten_and_mark_dead_pass` | T4d |
| T4f | The shake as a filter over the rows | `apply_js_shake_pass` | T4a, T4e |

`apply_external_shadow_pass` (P2) rewrites references to JavaScript globals
that a binding shadows. It changes no count of a declared variable, but it
reads which bindings exist, so it has to see the declarations P3 and P5
remove; it stays until the names are decided in the lowering (T5).

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
| Row T4 and the T4 prompt | export coercion on rows is the sixth step, after the scope-close decisions | every top-level status reads the export set and counts taken after coercion (11.4, finding 2); it is the first step |
