# Executed checker-departure search

## Scope and method

This is a bounded source-program search, not a proof of equivalence. The compilers
were built from `0b175b7d0`; the documentation branch subsequently fast-forwarded to
`772fca5d2`, whose additional change is in the separate `tc` rewrite, not the
`types` checker investigated here. No compiler source or test was modified.

51 candidates were run, at least six per place, in the order D1–D5, E1–E3.
Every candidate below is complete; a trailing newline was written to every source.
Empty fences denote literally empty output, not omitted output. Matching outputs
are printed once. JavaScript is on stdout for this invocation and is compared too.
A WITNESS denotes an observed compiler difference, not necessarily proof of the
proposed internal cause. REACHED means the indicated call/branch ran, not that
all stronger mutation-survival conditions were satisfied. NOT REACHED applies
only to the listed candidates and the precise failure branch.

### Builds and reference calibration

```sh
export PATH="$HOME/.cargo/bin:$PATH"
cargo build --release --manifest-path rewatch/Cargo.toml
eval $(opam env)
dune build --root .
bash scripts/rust_compiler_shims.sh release
export ROOT="$PWD"
RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime" \
  rewatch/target/release/rescript build-reference \
  --bsc "$ROOT/_build/install/default/bin/bsc" packages/@rescript/runtime
PARITY_JOBS=1 bash scripts/test_error_output_parity.sh \
  --release --compiler-only apply_non_function.res
```

Build result: Rust `Finished release profile [optimized] target(s) in 6m 43s`;
OCaml exited 0 with empty stdout/stderr. Runtime setup printed:

```text
OCaml reference build: 113 of 113 modules built
```

The first calibration attempt failed because reference runtime interfaces were
absent (`The module or file Pervasives can't be found.`). After the reference
runtime build, the parity script reported (terminal color escapes omitted here):

```text
Compiler diagnostics parity

Error output parity summary
  total:  2
  pass:   2
  fail:   0
SUCCESS: OCaml and Rust diagnostic output match for tested fixtures.
```

Existing fixture `tests/build_tests/super_errors/fixtures/apply_non_function.res`:

```rescript
let x = 1

let y = x(2)
```

Both compilers exited 2, stdout empty, stderr verbatim:

```text

  We've found a bug for you!
  tests/build_tests/super_errors/fixtures/apply_non_function.res:3:9

  1 │ let x = 1
  2 │ 
  3 │ let y = x(2)
  4 │ 

  This can't be called, it's not a function.
  It has type: int

```

### Candidate commands

Each candidate lives in its own directory created with `mktemp -d` under `$TMPDIR`,
with an empty `src/` directory and this `rescript.json`:

```json
{"name":"checker-probe","sources":["."]}
```

From that directory, the single-file commands are precisely the fixture flags:

```sh
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w +A -bs-jsx 4 -color never Main.res
timeout 10 "$ROOT/rewatch/target/release/bsc" -w +A -bs-jsx 4 -color never Main.res
```

The runner used Python `subprocess.run(..., capture_output=True, timeout=10)`
to apply the same timeout while retaining stdout, stderr and exit status separately.
Before each compiler run it deleted only the candidate's generated `.cm*` files.
For the two-file candidates D1-6 and D2-6, the script's `prepare_cached_case`
reference-interface prebuild is used before **each** compiler:

```sh
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w -A -color never Main.resi
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w +A -bs-jsx 4 -color never -I . -bs-read-cmi Main.res
# Repeat the reference-interface prebuild before the Rust invocation:
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w -A -color never Main.resi
timeout 10 "$ROOT/rewatch/target/release/bsc" -w +A -bs-jsx 4 -color never -I . -bs-read-cmi Main.res
```

Both reference prebuilds exit 0 with empty stdout/stderr. `-I .` is necessary
because the reference compiler does not find the local interface otherwise.
Without `-bs-read-cmi`, the initial implementation runs did not enforce interface
inclusion; those were setup probes, not valid inclusion evidence. The subsequent
missing-`-I` attempt is preserved below separately and is not classified as a
checker witness.

## Summary

| Place | Verdict | Candidates |
| --- | --- | ---: |
| D1 | REACHED, NO DIFFERENCE SEEN | 6 |
| D2 | WITNESS | 7 |
| D3 | NOT REACHED | 6 |
| D4 | REACHED, NO DIFFERENCE SEEN | 6 |
| D5 | NOT REACHED | 8 |
| E1 | REACHED, NO DIFFERENCE SEEN | 6 |
| E2 | REACHED, NO DIFFERENCE SEEN | 6 |
| E3 | REACHED, NO DIFFERENCE SEEN | 6 |
| E4 | WITNESS, FIXED | 6 |

## D1 — REACHED, NO DIFFERENCE SEEN

Module record-signature inclusion calls `equal` (`compiler-rust/src/types/ctype.rs:11051-11066`; `compiler/ml/ctype.ml:3361-3376`), and a field comparison must fail after alias expansion changes shared graph state. The subsequent per-field diagnostic comparisons or duplicate-field retry must observe that state for a difference to become visible.

All six candidates hit `equal` and return false at least once; D1-2, D1-3, D1-5 and D1-6 also hit substitution. These counts establish equality failure, not a persistent mutation or a causal connection between the substitution and equality; no impossibility claim is made.

### D1-1 — outputs agree

`Main.res`:

```rescript
module M: {type t = {a: int, b: int}} = {type t = {a: string, b: int}}
let later = 1
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (379 bytes):

```text

  We've found a bug for you!
  Main.res:1:41-70

  1 │ module M: {type t = {a: int, b: int}} = {type t = {a: string, b: int}}
  2 │ let later = 1
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:42-69):
    type t = {a: string, b: int}
  
  Expected declaration (Main.res:1:12-36):
    type t = {a: int, b: int}
  
  The types for field a are not equal.

```

Debugger hit counts:

```text
{"equal": 8, "equal_false": 4, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 8, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D1-2 — outputs agree

`Main.res`:

```rescript
type a = int
module M: {type t = {x: a, y: int}} = {type t = {x: int, y: string}}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (374 bytes):

```text

  We've found a bug for you!
  Main.res:2:39-68

  1 │ type a = int
  2 │ module M: {type t = {x: a, y: int}} = {type t = {x: int, y: string}}
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:2:40-67):
    type t = {x: int, y: string}
  
  Expected declaration (Main.res:2:12-34):
    type t = {x: a, y: int}
  
  The types for field y are not equal.

```

Debugger hit counts:

```text
{"equal": 8, "equal_false": 4, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 10, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D1-3 — outputs agree

`Main.res`:

```rescript
type a<'a> = ('a, int)
module M: {type t = {x: a<int>, y: int}} = {type t = {x: (int, string), y: int}}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (417 bytes):

```text

  We've found a bug for you!
  Main.res:2:44-80

  1 │ type a<'a> = ('a, int)
  2 │ module M: {type t = {x: a<int>, y: int}} = {type t = {x: (int, string), 
    │ y: int}}
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:2:45-79):
    type t = {x: (int, string), y: int}
  
  Expected declaration (Main.res:2:12-39):
    type t = {x: a<int>, y: int}
  
  The types for field x are not equal.

```

Debugger hit counts:

```text
{"equal": 8, "equal_false": 4, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 14, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 8, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D1-4 — outputs agree

`Main.res`:

```rescript
module M: {type t<'a> = {a: 'a, b: 'a}} = {type t<'a> = {a: 'a, b: int}}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (361 bytes):

```text

  We've found a bug for you!
  Main.res:1:43-72

  1 │ module M: {type t<'a> = {a: 'a, b: 'a}} = {type t<'a> = {a: 'a, b: int}}
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:44-71):
    type t<'a> = {a: 'a, b: int}
  
  Expected declaration (Main.res:1:12-38):
    type t<'a> = {a: 'a, b: 'a}
  
  The types for field b are not equal.

```

Debugger hit counts:

```text
{"equal": 8, "equal_false": 4, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D1-5 — outputs agree

`Main.res`:

```rescript
type a = int
type t = {"x": a, "x": string}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (169 bytes):

```text

  We've found a bug for you!
  Main.res:2:24-29

  1 │ type a = int
  2 │ type t = {"x": a, "x": string}
  3 │ 

  Method 'x' has type string, which should be a

```

Debugger hit counts:

```text
{"equal": 2, "equal_false": 2, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 2, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D1-6 — outputs agree

`Main.resi`:

```rescript
type a = int
type t = {x: a, y: int}
```

`Main.res`:

```rescript
type a = int
type t = {x: int, y: string}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (380 bytes):

```text

  We've found a bug for you!
  Main.res:2:1-28

  1 │ type a = int
  2 │ type t = {x: int, y: string}
  3 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:2:1-28):
    type t = {x: int, y: string}
  
  Expected declaration (Main.resi:2:1-23):
    type t = {x: a, y: int}
  
  The types for field y are not equal.

```

Debugger hit counts:

```text
{"equal": 10, "equal_false": 4, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 9, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 5, "subst_body_failure": 0, "subst_param_failure": 0}
```

## D2 — WITNESS

Module value inclusion invokes `moregeneral` with `inst_nongen=true`, allowing a weak implementation variable into `moregen_occur` (`compiler-rust/src/types/ctype.rs:9629-9674, 9920-9926`; `compiler/ml/ctype.ml:2901-2938`). A later abstract subject type must fail checked lowering while passing occurrence checking, and inclusion must then use the result of the additional variable link.

D2-1, D2-4, D2-5 and reduced D2-7 are accepted only by Rust; each hits `moregen_occur` and the expanding lowering retry once. D2-6 is a separate reverse-direction interface witness, not evidence that the swallowed lowering error caused that mismatch: its trace never enters `moregen_occur`. D2-7 is the smallest single-file witness found; D2-6 is the two-file witness as tested.

### Fixed

Two commits remove the D2 witnesses; all seven candidates were rerun with
both compilers after them, and every one now agrees.

- `24d7bee27` makes `moregen_occur` (`compiler-rust/src/types/ctype.rs`)
  return the failure of its checked level update, as OCaml's raising
  `update_level` does (`compiler/ml/ctype.ml:2901-2919`), so `moregeneral`
  answers false before the weak variable is linked. D2-1, D2-4, D2-5 and
  D2-7 are now rejected with OCaml's "Signature mismatch"; they are the
  super_errors fixtures `weak_variable_module_constraint_escape_used_later`,
  `_array`, `_local` and `weak_variable_module_constraint_escape`.
- `381bc9144` deletes the driver's `apply_moregen_constraints`, which linked
  each weak variable of an implementation to the stored interface's own type
  node (`Main.t`) before the inclusion check; OCaml has no such pass
  (`compiler/ml/typemod.ml:1797-1801`). D2-6 now builds with OCaml's
  JavaScript; it is `tests/tests/src/weak_variable_interface_instantiation`.
- D2-2 and D2-3 agreed before and still agree (both build, same JavaScript).

### D2-1 — WITNESS

`Main.res`:

```rescript
let r = ref(None)
module M: {type t
let v: option<t>} = {type t
let v = r.contents}
let later = r.contents
```

#### OCaml

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (365 bytes):

```text

  We've found a bug for you!
  Main.res:3:21-4:19

  1 │ let r = ref(None)
  2 │ module M: {type t
  3 │ let v: option<t>} = {type t
  4 │ let v = r.contents}
  5 │ let later = r.contents
  6 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:4:5):
    let v: option<'_weak1>
  
  Expected declaration (Main.res:3:1-16):
    let v: option<t>

```

#### Rust

`Main.res` exit status: **0**.

stdout (241 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let v = r.contents;

let M = {
  v: v
};

let later = r.contents;

exports.r = r;
exports.M = M;
exports.later = later;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 0, "level_retry": 1, "moregen_occur": 1, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-2 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M: {type t = int
let v: option<t>} = {type t = int
let v = r.contents}
let later = r.contents
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (241 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let v = r.contents;

let M = {
  v: v
};

let later = r.contents;

exports.r = r;
exports.M = M;
exports.later = later;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 1, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-3 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M: {type t
let v: option<t>} = {type t = int
let v = r.contents}
let later = r.contents
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (241 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let v = r.contents;

let M = {
  v: v
};

let later = r.contents;

exports.r = r;
exports.M = M;
exports.later = later;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 0, "level_retry": 0, "moregen_occur": 1, "nullary_lower": 1, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 2, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-4 — WITNESS

`Main.res`:

```rescript
let r = ref([])
module M: {type t
let v: array<t>} = {type t
let v = r.contents}
let later = r.contents
```

#### OCaml

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (360 bytes):

```text

  We've found a bug for you!
  Main.res:3:20-4:19

  1 │ let r = ref([])
  2 │ module M: {type t
  3 │ let v: array<t>} = {type t
  4 │ let v = r.contents}
  5 │ let later = r.contents
  6 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:4:5):
    let v: array<'_weak1>
  
  Expected declaration (Main.res:3:1-15):
    let v: array<t>

```

#### Rust

`Main.res` exit status: **0**.

stdout (234 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: []
};

let v = r.contents;

let M = {
  v: v
};

let later = r.contents;

exports.r = r;
exports.M = M;
exports.later = later;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 0, "level_retry": 1, "moregen_occur": 1, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-5 — WITNESS

`Main.res`:

```rescript
let f = () => {let r = ref(None)
module M: {type t
let v: option<t>} = {type t
let v = r.contents}
r.contents}
```

#### OCaml

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (369 bytes):

```text

  We've found a bug for you!
  Main.res:3:21-4:19

  1 │ let f = () => {let r = ref(None)
  2 │ module M: {type t
  3 │ let v: option<t>} = {type t
  4 │ let v = r.contents}
  5 │ r.contents}
  6 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:4:5):
    let v: option<'_weak1>
  
  Expected declaration (Main.res:3:1-16):
    let v: option<t>

```

#### Rust

`Main.res` exit status: **0**.

stdout (121 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f() {
  
}

exports.f = f;
/* No side effect */
```

stderr (211 bytes):

```text

  Warning number 32
  Main.res:3:1-16

  1 │ let f = () => {let r = ref(None)
  2 │ module M: {type t
  3 │ let v: option<t>} = {type t
  4 │ let v = r.contents}
  5 │ r.contents}

  unused value v.

```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 0, "level_retry": 1, "moregen_occur": 1, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-6 — WITNESS

`Main.resi`:

```rescript
type t
let v: option<t>
```

`Main.res`:

```rescript
type t
let r = ref(None)
let v = r.contents
```

#### OCaml

`Main.res` exit status: **0**.

stdout (120 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r;

let v = r;

exports.v = v;
/* No side effect */
```

stderr (0 bytes):

```text
```

#### Rust

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (328 bytes):

```text

  We've found a bug for you!
  Main.res:3:5

  1 │ type t
  2 │ let r = ref(None)
  3 │ let v = r.contents
  4 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:3:5):
    let v: option<Main.t>
  
  Expected declaration (Main.resi:2:1-16):
    let v: option<t>

```

Debugger hit counts:

```text
{"equal": 3, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D2-7 — WITNESS

`Main.res`:

```rescript
let r = ref(None)
module M: {type t
let v: option<t>} = {type t
let v = r.contents}
```

#### OCaml

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (334 bytes):

```text

  We've found a bug for you!
  Main.res:3:21-4:19

  1 │ let r = ref(None)
  2 │ module M: {type t
  3 │ let v: option<t>} = {type t
  4 │ let v = r.contents}
  5 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:4:5):
    let v: option<'_weak1>
  
  Expected declaration (Main.res:3:1-16):
    let v: option<t>

```

#### Rust

`Main.res` exit status: **0**.

stdout (193 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let v = r.contents;

let M = {
  v: v
};

exports.r = r;
exports.M = M;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 0, "level_retry": 1, "moregen_occur": 1, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

## D3 — NOT REACHED

Expanding a parameterized abbreviation calls `subst_with_memo` (`compiler-rust/src/types/ctype.rs:7361-7439`; `compiler/ml/ctype.ml:1113-1135`), where either the fresh stub/body or fresh parameter/argument unification must fail. Later checking must observe the forced link or subsequent parameter writes that Rust performs after that failure.

D3-1, D3-2, D3-4 and D3-5 enter substitution, but neither post-failure link breakpoint fires in any candidate. Cyclic abbreviations are rejected during declaration checking; the noncyclic aliases do not satisfy the failing-stub or incompatible-fresh-parameter conditions at ctype.rs:7422 and :7429. This is a bounded search result, not proof that these branches are unreachable for every source program.

### D3-1 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = option<t<'a>>
let f = (x: t<int>) => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (168 bytes):

```text

  We've found a bug for you!
  Main.res:1:1-30

  1 │ type rec t<'a> = option<t<'a>>
  2 │ let f = (x: t<int>) => x
  3 │ 

  The type abbreviation t is cyclic

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 2, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D3-2 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = ('a, option<t<'a>>)
let f = (x: t<int>): t<string> => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (185 bytes):

```text

  We've found a bug for you!
  Main.res:1:1-36

  1 │ type rec t<'a> = ('a, option<t<'a>>)
  2 │ let f = (x: t<int>): t<string> => x
  3 │ 

  The type abbreviation t is cyclic

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 2, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D3-3 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = {next: option<t<'a>>, value: 'a}
let f = (x: t<int>): t<string> => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (406 bytes):

```text

  We've found a bug for you!
  Main.res:2:35

  1 │ type rec t<'a> = {next: option<t<'a>>, value: 'a}
  2 │ let f = (x: t<int>): t<string> => x
  3 │ 

  This has type: [1;31mt<int>[0m
  But it's expected to have type: [1;33mt<string>[0m
  
  The incompatible parts:
    [1;31mint[0m vs [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D3-4 — outputs agree

`Main.res`:

```rescript
type a<'a> = ('a, 'a)
let f = (x: a<int>): (int, string) => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (437 bytes):

```text

  We've found a bug for you!
  Main.res:2:39

  1 │ type a<'a> = ('a, 'a)
  2 │ let f = (x: a<int>): (int, string) => x
  3 │ 

  This has type: [1;31ma<int>[0m [2m(defined as[0m [1;31m(int, int)[0m[2m)[0m
  But it's expected to have type: [1;33m(int, string)[0m
  
  The incompatible parts:
    [1;31mint[0m vs [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D3-5 — outputs agree

`Main.res`:

```rescript
let f = () => {module M = {type t = int
type a<'a> = (t, 'a)}
let x: M.a<string> = (1, "x")
x}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (149 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f() {
  return [
    1,
    "x"
  ];
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 3, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 6, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D3-6 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = t<array<'a>>
let f = (x: t<int>) => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (167 bytes):

```text

  We've found a bug for you!
  Main.res:1:1-29

  1 │ type rec t<'a> = t<array<'a>>
  2 │ let f = (x: t<int>) => x
  3 │ 

  The type abbreviation t is cyclic

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

## D4 — REACHED, NO DIFFERENCE SEEN

A repeated object field calls `equal` and retries with `unify` on false (`compiler-rust/src/types/typecore.rs:3525-3564`; `compiler/ml/typetexp.ml:595-607`). Equality must mutate an alias expansion before failing, and retry unification or the resulting diagnostic must expose the surviving mutation.

All six repeated-field candidates hit equality failure and the subsequent `unify` call; D4-1 and D4-2 constrain a parameter successfully, while D4-3 through D4-5 reject incompatible duplicates. Equality failure and the retry call are measured, but the stronger mutation-survival condition is not established.

### D4-1 — outputs agree

`Main.res`:

```rescript
type t<'a> = {"x": 'a, "x": int}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (156 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 1, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 1, "object_retry": 1, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 1, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D4-2 — outputs agree

`Main.res`:

```rescript
type a<'a> = ('a, int)
type t<'a> = {"x": a<'a>, "x": (string, int)}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (156 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 1, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 4, "object_retry": 1, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 5, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D4-3 — outputs agree

`Main.res`:

```rescript
type a<'a> = ('a, int)
type t<'a> = {"x": a<'a>, "x": (string, bool)}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (211 bytes):

```text

  We've found a bug for you!
  Main.res:2:32-45

  1 │ type a<'a> = ('a, int)
  2 │ type t<'a> = {"x": a<'a>, "x": (string, bool)}
  3 │ 

  Method 'x' has type (string, bool), which should be a<string>

```

Debugger hit counts:

```text
{"equal": 2, "equal_false": 2, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 2, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D4-4 — outputs agree

`Main.res`:

```rescript
type a = int
type t = {"x": a, "x": string}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (169 bytes):

```text

  We've found a bug for you!
  Main.res:2:24-29

  1 │ type a = int
  2 │ type t = {"x": a, "x": string}
  3 │ 

  Method 'x' has type string, which should be a

```

Debugger hit counts:

```text
{"equal": 2, "equal_false": 2, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 2, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D4-5 — outputs agree

`Main.res`:

```rescript
type t<'a> = {"x": ('a, 'a), "x": (int, string)}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (182 bytes):

```text

  We've found a bug for you!
  Main.res:1:35-47

  1 │ type t<'a> = {"x": ('a, 'a), "x": (int, string)}
  2 │ 

  Method 'x' has type (int, string), which should be (int, int)

```

Debugger hit counts:

```text
{"equal": 2, "equal_false": 2, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 2, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D4-6 — outputs agree

`Main.res`:

```rescript
type a<'a> = option<'a>
type t<'a> = {"x": a<'a>, @set "x": option<int>}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (156 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 1, "equal_false": 1, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 1, "object_retry": 1, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 5, "subst_body_failure": 0, "subst_param_failure": 0}
```

## D5 — NOT REACHED

A polymorphic-variant pattern must reach row unification in Pattern mode (`compiler-rust/src/types/ctype.rs:8532-8549`; `compiler/ml/ctype.ml:2401-2411`) and fail after changing payloads or row fields. The enclosing pattern checker must continue or diagnose in a way that distinguishes Rust propagation from OCaml rollback and reification.

No candidate hits the failed-row handler with Pattern mode set. D5-2 hits the failed-row handler twice, both in Expression mode; the GADT variants D5-7 and D5-8 do not reach failed row unification. The unsatisfied condition is Pattern-mode failure at ctype.rs:8545, not merely having a polymorphic-variant pattern in the source.

### D5-1 — outputs agree

`Main.res`:

```rescript
let f = (x: [#A(int)]) => switch x { | #A(true) => 1 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (251 bytes):

```text

  We've found a bug for you!
  Main.res:1:43-46

  1 │ let f = (x: [#A(int)]) => switch x { | #A(true) => 1 }
  2 │ 

  This pattern matches values of type [1;31mbool[0m
  but a pattern was expected which matches values of type [1;33mint[0m

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-2 — outputs agree

`Main.res`:

```rescript
let f = (x: [#A(int) | #B]) => switch x { | #C => 1 | _ => 0 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (622 bytes):

```text

  We've found a bug for you!
  Main.res:1:45-46

  1 │ let f = (x: [#A(int) | #B]) => switch x { | #C => 1 | _ => 0 }
  2 │ 

  This pattern matches values of type [1;31m[? #C][0m
  but a pattern was expected which matches values of type [1;33m[#A(int) | #B][0m
  
  The second polymorphic variant is [1;33mclosed[0m and doesn't include the constructor: [1;31m#C[0m.
  
  Possible solutions:
  - Either make the second variant [1;33mopen[0m so it can accept additional constructors. To do this, make sure the type starts with [1;33m[>[0m instead of [1;33m[[0m
  - Or add the missing constructor to it.

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 2, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-3 — outputs agree

`Main.res`:

```rescript
let f = (x: [#A((int, string))]) => switch x { | #A((1, true)) => 1 | _ => 0 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (287 bytes):

```text

  We've found a bug for you!
  Main.res:1:57-60

  1 │ let f = (x: [#A((int, string))]) => switch x { | #A((1, true)) => 1 | _ 
    │ => 0 }
  2 │ 

  This pattern matches values of type [1;31mbool[0m
  but a pattern was expected which matches values of type [1;33mstring[0m

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-4 — outputs agree

`Main.res`:

```rescript
let f = (x: [#A(int) | #B]) => switch x { | #A(1) | #B => 1 | _ => 0 }
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (208 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  if (typeof x === "object" && x.VAL !== 1) {
    return 0;
  } else {
    return 1;
  }
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 4, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-5 — outputs agree

`Main.res`:

```rescript
type t<'a> = A: t<[#A(int)]> | B: t<[#B]>
let f = (type a, x: t<a>, y: a) => switch x { | A => switch y { | #A(true) => 1 } | B => 0 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (315 bytes):

```text

  We've found a bug for you!
  Main.res:1:14-28

  1 │ type t<'a> = A: t<[#A(int)]> | B: t<[#B]>
  2 │ let f = (type a, x: t<a>, y: a) => switch x { | A => switch y { | #A(tru
    │ e) => 1 } | B => 0 }
  3 │ 

  GADTs require recursive type syntax.
  Define your type using `type rec` instead of `type`.

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-6 — outputs agree

`Main.res`:

```rescript
let f = (x: int) => switch x { | true => 1 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (241 bytes):

```text

  We've found a bug for you!
  Main.res:1:34-37

  1 │ let f = (x: int) => switch x { | true => 1 }
  2 │ 

  This pattern matches values of type [1;31mbool[0m
  but a pattern was expected which matches values of type [1;33mint[0m

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-7 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = A: t<[#A(int)]> | B: t<[#B]>
let f = (type a, x: t<a>, y: a) => switch x { | A => switch y { | #A(true) => 1 } | B => 0 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (352 bytes):

```text

  We've found a bug for you!
  Main.res:2:70-73

  1 │ type rec t<'a> = A: t<[#A(int)]> | B: t<[#B]>
  2 │ let f = (type a, x: t<a>, y: a) => switch x { | A => switch y { | #A(tru
    │ e) => 1 } | B => 0 }
  3 │ 

  This pattern matches values of type [1;31mbool[0m
  but a pattern was expected which matches values of type [1;33mint[0m

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 6, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 4, "subst_body_failure": 0, "subst_param_failure": 0}
```

### D5-8 — outputs agree

`Main.res`:

```rescript
type rec t<'a> = A: t<[#A(int)]> | B: t<[#B]>
let f = (type a, x: t<a>, y: a) => switch (x, y) { | (A, #A(true)) => 1 | _ => 0 }
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (342 bytes):

```text

  We've found a bug for you!
  Main.res:2:61-64

  1 │ type rec t<'a> = A: t<[#A(int)]> | B: t<[#B]>
  2 │ let f = (type a, x: t<a>, y: a) => switch (x, y) { | (A, #A(true)) => 1 
    │ | _ => 0 }
  3 │ 

  This pattern matches values of type [1;31mbool[0m
  but a pattern was expected which matches values of type [1;33mint[0m

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 2, "subst_body_failure": 0, "subst_param_failure": 0}
```

## E1 — REACHED, NO DIFFERENCE SEEN

Unification must compare distinct uncached nullary constructors with the same path (`compiler-rust/src/types/ctype.rs:8093-8102`; `compiler/ml/ctype.ml:2255`) and lower one below its locally bound scope. Later checking or printing must distinguish the plain lowering from environment-aware expansion or rejection.

The nullary-lowering call is hit in E1-1, E1-2, E1-4, E1-5 and E1-6; no output differs. These hits do not prove that the nullary branch lowered a constructor below its binding scope; abstract escapes E1-3 and E1-6 are rejected by both compilers.

### E1-1 — outputs agree

`Main.res`:

```rescript
let f = (x: int): int => x
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (131 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E1-2 — outputs agree

`Main.res`:

```rescript
let f = () => {module M = {type t = int}
let id = (x: M.t): M.t => x
id(1)}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (130 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f() {
  return 1;
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 3, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E1-3 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t
external v: t = "v"}
r.contents = Some(M.v)
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (278 bytes):

```text

  We've found a bug for you!
  Main.res:4:19-21

  2 │ module M = {type t
  3 │ external v: t = "v"}
  4 │ r.contents = Some(M.v)
  5 │ 

  This has type: [1;31mM.t[0m
  But it's expected to have type: [1;33m'a[0m
  The type constructor M.t would escape its scope

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 3, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E1-4 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t = int
let v: t = 1}
r.contents = Some(M.v)
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (193 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let M = {
  v: 1
};

r.contents = 1;

exports.r = r;
exports.M = M;
/*  Not a pure module */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E1-5 — outputs agree

`Main.res`:

```rescript
let f = (type a, x: a): a => x
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (131 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E1-6 — outputs agree

`Main.res`:

```rescript
let f = () => {module M = {type t
external v: t = "v"}
let id = (x: M.t): M.t => x
id(M.v)}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (271 bytes):

```text

  We've found a bug for you!
  Main.res:4:1-7

  2 │ external v: t = "v"}
  3 │ let id = (x: M.t): M.t => x
  4 │ id(M.v)}
  5 │ 

  This has type: [1;31mM.t[0m
  But it's expected to have type: [1;33m'a[0m
  The type constructor M.t would escape its scope

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 3, "moregen_occur": 0, "nullary_lower": 6, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

## E2 — REACHED, NO DIFFERENCE SEEN

A variable binding in `unify_types` must lower the compared graph (`compiler-rust/src/types/ctype.rs:8093-8102`) before its occurrence check fails at :8150, unlike `compiler/ml/ctype.ml:2216-2225`. A subsequent attempt, continuation or diagnostic must observe the changed levels rather than only the recursive-type error.

E2-1 and E2-2 hit the occurrence-failure branch two and three times respectively, after the earlier lowering stage; their diagnostics agree. E2-6 exercises the supplied top-level continuation sketch but warning 109 is fatal under the fixture defaults, so it is not evidence of nonfatal continuation.

### E2-1 — outputs agree

`Main.res`:

```rescript
let f = x => x(x)
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (141 bytes):

```text

  We've found a bug for you!
  Main.res:1:16

  1 │ let f = x => x(x)
  2 │ 

  [1;33mThis call is missing an argument[0m of type 'a

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 2, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E2-2 — outputs agree

`Main.res`:

```rescript
let f = x => {let y = (x, 1)
x(y)}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (262 bytes):

```text

  We've found a bug for you!
  Main.res:2:3

  1 │ let f = x => {let y = (x, 1)
  2 │ x(y)}
  3 │ 

  This has type: [1;31m('a => 'b, int)[0m
  But this function argument is expecting: [1;33m'a[0m
  The type variable 'a occurs inside ('a => 'b, int)

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 3, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E2-3 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
r.contents = Some(r)
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (258 bytes):

```text

  We've found a bug for you!
  Main.res:2:19

  1 │ let r = ref(None)
  2 │ r.contents = Some(r)
  3 │ 

  This has type: [1;31mref<option<'a>>[0m
  But it's expected to have type: [1;33m'a[0m
  The type variable 'a occurs inside ref<option<'a>>

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E2-4 — outputs agree

`Main.res`:

```rescript
let f = x => {let y = [x]
x(y)}
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (259 bytes):

```text

  We've found a bug for you!
  Main.res:2:3

  1 │ let f = x => {let y = [x]
  2 │ x(y)}
  3 │ 

  This has type: [1;31marray<'a => 'b>[0m
  But this function argument is expecting: [1;33m'a[0m
  The type variable 'a occurs inside array<'a => 'b>

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E2-5 — outputs agree

`Main.res`:

```rescript
let f = x => {let y = {"a": x}
x(y)}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (147 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x({
    a: x
  });
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E2-6 — outputs agree

`Main.res`:

```rescript
1
let id = x => x
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (545 bytes):

```text

  Warning number 109 (configured as error) 
  Main.res:1:1

  1 │ 1
  2 │ let id = x => x
  3 │ 

  This is at the top level and is expected to return `unit`. But it's returning `int`.

  In ReScript, anything at the top level must evaluate to `unit`. You can fix this by assigning the expression to a value, or piping it into the `ignore` function.

  Possible solutions:
  - Assigning to a value that is then ignored: `let _ = yourExpression`
  - Piping into the built-in ignore function to ignore the result: `yourExpression->ignore`

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

## E3 — REACHED, NO DIFFERENCE SEEN

A scoped type inside a lowering request must fail the first pass and execute the expanding retry (`compiler-rust/src/types/ctype.rs:2569-2588`; `compiler/ml/ctype.ml:631-640`, `compiler/ml/btype.ml:773-781`). Previously memoized abbreviations must subsequently be consulted so that retaining them rather than forgetting them changes acceptance, a diagnostic or generated JavaScript.

E3-2 and E3-4 hit the expanding retry three and two times respectively, with identical outputs. E3-4 also expands parameterized aliases; the trace does not establish a later read of a stale memo, and the other candidates do not reach the retry.

### E3-1 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t = int}
let x: M.t = 1
r.contents = Some(x)
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (212 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let M = {};

r.contents = 1;

let x = 1;

exports.r = r;
exports.M = M;
exports.x = x;
/*  Not a pure module */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E3-2 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t
external x: t = "x"}
r.contents = Some(M.x)
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (278 bytes):

```text

  We've found a bug for you!
  Main.res:4:19-21

  2 │ module M = {type t
  3 │ external x: t = "x"}
  4 │ r.contents = Some(M.x)
  5 │ 

  This has type: [1;31mM.t[0m
  But it's expected to have type: [1;33m'a[0m
  The type constructor M.t would escape its scope

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 3, "moregen_occur": 0, "nullary_lower": 0, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 0, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E3-3 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t<'a> = ('a, int)}
let x: M.t<int> = (1, 2)
r.contents = Some(x)
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (223 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let M = {};

let x = [
  1,
  2
];

r.contents = x;

exports.r = r;
exports.M = M;
exports.x = x;
/*  Not a pure module */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 4, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E3-4 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t
type pair<'a> = ('a, t)
external x: pair<int> = "x"}
r.contents = Some(M.x)
```

#### Both compilers

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (469 bytes):

```text

  We've found a bug for you!
  Main.res:5:19-21

  3 │ type pair<'a> = ('a, t)
  4 │ external x: pair<int> = "x"}
  5 │ r.contents = Some(M.x)
  6 │ 

  This has type: [1;31m(int, M.t)[0m
  But it's expected to have type: [1;33m'a[0m
  The type constructor M.t would escape its scope
  
  Possible solutions: 
  - These types are compatible at runtime. You can use the coercion operator to convert to the expected type: [1;33m(M.x :> (int, M.t))
[0m
  

```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 2, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 8, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E3-5 — outputs agree

`Main.res`:

```rescript
let f = () => {let r = ref(None)
module M = {type a<'a> = option<'a>}
let x: M.a<int> = Some(1)
r.contents = Some(x)
r.contents}
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (252 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_option = require("@rescript/runtime/lib/js/Primitive_option.cjs");

function f() {
  let r;
  r = Primitive_option.some(1);
  return r;
}

exports.f = f;
/* No side effect */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 2, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 3, "subst_body_failure": 0, "subst_param_failure": 0}
```

### E3-6 — outputs agree

`Main.res`:

```rescript
let r = ref(None)
module M = {type t = int
type a<'a> = ('a, t)}
let x: M.a<int> = (1, 2)
let y: M.a<string> = ("s", 2)
r.contents = Some((x, y))
```

#### Both compilers

`Main.res` exit status: **0**.

stdout (274 bytes):

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let M = {};

let x = [
  1,
  2
];

let y = [
  "s",
  2
];

r.contents = [
  x,
  y
];

exports.r = r;
exports.M = M;
exports.x = x;
exports.y = y;
/*  Not a pure module */
```

stderr (0 bytes):

```text
```

Debugger hit counts:

```text
{"equal": 0, "equal_false": 0, "level_retry": 0, "moregen_occur": 0, "nullary_lower": 5, "object_retry": 0, "occur_failure": 0, "pattern_row_failure": 0, "row_failure": 0, "subst": 9, "subst_body_failure": 0, "subst_param_failure": 0}
```

## E4 — WITNESS, FIXED: the link of an expanded head to the original type

OCaml's `unify3` links the expanded head it chose to the ORIGINAL opposite
side before it unifies the children, in expression mode
(`compiler/ml/ctype.ml:2330-2331`: `occur !env t1' t2'; link_type t1' t2`;
`d1` and `d2` are read before the link at 2308, `create_recursion` at 2309,
a failure puts `d1` back at 2437, and the recursion is repaired after the
children at 2428-2436). The Rust `unify_after_expansion`
(`compiler-rust/src/types/ctype.rs:7855`, before the fix) had this order only
for two constructors of one path. For every other pair it called `unify` on
the two expanded heads (`ctype.rs:8006`), which linked one expanded head to
the other, and linked to the original afterwards only when the head did not
occur in it (`!deep_occur(ctx, lhs, to_ty)`, `ctype.rs:8021`). For an
abbreviation that expands to its own argument (`type id<'a> = 'a`) the head
always occurs there, so the link to the original never happened and the
alias spelling of the original was lost.

E4-1 to E4-3 are the three witnesses (each a file of its own; `let z:
string = ...` prints a type). E4-4 to E4-6 print the other variable; they
agreed before and agree after. Commands as in "Candidate commands"
(single-file); every output below is stderr, colour escapes removed, stdout
empty, exit status 2 on both sides.

### Fixed

`unify_types` (`compiler-rust/src/types/ctype.rs:8136`) takes the target
its structural arms link the left side to: the right side when it is reached
directly, the original opposite side from `unify_after_expansion`, whose
general arm in expression mode now reads `create_recursion` before the link
(`ctype.rs:8025`, OCaml 2309), runs the structural arms on the expanded pair
with the original as the target (occurrence check, link, children, the
descriptor put back on failure; OCaml 2330-2331 and 2437), and then the
recursion repair `repair_recursion` (`ctype.rs:8041`, OCaml 2428-2436) with
`forget_abbrev` (OCaml `btype.ml:636-647`) and `closed_parameterized_type`
(`ctype.rs:8061`, OCaml `ctype.ml:441-451`). All six candidates now print
OCaml's output byte for byte; E4-1 to E4-3 are the super_errors fixtures
`abbreviation_expansion_links_original`, `_object` and `_one_sided`. Pattern
mode keeps unifying the two expanded heads (OCaml: `add_type_equality t1'
t2'`, ctype.ml:2332); that departure stays open, as do the `deep_occur`
guards of the same-path arm of `unify_after_expansion`, of the same-path
constructor arm of `unify_types` and of `update_level_pass`
(OCaml `ctype.ml:2330-2331`, 594, 603 have none), for which no program
showing a difference was found.

### E4-1 — WITNESS (program A)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = b
  z
}
```

#### OCaml, and Rust after the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = b
  8 │   z
  9 │ }

  This has type: id<id<(int, int)>> (defined as (int, int))
  But it's expected to have type: string

```

#### Rust before the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = b
  8 │   z
  9 │ }

  This has type: id<(int, int)> (defined as (int, int))
  But it's expected to have type: string

```

### E4-2 — WITNESS (program B)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<{"x": int}> => {"x": 1}
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = b
  z
}
```

#### OCaml, and Rust after the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = b
  8 │   z
  9 │ }

  This has type: id<id<{"x": int}>>
  But it's expected to have type: string

```

#### Rust before the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = b
  8 │   z
  9 │ }

  This has type: id<{"x": int}>
  But it's expected to have type: string

```

### E4-3 — WITNESS (program C)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let pl = (): (int, int) => (1, 2)
let f = (a, b) => {
  let _ = [a, pl()]
  let _ = [b, mk()]
  let _ = [b, a]
  let z: string = a
  z
}
```

#### OCaml, and Rust after the fix

```text

  We've found a bug for you!
  Main.res:8:19

   6 │   let _ = [b, mk()]
   7 │   let _ = [b, a]
   8 │   let z: string = a
   9 │   z
  10 │ }

  This has type: id<(int, int)> (defined as (int, int))
  But it's expected to have type: string

```

#### Rust before the fix

```text

  We've found a bug for you!
  Main.res:8:19

   6 │   let _ = [b, mk()]
   7 │   let _ = [b, a]
   8 │   let z: string = a
   9 │   z
  10 │ }

  This has type: (int, int)
  But it's expected to have type: string

```

### E4-4 — outputs agree (program A, printing `a`)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = a
  z
}
```

#### Both compilers, before and after the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = a
  8 │   z
  9 │ }

  This has type: id<(int, int)> (defined as (int, int))
  But it's expected to have type: string

```

### E4-5 — outputs agree (program B, printing `a`)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<{"x": int}> => {"x": 1}
let f = (a, b) => {
  let _ = [a, mk()]
  let _ = [b, mk()]
  let _ = [a, b]
  let z: string = a
  z
}
```

#### Both compilers, before and after the fix

```text

  We've found a bug for you!
  Main.res:7:19

  5 │   let _ = [b, mk()]
  6 │   let _ = [a, b]
  7 │   let z: string = a
  8 │   z
  9 │ }

  This has type: id<{"x": int}>
  But it's expected to have type: string

```

### E4-6 — outputs agree (program C, printing `b`)

`Main.res`:

```rescript
type id<'a> = 'a
let mk = (): id<(int, int)> => (1, 2)
let pl = (): (int, int) => (1, 2)
let f = (a, b) => {
  let _ = [a, pl()]
  let _ = [b, mk()]
  let _ = [b, a]
  let z: string = b
  z
}
```

#### Both compilers, before and after the fix

```text

  We've found a bug for you!
  Main.res:8:19

   6 │   let _ = [b, mk()]
   7 │   let _ = [b, a]
   8 │   let z: string = b
   9 │   z
  10 │ }

  This has type: id<(int, int)> (defined as (int, int))
  But it's expected to have type: string

```

## Reachability measurement

No instrumentation rebuild was used. The release ELF retains local symbols;
GDB breakpoints count function entries and specific post-error instructions.
The ELF build ID was `e9502b864ac46110ee66fa890fec58ceb6de59d7`.
These offsets are specific to this build: on a different binary, identify the
same call/branch in disassembly instead of reusing its offsets blindly.
All 51 debugger runs completed; their counts are printed with each candidate.

The following GDB Python script was used (`TRACE_OUT` names a temporary JSON
file), with `gdb -batch -ex 'set pagination off' -ex 'set print thread-events off'
-x trace.py --args "$ROOT/rewatch/target/release/rescript" bsc ...` and the
candidate flags above. Each debugger invocation had a 30-second outer timeout.

```python
import gdb,json,os
counts={}
prefix='_RNvNtNtCs49VnplE2UFO_17rescript_compiler5types5ctype'
class Hit(gdb.Breakpoint):
 def __init__(self,label,suffix,offset=0,condition=None):
  super().__init__('*'+(suffix if suffix.startswith('_R') else prefix+suffix)+'+'+str(offset),internal=True);self.label=label;self.cond=condition;counts[label]=0
 def stop(self):
  if self.cond is None or int(gdb.parse_and_eval(self.cond)): counts[self.label]+=1
  return False
Hit('equal','5equal')
Hit('equal_false','5equal',0x14f,'$al == 0')
Hit('object_retry','_RNvNvNtNtCs49VnplE2UFO_17rescript_compiler5types8typecore17transl_type_inner16add_object_field',0x44b)
Hit('moregen_occur','13moregen_occur')
Hit('subst','15subst_with_memo')
Hit('subst_body_failure','15subst_with_memo',0x6c3)
Hit('subst_param_failure','15subst_with_memo',0x751)
Hit('level_retry','26update_level_checked_above',0x202)
Hit('nullary_lower','11unify_types',0x13c5c39-0x13c5140)
Hit('occur_failure','11unify_types',0x13c5a1c-0x13c5140)
Hit('row_failure','11unify_types',0x13c648c-0x13c5140)
Hit('pattern_row_failure','11unify_types',0x13c648c-0x13c5140,'*(unsigned char *)(*(unsigned long *)($rsp+0x28)+0x78) == 1')
gdb.execute('run',to_string=True)
open(os.environ['TRACE_OUT'],'w').write(json.dumps(counts))
```

The `equal_false` counter stops at the return instruction with `$al == 0`;
`object_retry` stops at the `unify` call after the duplicate-field equality check.
The two substitution failure addresses are calls to `link_type` guarded by
failed `unify_var` results: `subst_with_memo+0x6c3` and `+0x751`.
The retry address is the second `update_level_pass` call, after
`restore_type_state`. The row-failure address is the descriptor-restore block
selected by `Err(Unify)` after `unify_rows`; the mode byte at state offset 0x78
is 0 for Expression and 1 for Pattern (also used by the preceding conditional
occurrence check). The occurrence-failure address is the error arm following
`occur_check`. The nullary address is the plain `update_level` call following
the same-path/no-cached-expansion fast-path checks.

These are process-wide counts, including any setup work within the compiler;
they do not measure graph mutations or prove that a particular memo is stale.

## Interface setup attempts (not checker witnesses)

These attempts compiled each interface with its respective compiler, then used
`-bs-read-cmi` without `-I .`. The missing include path blocks the reference
compiler before inclusion; the corrected runs above are the evidence.

### D1-6, missing include path

#### OCaml

`Main.resi` exit status: **0**.

stdout (0 bytes):

```text
```

stderr (0 bytes):

```text
```

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (88 bytes):

```text

  We've found a bug for you!
  Main.res

  Could not compile the interface Main.resi.

```

#### Rust

`Main.resi` exit status: **0**.

stdout (0 bytes):

```text
```

stderr (0 bytes):

```text
```

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (380 bytes):

```text

  We've found a bug for you!
  Main.res:2:1-28

  1 │ type a = int
  2 │ type t = {x: int, y: string}
  3 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:2:1-28):
    type t = {x: int, y: string}
  
  Expected declaration (Main.resi:2:1-23):
    type t = {x: a, y: int}
  
  The types for field y are not equal.

```

### D2-6, missing include path

#### OCaml

`Main.resi` exit status: **0**.

stdout (0 bytes):

```text
```

stderr (0 bytes):

```text
```

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (88 bytes):

```text

  We've found a bug for you!
  Main.res

  Could not compile the interface Main.resi.

```

#### Rust

`Main.resi` exit status: **0**.

stdout (0 bytes):

```text
```

stderr (0 bytes):

```text
```

`Main.res` exit status: **2**.

stdout (0 bytes):

```text
```

stderr (328 bytes):

```text

  We've found a bug for you!
  Main.res:3:5

  1 │ type t
  2 │ let r = ref(None)
  3 │ let v = r.contents
  4 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:3:5):
    let v: option<Main.t>
  
  Expected declaration (Main.resi:2:1-16):
    let v: option<t>

```


## Limits and gates

- The full compiler suite was not run, as required for this investigation.
- No Cargo manifest, compiler source or test changed; this is documentation only.
- No benchmark comparison was run: there is no candidate compiler implementation
  or performance change to compare, and the allowed single release build was
  used for the oracle investigation.
- D3 and D5 remain without a source witness or general unreachability proof.
  Their verdicts report measured non-reachability in this search, not equivalence.
- For D1, D4, E1, E2 and E3 the measured calls/branches agree observationally;
  the stronger state-survival conditions remain unproved.
- The two-file D2 witness has not been reduced further or attributed to D2's
  swallowed lowering error. It must not be used as evidence of that cause.

## Second round: universal variables, polymorphic types and packages

### Scope, calibration and reproducibility

This search ran 74 candidates against `7871ac5909`, six per place in U1–U11
order followed by eight reduction/coverage probes. All output comparisons use the
unmodified compiler; a separate instrumented binary records reachability only.
A WITNESS is an observed difference, **not a causal attribution** to the nominated
lines. In particular U2, U7 and U8 have off-path witnesses. REACHED means the
specific marker ran, not that every escape/mutation condition was satisfied.
The smallest witness found for each place is identified below; this is bounded
reduction, not a proof of global minimality.

Every source below ends with a newline. Every candidate has its own temporary
directory under `$TMPDIR`, containing `Main.res`, optional `Main.resi`, and:

```json
{"name":"checker-probe","sources":["."]}
```

Commands (ROOT is the checkout; SCRATCH is a temporary directory):

```sh
export PATH="$HOME/.cargo/bin:$PATH"
export ROOT="$PWD"
export RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime"
eval $(opam env)
dune build --root .
CARGO_TARGET_DIR="$ROOT/.universal-target" CARGO_PROFILE_RELEASE_LTO=thin \
  cargo build --release --manifest-path rewatch/Cargo.toml
cp .universal-target/release/rescript "$SCRATCH/rescript-original"
"$SCRATCH/rescript-original" build-reference \
  --bsc "$ROOT/_build/install/default/bin/bsc" packages/@rescript/runtime
# bsc-original is a shell wrapper executing rescript-original bsc "$@".
RUST_BSC="$SCRATCH/bsc-original" PARITY_JOBS=1 \
  bash scripts/test_error_output_parity.sh --release --compiler-only apply_non_function.res
```

The initial Cargo attempt with the default target directory failed writing a
cached dependency file (`No such file or directory`); a fresh target directory
built successfully. OCaml build exited 0 with empty stdout and stderr. Rust:

```text
warning: `rescript` (lib) generated 1 warning (run `cargo fix --lib -p rescript` to apply 1 suggestion)
warning: `rescript` (lib) generated 1 warning (1 duplicate)
    Finished `release` profile [optimized] target(s) in 2m 05s
```

The warning is the existing unused `console::style` import in
`rewatch/src/build/packages.rs:12`. Runtime and calibration output (terminal
color escapes omitted only in this build/calibration summary):

```text
OCaml reference build: 113 of 113 modules built
Compiler diagnostics parity

Error output parity summary
  total:  2
  pass:   2
  fail:   0
SUCCESS: OCaml and Rust diagnostic output match for tested fixtures.
```

The first calibration attempt omitted RESCRIPT_RUNTIME for the relocated Rust
binary and failed with `bsc: pass -runtime-path or set RESCRIPT_RUNTIME` (exit 1).
The exported runtime above fixes that setup error; it is not a checker witness.
Existing fixture `tests/build_tests/super_errors/fixtures/apply_non_function.res`:

```rescript
let x = 1

let y = x(2)
```

Both exit 2; stdout:

```text
```

Both stderr:

```text

  We've found a bug for you!
  tests/build_tests/super_errors/fixtures/apply_non_function.res:3:9

  1 │ let x = 1
  2 │ 
  3 │ let y = x(2)
  4 │ 

  This can't be called, it's not a function.
  It has type: int

```

Each single-file candidate was compiled from its directory with these commands:

```sh
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w +A -bs-jsx 4 -color never Main.res
timeout 10 "$SCRATCH/rescript-original" bsc -w +A -bs-jsx 4 -color never Main.res
```

The runner uses Python `subprocess.run(capture_output=True, text=True, timeout=10)`
for the equivalent timeout and separate exit/stdout/stderr capture. Before each
invocation it deletes only that candidate's generated `.cm*` files. U6 uses the
parity script's reference interface prebuild before **each** implementation:

```sh
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w -A -color never Main.resi
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w +A -bs-jsx 4 -color never -I . -bs-read-cmi Main.res
# Repeat the OCaml interface prebuild, then:
timeout 10 "$SCRATCH/rescript-original" bsc -w +A -bs-jsx 4 -color never -I . -bs-read-cmi Main.res
```

JavaScript is stdout and was compared byte-for-byte along with stderr and exit
status. Empty fences are literally empty streams. Candidate output fences retain
ANSI escape bytes emitted by the compilers even with `-color never`; no diagnostic
normalization was applied. Matching outputs are pasted once.

### Reachability instrumentation

Temporary `eprintln!("PROBE:U<n>")` statements were inserted at the sites below,
then the same thin-LTO build was rerun (exit 0, `Finished release profile
[optimized] target(s) in 1m 26s`). Every candidate was also run with that binary,
using the same flags and interface setup. Markers are listed separately from the
unmodified outputs and were never used as diagnostic comparison evidence. The
source was restored byte-for-byte before any commit; no compiler change is part
of this report.

| Marker | Exact insertion site in compiler-rust/src/types/ctype.rs at the tested commit |
| --- | --- |
| U1 | After `state.univar_pairs.push((cl1, cl2))` in mcomp_enter_poly and unify_enter_poly (1119, 1252). |
| U2 | Inside `for (cl1, cl2) in pairs.iter().rev()` in mcomp_univar_family (1007). |
| U3 | Immediately before surely_univar_free in occur_univar (2278). |
| U4 | Start of the nonempty equal-binder-count Tpoly arm in moregen (10202). |
| U5 | The successful name-equal Tunivar row-tail arm in moregen_row (9883). This marker does not cover the name-unequal rejection arm. |
| U6 | Start of the nonempty equal-binder-count Tpoly arm in equal_type_exprs_without_renaming_rec (11409). |
| U7 | After successful occur and before update_level_checked in moregen_occur (9758). |
| U8 | After both remq calls, before lowering in unify_row_field (9347). |
| U9 | subtype_rec fallback (6372), guarded by both operands being Tpackage. |
| U10 | Inside the path.is_free(mid) branch of nondep_type_rec's Tpackage arm (14651). |
| U11 | At the start of each one-sided empty-binder Tpoly unwrapping arm in unify (8773, 8777). |

### Second-round summary

| Place | Verdict | Candidates | Smallest witness found |
| --- | --- | ---: | --- |
| U1 | REACHED, NO DIFFERENCE SEEN | 6 | — |
| U2 | WITNESS, FIXED | 7 | U2-7 (off-path) |
| U3 | REACHED, NO DIFFERENCE SEEN | 6 | — |
| U4 | WITNESS | 7 | U4-7 |
| U5 | WITNESS | 7 | U5-7 |
| U6 | WITNESS | 6 | U6-1 |
| U7 | WITNESS | 7 | U7-7 (off-path; identical to U4-7) |
| U8 | WITNESS | 9 | U8-8 (off-path) |
| U9 | WITNESS | 6 | U9-1 |
| U10 | WITNESS | 7 | U10-7 |
| U11 | NOT REACHED | 6 | — |

### U1 — REACHED, NO DIFFERENCE SEEN

A program must unify two nonempty polymorphic object schemes to enter the directional pair scopes in Rust mcomp_enter_poly/unify_enter_poly (1088–1123, 1213–1256) and OCaml enter_poly (1656–1679). A later body comparison or scope exit must expose different pairing or restoration to produce an output difference.

U1-1, U1-2, U1-3 and U1-6 hit U1; all six outputs agree. This does not exercise every exceptional scope-exit path.

#### U1-1 — outputs agree

`Main.res`:

```rescript
type a = {"id": 'a. 'a => 'a}
type b = {"id": 'b. 'b => 'b}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### U1-2 — outputs agree

`Main.res`:

```rescript
type a = {"id": 'a 'b. ('a, 'b) => 'a}
type b = {"id": 'b 'a. ('a, 'b) => 'a}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### U1-3 — outputs agree

`Main.res`:

```rescript
type a = {"id": 'a 'b. ('a, 'b) => 'a}
type b = {"id": 'a 'b. ('a, 'b) => 'b}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"id": 'a 'b. ('a, 'b) => 'a}
  2 │ type b = {"id": 'a 'b. ('a, 'b) => 'b}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Types for field [1;33m"id"[0m are incompatible:
  Field [1;33m"id"[0m in the passed object has type [1;31m'a 'b. ('a, 'b) => 'a[0m, but is expected to have type [1;33m'a 'b. ('a, 'b) => 'b[0m.
  
  Possible solutions: 
  - These types are compatible at runtime. You can use the coercion operator to convert to the expected type: [1;33m(x :> b)
[0m
  

```

#### U1-4 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let v: t = {f: x => x}
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let v = {
  f: x => x
};

exports.v = v;
/* No side effect */
```

stderr:

```text
```

#### U1-5 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let v: t = {f: x => 1}
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:16-21

  1 │ type t = {f: 'a. 'a => 'a}
  2 │ let v: t = {f: x => 1}
  3 │ 

  This field value has type [1;31mint => int[0m
  which is less general than [1;33m'a. 'a => 'a[0m

```

#### U1-6 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a. {"g": 'b. ('a, 'b) => 'a} => 'a}
type b = {"f": 'x. {"g": 'y. ('x, 'y) => 'x} => 'x}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```


### U2 — WITNESS

A program must re-enter a binder already present in the pairing stack so enter_poly_univars (1147–1152) calls mcomp_univars_escape and its family loop (996–1012), corresponding to OCaml get_univar_family (1612–1623). The family propagated across multiple scopes must affect escape acceptance to expose a traversal-order difference.

No U2 marker ran: these candidates did not satisfy the known-binder escape guard in enter_poly_univars. U2-5 and the smaller U2-7 instead expose acceptance of a field that OCaml rejects as less general; this is an off-path witness, not evidence against reverse family iteration.

Smallest witness found: **U2-7 (off-path)** (full source and both outputs below).

#### Fixed

The two witnesses are not a difference of the family loop the place
nominates; tracing them found three causes in the typing of a value for a
polymorphic record field, each fixed in its own commit. After them all
seven candidates agree with OCaml byte for byte (exit status, stdout and
stderr, commands as in "Scope, calibration and reproducibility"), and so
do 48 further programs of the same family (record literal, record field
assignment, object field assignment, let binding with a polymorphic
annotation; accepted and rejected), 17 of which differed before.

- `ff3fc6fe1`: OCaml's `instance_label` copies the record type and
  instantiates the field in one copy session (`compiler/ml/ctype.ml:1097-1105`),
  and `instance_poly`'s delayed `copy` of the univar-free parts sees that
  session (ctype.ml:1037-1041), so the field's `'a` is the record's. The
  Rust `instance_label` (`compiler-rust/src/types/ctype.rs:12604` before the
  fix) called `instance_poly`, which opened a copy cache of its own, so the
  field's `'a` was a fresh variable; `check_univars` then found `'b`, unified
  with it by `y => y`, still generic and accepted the field. Now
  `instance_poly_in_session` (`ctype.rs:12367`) takes the copy cache of the
  operation it belongs to and `instance_label` (`ctype.rs:12611`) passes its
  own. U2-5 and U2-7 are rejected with OCaml's "less general" diagnostic;
  U2-7 is the super_errors fixture
  `polymorphic_field_generality_record_parameter`, and
  `tests/tests/src/polymorphic_field_generality_record_parameter` holds
  programs with such fields both compilers accept.
- `8379f4a59`: OCaml's `type_label_exp` (`compiler/ml/typecore.ml:4336-4358`)
  types an expansive value again without the field type propagated when
  `check_univars` rejects it (PR#4862); Rust checked once and rejected
  values OCaml accepts, such as `{f: Obj.magic(x => x)}` for
  `{f: 'a. 'a => 'a}`. `check_label_univars`
  (`compiler-rust/src/types/typecore.rs:19636`) does what those lines do. It
  is `tests/tests/src/polymorphic_field_generality_retry`; the super_errors
  fixture `polymorphic_field_generality_retry_less_general` is an expansive
  value both reject.
- `77d4cb02b`: OCaml types the value of `r.f = v` with `type_label_exp`
  (typecore.ml:3206-3211); the Rust setfield path
  (`typecore.rs:16873` before the fix) called `ctype::check_univars`
  (`ctype.rs:12794` before the fix), which never generalized and never
  failed. It now calls `check_label_univars` (`typecore.rs:16873`); the
  super_errors fixture `polymorphic_field_generality_setfield` is
  `v.f = y => y` for `{mutable f: 'b. 'b => 'a}`, and
  `tests/tests/src/polymorphic_field_generality_setfield` holds assignments
  both accept.

The object field assignment (`type_object_field_value`) and the
let binding with a polymorphic annotation agreed in every program tried,
before and after.

#### U2-1 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a. {"g": 'b. ('a, 'b) => 'a} => 'a}
type b = {"f": 'x. {"g": 'y. ('x, 'y) => 'x} => 'x}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### U2-2 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a. {"g": 'b. ('a, 'b) => 'b} => 'a}
type b = {"f": 'x. {"g": 'y. ('x, 'y) => 'x} => 'x}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a. {"g": 'b. ('a, 'b) => 'b} => 'a}
  2 │ type b = {"f": 'x. {"g": 'y. ('x, 'y) => 'x} => 'x}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Types for field [1;33m"g"[0m are incompatible:
  Field [1;33m"g"[0m in the passed object has type [1;31m'y. ('x, 'y) => 'y[0m, but is expected to have type [1;33m'y. ('x, 'y) => 'x[0m.

```

#### U2-3 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a. 'a => a}
type b = {"f": 'b. 'b => b}
let f = (x: a): b => x
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:26

  1 │ type a = {"f": 'a. 'a => a}
  2 │ type b = {"f": 'b. 'b => b}
  3 │ let f = (x: a): b => x

  This type constructor, `a`, can't be found.
  If you wanted to write a recursive type, don't forget the `rec` in `type rec`

```

#### U2-4 — outputs agree

`Main.res`:

```rescript
type a<'x> = {"f": 'a. ('a, 'x) => a<'a>}
type b<'x> = {"f": 'b. ('b, 'x) => b<'x>}
let f = (x: a<int>): b<int> => x
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:36

  1 │ type a<'x> = {"f": 'a. ('a, 'x) => a<'a>}
  2 │ type b<'x> = {"f": 'b. ('b, 'x) => b<'x>}
  3 │ let f = (x: a<int>): b<int> => x

  This type constructor, `a`, can't be found.
  If you wanted to write a recursive type, don't forget the `rec` in `type rec`

```

#### U2-5 — WITNESS

`Main.res`:

```rescript
type t<'a> = {f: 'b. 'b => 'a}
let f = x => {f: y => y}
```

Reachability markers: none.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:18-23

  1 │ type t<'a> = {f: 'b. 'b => 'a}
  2 │ let f = x => {f: y => y}
  3 │ 

  This field value has type [1;31m'c => 'c[0m
  which is less general than [1;33m'b. 'b => 'a[0m

```

Rust, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return {
    f: y => y
  };
}

exports.f = f;
/* No side effect */
```

stderr:

```text

  Warning number 27
  Main.res:2:9

  1 │ type t<'a> = {f: 'b. 'b => 'a}
  2 │ let f = x => {f: y => y}
  3 │ 

  unused variable x.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_x`) to ignore that the variable is unused.
- Using the variable somewhere.

```

#### U2-6 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let f = x => {f: y => x}
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:18-23

  1 │ type t = {f: 'a. 'a => 'a}
  2 │ let f = x => {f: y => x}
  3 │ 

  This field value has type [1;31m'b => 'b[0m
  which is less general than [1;33m'a. 'a => 'a[0m

```

#### U2-7 — WITNESS

`Main.res`:

```rescript
type t<'a> = {f: 'b. 'b => 'a}
let v = {f: y => y}
```

Reachability markers: none.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:13-18

  1 │ type t<'a> = {f: 'b. 'b => 'a}
  2 │ let v = {f: y => y}
  3 │ 

  This field value has type [1;31m'c => 'c[0m
  which is less general than [1;33m'b. 'b => 'a[0m

```

Rust, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let v = {
  f: y => y
};

exports.v = v;
/* No side effect */
```

stderr:

```text
```


### U3 — REACHED, NO DIFFERENCE SEEN

A program must link a variable through occur_univar so Rust executes the bounded surely_univar_free precheck (2005–2014, 2275–2279), where OCaml starts its binder walk (1563–1607). Acceptance or a later diagnostic must reveal a free universal missed by that precheck or an observable skipped traversal.

U3-5 and U3-6 hit U3; all six outputs agree. The marker proves precheck entry, not which of its return paths was taken.

#### U3-1 — outputs agree

`Main.res`:

```rescript
let id = x => x
let n = id(1)
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function id(x) {
  return x;
}

let n = 1;

exports.id = id;
exports.n = n;
/* No side effect */
```

stderr:

```text
```

#### U3-2 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let v: t = {f: x => x}
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let v = {
  f: x => x
};

exports.v = v;
/* No side effect */
```

stderr:

```text
```

#### U3-3 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let v: t = {f: x => 1}
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:16-21

  1 │ type t = {f: 'a. 'a => 'a}
  2 │ let v: t = {f: x => 1}
  3 │ 

  This field value has type [1;31mint => int[0m
  which is less general than [1;33m'a. 'a => 'a[0m

```

#### U3-4 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
let escape = x => {f: y => x}
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:23-28

  1 │ type t = {f: 'a. 'a => 'a}
  2 │ let escape = x => {f: y => x}
  3 │ 

  This field value has type [1;31m'b => 'b[0m
  which is less general than [1;33m'a. 'a => 'a[0m

```

#### U3-5 — outputs agree

`Main.res`:

```rescript
let id: 'a. 'a => 'a = x => x
```

Reachability markers: `PROBE:U3`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function id(x) {
  return x;
}

exports.id = id;
/* No side effect */
```

stderr:

```text
```

#### U3-6 — outputs agree

`Main.res`:

```rescript
let id: type a. a => a = x => 1
```

Reachability markers: `PROBE:U3`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:31

  1 │ let id: type a. a => a = x => 1
  2 │ 

  This has type: [1;31mint[0m
  But it's expected to have type: [1;33ma[0m

```


### U4 — WITNESS

A signature value comparison must descend into nonempty polymorphic object methods in moregen (10198–10208), where OCaml uses enter_poly and unify_univar (2985–2989). Renaming or reordering binders must then affect the acceptance or diagnostic of signature inclusion.

All seven candidates hit U4. Alpha-renaming alone fails in U4-1 and the reduced U4-7; reordering in U4-2 agrees.

Smallest witness found: **U4-7** (full source and both outputs below).

#### Fixed

Cause: `moregen`'s polymorphic-type arm compared the binder counts and its
universal-variable arm the variables' names
(`compiler-rust/src/types/ctype.rs:10200-10208` before the fix), where
OCaml enters the binder lists as a scope of pairs and looks the pair up
(`compiler/ml/ctype.ml:2985-2989`, `enter_poly` 1656-1679, `unify_univar`
1544-1559, from an empty `univar_pairs`, 3093). `7a0be2705` gives `moregen`
a `UnivarPairs` scope (`MoregenState`; arms at `ctype.rs:10283-10312`) built
by the functions unification uses. U4-1 and U4-7 now build with OCaml's
JavaScript; U4-2 to U4-6 agree as before. Fixtures: tests/tests
`universal_pairing_moregen` (U4-7, U5-5, U4-2) and super_errors
`universal_pairing_moregen_mismatch` (U4-3).

#### U4-1 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. 'a => 'a}}
module F = (X: A): {let x: {"id": 'b. 'b => 'b}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:53

  1 │ module type A = {let x: {"id": 'a. 'a => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'b. 'b => 'b}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-44):
    let x: {"id": 'a. 'a => 'a}
  
  Expected declaration (Main.res:2:21-47):
    let x: {"id": 'b. 'b => 'b}

```

#### U4-2 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a 'b. ('a, 'b) => 'a}}
module F = (X: A): {let x: {"id": 'b 'a. ('a, 'b) => 'a}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U4-3 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a 'b. ('a, 'b) => 'a}}
module F = (X: A): {let x: {"id": 'a 'b. ('a, 'b) => 'b}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:62

  1 │ module type A = {let x: {"id": 'a 'b. ('a, 'b) => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a 'b. ('a, 'b) => 'b}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-53):
    let x: {"id": 'a 'b. ('a, 'b) => 'a}
  
  Expected declaration (Main.res:2:21-56):
    let x: {"id": 'a 'b. ('a, 'b) => 'b}

```

#### U4-4 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. 'a => 'a}}
module F = (X: A): {let x: {"id": 'a. 'a => 'a}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U4-5 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a 'b. 'a => 'a}}
module F = (X: A): {let x: {"id": 'a. 'a => 'a}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U4-6 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. 'a => int}}
module F = (X: A): {let x: {"id": 'b. 'b => string}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:57

  1 │ module type A = {let x: {"id": 'a. 'a => int}}
  2 │ module F = (X: A): {let x: {"id": 'b. 'b => string}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-45):
    let x: {"id": 'a. 'a => int}
  
  Expected declaration (Main.res:2:21-51):
    let x: {"id": 'b. 'b => string}

```

#### U4-7 — WITNESS

`Main.res`:

```rescript
module F = (X: {let x: {"f": 'a. 'a => 'a}}): {let x: {"f": 'b. 'b => 'b}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:79

  1 │ module F = (X: {let x: {"f": 'a. 'a => 'a}}): {let x: {"f": 'b. 'b => 'b
    │ }} => X
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:17-42):
    let x: {"f": 'a. 'a => 'a}
  
  Expected declaration (Main.res:1:48-73):
    let x: {"f": 'b. 'b => 'b}

```


### U5 — WITNESS

A moregeneral comparison must descend through a polymorphic variant to two universal row tails in moregen_row (9883–9886), corresponding to OCaml's pairing comparison (3048–3049). Row-tail matching or the subsequent printed signature must expose a name-versus-pairing difference.

U5-1 through U5-5 and U5-7 hit the successful U5 row-tail arm. U5-4, U5-6 and U5-7 differ in printed aliases; U5-5 differs in acceptance, with U4 also hit, so this does not isolate the tail comparison as the cause.

Smallest witness found: **U5-7** (full source and both outputs below).

#### Fixed

Two causes. U5-4, U5-6 and U5-7: the printed expected declaration is a
`subst_identity_copy` copy (traced: its `Tpoly` binder list held a `Ttuple`
node), because both Rust copies copied a `Tpoly`'s body before its binders,
so a binder that is also a row tail came back as the marker the row copy
leaves on the tail (`ctype.rs` `subst_identity_copy_rec` and
`copy_type_cached`, `Poly` arms, now at 13488 and 14029). OCaml copies the binders first through
`norm_univar` (`compiler/ml/btype.ml:396-401, 537-539`) and its row copy
reuses a tail copied before (`ctype.ml:816`); `bb08840b0` does the same
(fixture super_errors `universal_pairing_row_binder_copy`, U5-7). U5-5:
`moregen_row` compared universal row tails by name (`ctype.rs:9883` before
the fix; OCaml `ctype.ml:3048`, `unify_univar`); `7a0be2705` pairs them
(`ctype.rs:9963`)
(fixture tests/tests `universal_pairing_moregen`). With pairing alone U5-1,
U5-2 and U6-6 were rejected, because of the first cause; both commits
together make all seven candidates agree.

#### U5-1 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'b. ([< #A | #B] as 'b) => 'b}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U5-2 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U5-3 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. ([> #A] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'b. ([> #A] as 'b) => 'b}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U5-4 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. ([< #A(int) | #B] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'a. ([< #A(string) | #B] as 'a) => 'a}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:78

  1 │ module type A = {let x: {"id": 'a. ([< #A(int) | #B] as 'a) => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a. ([< #A(string) | #B] as 'a) => 'a}
    │ } => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-66):
    let x: {"id": 'a. ([< #A(int) | #B] as 'a) => 'a}
  
  Expected declaration (Main.res:2:21-72):
    let x: {"id": 'a. ([< #A(string) | #B] as 'a) => 'a}

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:78

  1 │ module type A = {let x: {"id": 'a. ([< #A(int) | #B] as 'a) => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a. ([< #A(string) | #B] as 'a) => 'a}
    │ } => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-66):
    let x: {"id": 'a. ([< #A(int) | #B] as 'a) => 'a}
  
  Expected declaration (Main.res:2:21-72):
    let x: {"id": 'a. ([< #A(string) | #B] as 'b) => 'b}

```

#### U5-5 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'a 'b. ([< #A('b)] as 'a) => 'b}}
module F = (X: A): {let x: {"id": 'b 'a. ([< #A('a)] as 'b) => 'a}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:72

  1 │ module type A = {let x: {"id": 'a 'b. ([< #A('b)] as 'a) => 'b}}
  2 │ module F = (X: A): {let x: {"id": 'b 'a. ([< #A('a)] as 'b) => 'a}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-63):
    let x: {"id": 'a 'b. ([< #A('b)] as 'a) => 'b}
  
  Expected declaration (Main.res:2:21-66):
    let x: {"id": 'b 'a. [< #A('a)] => 'a}

```

#### U5-6 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'a. ([< #A] as 'a) => 'a}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:65

  1 │ module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a. ([< #A] as 'a) => 'a}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-61):
    let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}
  
  Expected declaration (Main.res:2:21-59):
    let x: {"id": 'a. ([< #A] as 'a) => 'a}

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:65

  1 │ module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a. ([< #A] as 'a) => 'a}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-61):
    let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}
  
  Expected declaration (Main.res:2:21-59):
    let x: {"id": 'a. ([< #A] as 'b) => 'b}

```

#### U5-7 — WITNESS

`Main.res`:

```rescript
module F = (X: {let x: {"f": 'a. ([< #A(int)] as 'a) => 'a}}): {let x: {"f": 'a. ([< #A(string)] as 'a) => 'a}} => X
```

Reachability markers: `PROBE:U4`, `PROBE:U5`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:116

  1 │ module F = (X: {let x: {"f": 'a. ([< #A(int)] as 'a) => 'a}}): {let x: {
    │ "f": 'a. ([< #A(string)] as 'a) => 'a}} => X
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:17-59):
    let x: {"f": 'a. ([< #A(int)] as 'a) => 'a}
  
  Expected declaration (Main.res:1:65-110):
    let x: {"f": 'a. ([< #A(string)] as 'a) => 'a}

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:116

  1 │ module F = (X: {let x: {"f": 'a. ([< #A(int)] as 'a) => 'a}}): {let x: {
    │ "f": 'a. ([< #A(string)] as 'a) => 'a}} => X
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:17-59):
    let x: {"f": 'a. ([< #A(int)] as 'a) => 'a}
  
  Expected declaration (Main.res:1:65-110):
    let x: {"f": 'a. ([< #A(string)] as 'b) => 'b}

```


### U6 — WITNESS

An implementation/interface record declaration comparison must require equality of a quantified field, reaching equal_type_exprs_without_renaming_rec (11401–11418) rather than only value inclusion. Comparing alpha-renamed field binders then tests Rust's name comparison against OCaml eqtype's scoped pairing (3268–3272).

All six candidates hit U6. U6-1 rejects alpha-renaming only in Rust; its interface prebuild succeeds on both invocations.

Smallest witness found: **U6-1** (full source and both outputs below).

#### Fixed

Cause: `equal_type_exprs_without_renaming_rec` compared binder counts and
universal-variable names (`ctype.rs:11401-11418` before the fix), where
OCaml's `eqtype` enters the binders as pairs (`ctype.ml:3268-3272`, from an
empty `univar_pairs`, 3362). `7a0be2705` gives `EqtypeState` a
`UnivarPairs` scope (arms at `ctype.rs:11516-11546`). U6-1 builds with
OCaml's output; U6-2 to U6-6 agree (U6-6 needs `bb08840b0` as well, see U5).
Fixture: tests/tests `universal_pairing_equal` with its interface (U6-1 and
U6-2).

#### U6-1 — WITNESS

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'b. 'b => 'b}
```

Reachability markers: `PROBE:U6`.

OCaml, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr:

```text
```

Rust, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:1-26

  1 │ type t = {f: 'a. 'a => 'a}
  2 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:1:1-26):
    type t = {f: 'a. 'a => 'a}
  
  Expected declaration (Main.resi:1:1-26):
    type t = {f: 'b. 'b => 'b}
  
  The types for field f are not equal.

```

#### U6-2 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a 'b. ('a, 'b) => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'b 'a. ('a, 'b) => 'a}
```

Reachability markers: `PROBE:U6`.

Both compilers, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr:

```text
```

#### U6-3 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a 'b. ('a, 'b) => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'a 'b. ('a, 'b) => 'b}
```

Reachability markers: `PROBE:U6`.

Both compilers, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:1-35

  1 │ type t = {f: 'a 'b. ('a, 'b) => 'a}
  2 │ 

  The implementation Main.res does not match the interface Main.resi:
  
  Actual declaration (Main.res:1:1-35):
    type t = {f: 'a 'b. ('a, 'b) => 'a}
  
  Expected declaration (Main.resi:1:1-35):
    type t = {f: 'a 'b. ('a, 'b) => 'b}
  
  The types for field f are not equal.

```

#### U6-4 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. 'a => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'a. 'a => 'a}
```

Reachability markers: `PROBE:U6`.

Both compilers, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr:

```text
```

#### U6-5 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a 'b. 'a => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'a. 'a => 'a}
```

Reachability markers: `PROBE:U6`.

Both compilers, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr:

```text
```

#### U6-6 — outputs agree

`Main.res`:

```rescript
type t = {f: 'a. ([< #A] as 'a) => 'a}
```

`Main.resi`:

```rescript
type t = {f: 'b. ([< #A] as 'b) => 'b}
```

Reachability markers: `PROBE:U6`.

Both compilers, reference interface prebuild exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */
```

stderr:

```text
```


### U7 — WITNESS

Signature inclusion must instantiate a pattern variable and finish moregen_occur (9757–9759), where OCaml additionally calls occur_univar (2918). A free universal in the candidate must escape the ordinary occurrence/lowering checks and alter acceptance to isolate the missing call.

U7-1 and U7-2 hit U7 and agree. U7-3, U7-4 and U7-7 instead hit U4 and differ there; none establishes a free-universal escape through the nominated U7 exit.

Smallest witness found: **U7-7 (off-path; identical to U4-7)** (full source and both outputs below).

#### Fixed

U7-3, U7-4 and U7-7 were the U4 cause and agree after `7a0be2705`. The
nominated difference is real as well: OCaml's `moregen_occur` ends with
`occur_univar env ty` (`ctype.ml:2918`) and the Rust one had no such call
(`ctype.rs:9713-9760` before the fix), so a pattern variable inside a
polymorphic method could be instantiated with the method's universal
variable. U7-8 below shows it (OCaml rejects, Rust built it before
`8f73338c3`). `8f73338c3` calls `occur_univar` in `moregen_occur` when
`moregen` has entered a binder scope (`ctype.rs:9784-9840`): outside
one the subject holds no free universal variable, so inclusion of values
without polymorphic types does no walk. U7-9 below agreed before and
after. Fixtures: super_errors `universal_pairing_free_univar` (U7-8) and
tests/tests `universal_pairing_free_univar` (U7-9).

#### U7-1 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a => 'a}}
module F = (X: A): {let x: {"id": int => int}} => X
```

Reachability markers: `PROBE:U7`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

#### U7-2 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a => 'a}}
module F = (X: A): {let x: {"id": int => string}} => X
```

Reachability markers: `PROBE:U7`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:54

  1 │ module type A = {let x: {"id": 'a => 'a}}
  2 │ module F = (X: A): {let x: {"id": int => string}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-40):
    let x: {"id": 'a => 'a}
  
  Expected declaration (Main.res:2:21-48):
    let x: {"id": int => string}

```

#### U7-3 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'x. 'x => 'x}}
module F = (X: A): {let x: {"id": 'a. 'a => 'a}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:53

  1 │ module type A = {let x: {"id": 'x. 'x => 'x}}
  2 │ module F = (X: A): {let x: {"id": 'a. 'a => 'a}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-44):
    let x: {"id": 'x. 'x => 'x}
  
  Expected declaration (Main.res:2:21-47):
    let x: {"id": 'a. 'a => 'a}

```

#### U7-4 — WITNESS

`Main.res`:

```rescript
module type A = {let x: {"id": 'x. 'x => int}}
module F = (X: A): {let x: {"id": 'a. 'a => int}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:54

  1 │ module type A = {let x: {"id": 'x. 'x => int}}
  2 │ module F = (X: A): {let x: {"id": 'a. 'a => int}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-45):
    let x: {"id": 'x. 'x => int}
  
  Expected declaration (Main.res:2:21-48):
    let x: {"id": 'a. 'a => int}

```

#### U7-5 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. 'a => 'a}}
module F = (X: A): {let x: {"id": 'a 'b. 'a => 'b}} => X
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:56

  1 │ module type A = {let x: {"id": 'a. 'a => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a 'b. 'a => 'b}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-44):
    let x: {"id": 'a. 'a => 'a}
  
  Expected declaration (Main.res:2:21-50):
    let x: {"id": 'a 'b. 'a => 'b}

```

#### U7-6 — outputs agree

`Main.res`:

```rescript
module type A = {let x: {"id": 'a. 'a => 'a}}
module F = (X: A): {let x: {"id": 'a. 'a => {"id": 'b. 'b => 'b}}} => X
```

Reachability markers: `PROBE:U4`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:71

  1 │ module type A = {let x: {"id": 'a. 'a => 'a}}
  2 │ module F = (X: A): {let x: {"id": 'a. 'a => {"id": 'b. 'b => 'b}}} => X
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:18-44):
    let x: {"id": 'a. 'a => 'a}
  
  Expected declaration (Main.res:2:21-65):
    let x: {"id": 'a. 'a => {"id": 'b. 'b => 'b}}

```

#### U7-7 — WITNESS

`Main.res`:

```rescript
module F = (X: {let x: {"f": 'a. 'a => 'a}}): {let x: {"f": 'b. 'b => 'b}} => X
```

Reachability markers: `PROBE:U4`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:79

  1 │ module F = (X: {let x: {"f": 'a. 'a => 'a}}): {let x: {"f": 'b. 'b => 'b
    │ }} => X
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:17-42):
    let x: {"f": 'a. 'a => 'a}
  
  Expected declaration (Main.res:1:48-73):
    let x: {"f": 'b. 'b => 'b}

```


#### U7-8 — WITNESS (added after the search)

`Main.res`:

```rescript
module F = (X: {let x: {"f": 'b. 'b => 'a}}): {let x: {"f": 'b. 'b => 'b}} => X
```

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:79

  1 │ module F = (X: {let x: {"f": 'b. 'b => 'a}}): {let x: {"f": 'b. 'b => 'b
    │ }} => X
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:17-42):
    let x: {"f": 'b. 'b => 'a}
  
  Expected declaration (Main.res:1:48-73):
    let x: {"f": 'b. 'b => 'b}

```

Rust before `8f73338c3`, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

After `8f73338c3` the Rust output is OCaml's, byte for byte.

#### U7-9 — outputs agree (added after the search)

`Main.res`:

```rescript
module type A = {let x: {"f": 'b. 'b => 'a}}
module F = (X: A): {let x: {"f": 'b. 'b => int}} => X
```

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```

Rust at `8f73338c3`, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

exports.F = F;
/* No side effect */
```

stderr:

```text
```


### U8 — WITNESS

Two distinct Reither fields must pass the fixed-row fast path and duplicate-removal logic in unify_row_field (9346–9354), corresponding to OCaml's residual partition (2685–2703). A residual containing a universal must survive to lowering and change acceptance or diagnostics to isolate the omitted reconciliation.

U8-9 hits U8 and agrees, but has ordinary int payloads. The universal-payload witnesses U8-1, U8-3 through U8-6 and U8-8 hit U1, not U8: the fixed-row pairwise payload path at 9290–9305 precedes the residual branch, so these are off-path witnesses. Removing the explicit row binder in U8-7 fails with an unbound variable in both compilers.

Smallest witness found: **U8-8 (off-path)** (full source and both outputs below).

#### Fixed and open

- U8-1, U8-3, U8-4, U8-5 and U8-8: unification already paired binders by
  node, and the binder lists of the copies it compared held the row copy's
  `Ttuple` marker instead of the row tail (traced in the `moregen` and
  unification arms on U5-1 and U8-6: `vars1=[Ttuple(..)]`); the U5 copy
  cause, fixed by `bb08840b0` (fixture tests/tests
  `universal_pairing_row_binder`, U8-8).
- U8-6: OCaml's `transl_simple_type` and `transl_simple_type_delayed` end
  with `make_fixed_univars` (`compiler/ml/typetexp.ml:677-703, 736-748`),
  which fixes every row with a universal tail and marks its `Reither`
  fields matched; Rust had no such pass, so `set_more`
  (`ctype.ml:2597-2606`) erased the unmatched `#B` instead of reporting it.
  `3681faca1` adds `make_fixed_univars` (`compiler-rust/src/types/typecore.rs:2740`),
  run only when the translation universalized a variable (fixtures
  super_errors and tests/tests `universal_pairing_fixed_row`, U8-6 and
  U8-1/U8-9).
- U8-10 and U8-11, the nominated residual split (PR#6744,
  `compiler/ml/ctype.ml:2685-2703`): the Rust `unify_row_field` lowered and
  kept every residual payload in the merged `Reither` conjunction, so a
  universal variable entered it (`#A(int) & ('a0)`) and escaped later, at
  another location and with another type in the report. Fixed by
  `c51da5f56`: the residual payloads are tested with `occur_univar` once
  each and split only when one holds a universal variable (those of both
  sides unified, one on a single side rejected, the rest lowered), as OCaml
  does (`compiler-rust/src/types/ctype.rs`, `unify_row_field`). Fixtures:
  super_errors `universal_pairing_residual_escape` (U8-10) and
  `universal_pairing_residual_swap` (U8-11), tests/tests
  `universal_pairing_residual_payload` (agreed before).
- U8-12 and U8-13, fixed. OCaml rejects the program's own inferred
  signature; Rust accepted it. Reduction: `let f = (x: {"f": 'a. [<
  #A('a)] => int}) => x`. Three causes, all needed (each verified by an
  experiment: the order change alone, or the shortcut disabled alone,
  leaves all three programs accepted):
  1. The order of a type copy. OCaml's `copy_type_desc`
     (`compiler/ml/btype.ml:508-541`) is evaluated right to left for
     constructor arguments and record fields: an arrow's result is copied
     before its parameters (`btype.ml:512`), a field's rest before its type
     (`btype.ml:532`); lists are mapped left to right and a `Tpoly`'s
     binders come before its body (`btype.ml:538-539`), as a probe built
     with the OCaml 5.5 native compiler prints. Where two variants share a
     row variable the copy keeps the variant it reaches first
     (`ctype.ml:786-791, 806-816`). `7db7702c3` makes every Rust copy that
     builds a descriptor as `copy_type_desc` does visit children in that
     order: `copy_type_cached` (`compiler-rust/src/types/ctype.rs:14004`,
     Ctype.copy), `subst_identity_copy_rec` (`ctype.rs:13637`,
     Subst.typexp), `copy_sep_inner` (`ctype.rs:12489`, Ctype.copy_sep),
     `nondep_type_rec` (`ctype.rs:14847`, Ctype.nondep_type) and
     `copy_lookup_type_expr_with_paths` (`typecore.rs:21718`, Subst.typexp
     with a path map). It changes no output by itself.
  2. `inferred_signature_coercion` (`includemod.rs:2213`) answered the
     inclusion without comparing anything; OCaml always runs
     `Includemod.compunit` (`compiler/ml/typemod.ml:1812-1815`).
     `94fd623f3` records on the unit's type context whether it created or
     copied a polymorphic type with a bound variable
     (`TypeContext::note_bound_universal`, `context.rs:3008`; set in the
     `Ptyp_poly` translation, `typecore.rs:3542`, and in the `Tpoly` arm of
     the five copies above when the binder list is not empty); such a unit
     goes to the full `compunit` check, the others keep the shortcut for one
     load. No program without a polymorphic type was found whose inferred
     signature OCaml rejects (19 programs, listed in the pull request).
  3. The driver reported the failure as an internal message
     (`Inferred signature inclusion failed: ...`, exit 1). `b3944a33a`
     reports it through `format_compunit_mismatch_report`, the path of an
     interface mismatch, named "(inferred signature)", exit 2
     (`inferred_signature_mismatch`, `driver.rs:7361`, at both sites).
  Fixtures: super_errors `inferred_signature_shared_variant` (the
  reduction) and `inferred_signature_shared_variant_annotated` (U8-12),
  tests/tests `inferred_signature_polymorphic` (accepted before and after,
  now through the full check). U8-1 to U8-11 still agree.

#### U8-1 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'a 'r. ([< #A('a) | #B] as 'r) => 'a}
type b = {"f": 'b 's. ([< #A('b) | #B] as 's) => 'b}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'r. ([< #A('a) | #B] as 'r) => 'a}
  2 │ type b = {"f": 'b 's. ([< #A('b) | #B] as 's) => 'b}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m

```

#### U8-2 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
type b = {"f": 'a 'r. ([< #A(int)] as 'r) => 'a}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  2 │ type b = {"f": 'a 'r. ([< #A(int)] as 'r) => 'a}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Both polymorphic variants have the constructor [1;33m#A[0m, but their payload types are incompatible.
  Make sure the payload types for [1;33m#A[0m match exactly in both polymorphic variants.

```

#### U8-3 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
type b = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  2 │ type b = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Both polymorphic variants have the constructor [1;33m#A[0m, but their payload types are incompatible.
  Make sure the payload types for [1;33m#A[0m match exactly in both polymorphic variants.

```

#### U8-4 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'a 'b 'r. ([< #A('a) | #B('b)] as 'r) => 'a}
type b = {"f": 'a 'b 'r. ([< #A('b) | #B('a)] as 'r) => 'a}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'b 'r. ([< #A('a) | #B('b)] as 'r) => 'a}
  2 │ type b = {"f": 'a 'b 'r. ([< #A('b) | #B('a)] as 'r) => 'a}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Types for field [1;33m"f"[0m are incompatible:
  Field [1;33m"f"[0m in the passed object has type [1;31m'b 'a 'c. [< #A('b) | #B('a)] => 'b[0m, but is expected to have type [1;33m'a 'b 'd. [< #A('b) | #B('a)] => 'a[0m.
  
  Possible solutions: 
  - These types are compatible at runtime. You can use the coercion operator to convert to the expected type: [1;33m(x :> b)
[0m
  

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'b 'r. ([< #A('a) | #B('b)] as 'r) => 'a}
  2 │ type b = {"f": 'a 'b 'r. ([< #A('b) | #B('a)] as 'r) => 'a}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m

```

#### U8-5 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'r. ([< #A(int) | #B] as 'r) => 'r}
type b = {"f": 'r. ([< #A(string) | #B] as 'r) => 'r}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'r. ([< #A(int) | #B] as 'r) => 'r}
  2 │ type b = {"f": 'r. ([< #A(string) | #B] as 'r) => 'r}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  Both polymorphic variants have the constructor [1;33m#A[0m, but their payload types are incompatible.
  Make sure the payload types for [1;33m#A[0m match exactly in both polymorphic variants.
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'r. ([< #A(int) | #B] as 'r) => 'r}
  2 │ type b = {"f": 'r. ([< #A(string) | #B] as 'r) => 'r}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m

```

#### U8-6 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
type b = {"f": 'b 'r. ([< #A('b) | #B] as 'r) => 'b}
let f = (x: a): b => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  2 │ type b = {"f": 'b 'r. ([< #A('b) | #B] as 'r) => 'b}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m
  
  The first polymorphic variant is [1;33mclosed[0m and doesn't include the constructor: [1;31m#B[0m.
  
  Possible solutions:
  - Either make the first variant [1;33mopen[0m so it can accept additional constructors. To do this, make sure the type starts with [1;33m[>[0m instead of [1;33m[[0m
  - Or add the missing constructor to it.

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22

  1 │ type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  2 │ type b = {"f": 'b 'r. ([< #A('b) | #B] as 'r) => 'b}
  3 │ let f = (x: a): b => x
  4 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33mb[0m

```

#### U8-7 — outputs agree

`Main.res`:

```rescript
type a = {"f": 'a. [< #A('a)] => 'a}
type b = {"f": 'a. [< #A('a)] => 'a}
let f = (x: a): b => x
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:1-36

  1 │ type a = {"f": 'a. [< #A('a)] => 'a}
  2 │ type b = {"f": 'a. [< #A('a)] => 'a}
  3 │ let f = (x: a): b => x

  A type variable is unbound in this type declaration.
In field f: 'a. ([< #A('a)] as 'b) => 'a the variable 'b is unbound

```

#### U8-8 — WITNESS

`Main.res`:

```rescript
type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
let f = (x: a): {"f": 'a 'r. ([< #A('a)] as 'r) => 'a} => x
```

Reachability markers: `PROBE:U1`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:59

  1 │ type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
  2 │ let f = (x: a): {"f": 'a 'r. ([< #A('a)] as 'r) => 'a} => x
  3 │ 

  This has type: [1;31ma[0m
  But it's expected to have type: [1;33m{"f": 'a 'b. [< #A('a)] => 'a}[0m
  
  Both polymorphic variants have the constructor [1;33m#A[0m, but their payload types are incompatible.
  Make sure the payload types for [1;33m#A[0m match exactly in both polymorphic variants.

```

#### U8-9 — outputs agree

`Main.res`:

```rescript
let f = (x: [< #A(int)]) => (x: [< #A(int) | #B])
```

Reachability markers: `PROBE:U8`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```


#### U8-10 — WITNESS (added after the search)

`Main.res`:

```rescript
let f = (x: {"f": 'a. [< #A('a)] => 'a}) => (x: {"f": 'a. [< #A(int)] => 'a})
```

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:46

  1 │ let f = (x: {"f": 'a. [< #A('a)] => 'a}) => (x: {"f": 'a. [< #A(int)] =>
    │  'a})
  2 │ 

  This has type: [1;31m{"f": 'a. [< #A('a)] => 'a}[0m
  But it's expected to have type: [1;33m{"f": 'a. [< #A(int)] => 'a}[0m
  The universal variable 'a would escape its scope

```

Rust at `8f73338c3`, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:46-76

  1 │ let f = (x: {"f": 'a. [< #A('a)] => 'a}) => (x: {"f": 'a. [< #A(int)] =>
    │  'a})
  2 │ 

  This has type: [1;31m{"f": 'a. [< #A(int) & ('a0)] => 'a}[0m
  But it's expected to have type: [1;33m'b[0m
  The universal variable 'a0 would escape its scope

```

Fixed by `c51da5f56`: after it the Rust output is OCaml's, byte for byte.

#### U8-11 — WITNESS (added after the search)

`Main.res`:

```rescript
let f = (x: {"f": 'a 'b. ([< #A('a) | #B('b)] => 'a)}) => (x: {"f": 'a 'b. [< #A('b) | #B('a)] => 'a})
```

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:60

  1 │ let f = (x: {"f": 'a 'b. ([< #A('a) | #B('b)] => 'a)}) => (x: {"f": 'a '
    │ b. [< #A('b) | #B('a)] => 'a})
  2 │ 

  This has type: [1;31m{"f": 'a 'b. ([< #A('a) | #B('b)] as 'c) => 'a}[0m
  But it's expected to have type: [1;33m{"f": 'b 'a. 'c => 'b}[0m
  
  Types for field [1;33m"f"[0m are incompatible:
  Field [1;33m"f"[0m in the passed object has type [1;31m'a 'b. 'c => 'a[0m, but is expected to have type [1;33m'b 'a. 'c => 'b[0m.
  
  Possible solutions: 
  - These types are compatible at runtime. You can use the coercion operator to convert to the expected type: [1;33m(x :> {"f": 'b 'b. [< #A('b) | #B('b)] => 'b})
[0m
  

```

Rust at `8f73338c3`, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:60-101

  1 │ let f = (x: {"f": 'a 'b. ([< #A('a) | #B('b)] => 'a)}) => (x: {"f": 'a '
    │ b. [< #A('b) | #B('a)] => 'a})
  2 │ 

  This has type: [1;31m{"f": 'a 'b. [< #A('b) & ('a0) | #B('a) & ('b0)] => 'a}[0m
  But it's expected to have type: [1;33m'c[0m
  The universal variable 'a0 would escape its scope

```

Fixed by `c51da5f56`: after it the Rust output is OCaml's, byte for byte.

#### U8-12 — WITNESS (added after the search)

`Main.res`:

```rescript
let f = (x: {"f": 'a. [< #A('a) | #B] => 'a}) => (x: {"f": 'a. [< #A('a) | #B] => 'a})
```

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:5

  1 │ let f = (x: {"f": 'a. [< #A('a) | #B] => 'a}) => (x: {"f": 'a. [< #A('a)
    │  | #B] => 'a})
  2 │ 

  The implementation Main.res
  does not match the interface (inferred signature):
  
  Actual declaration (Main.res:1:5):
    let f: {"f": 'a. ([< #A('a) | #B] as 'b) => 'a} => {"f": 'a. 'b => 'a}
  
  Expected declaration (Main.res:1:5):
    let f: {"f": 'a. ([< #A('a0) | #B] as 'b) => 'a} => {"f": 'a0. 'b => 'a0}

```

Rust at `8f73338c3`, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:51-85

  1 │ let f = (x: {"f": 'a. [< #A('a) | #B] => 'a}) => (x: {"f": 'a. [< #A('a)
    │  | #B] => 'a})
  2 │ 

  This has type: [1;31m{"f": 'a. [< #A('a) & ('a0) | #B] => 'a}[0m
  But it's expected to have type: [1;33m'b[0m
  The universal variable 'a0 would escape its scope

```

Fixed (see "Fixed and open").

#### U8-13 — WITNESS (added after the search)

`Main.res`:

```rescript
let f = (x: {"f": 'a. [< #A('a) & (int)] => 'a}) => x
```

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:5

  1 │ let f = (x: {"f": 'a. [< #A('a) & (int)] => 'a}) => x
  2 │ 

  The implementation Main.res
  does not match the interface (inferred signature):
  
  Actual declaration (Main.res:1:5):
    let f: {"f": 'a. ([< #A('a) & (int)] as 'b) => 'a} => {"f": 'a. 'b => 'a}
  
  Expected declaration (Main.res:1:5):
    let f: {"f": 'a. ([< #A('a0) & (int)] as 'b) => 'a} => {"f": 'a0. 'b => 'a0}

```

Rust at `8f73338c3`, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Fixed (see "Fixed and open").


### U9 — WITNESS

An explicit :> coercion must compare first-class module types and reach subtype_rec's package fallback (6372–6375), where OCaml has asymmetric constraint completion and package subtyping (4077–4104). Dropping a constraint or comparing distinct constraints must then expose equality being stronger than subtyping or change the error text.

All six candidates hit U9. U9-1 and U9-6 reject valid constraint removal in Rust; U9-3 differs in the printed source type and extra incompatibility detail.

Smallest witness found: **U9-1** (full source and both outputs below).

#### Fixed

The Rust `subtype_rec` (`compiler-rust/src/types/ctype.rs:5957`) had no arm
for two package types: its fallback recorded the pair, and enforcing it
unified the two packages, which asked for the same constraint labels and the
same path. `d958d98c6` adds OCaml's arm (`compiler/ml/ctype.ml:4077-4104`) as
`subtype_package` (`ctype.rs:6416`). It completes both constraint lists with
`complete_type_list` (`ctype.rs:7672`, OCaml `ctype.ml:2135-2169`), records
one constraint per label of the completed target, and for different paths
runs a speculative unification plus `Typemod.package_subtype`
(`typemod.rs:8488`, OCaml `typemod.ml:1224-1236`), comparing the paths with
`eq_package_path`/`normalize_package_path` (`ctype.rs:7802`, `7778`; OCaml
`ctype.ml:2110-2112`, `571-582`). U9-1 and U9-6 are now accepted with OCaml's
JavaScript (`tests/tests/src/package_type_subtype`), and U9-3 prints OCaml's
text (super_errors `package_type_subtype_constraint_mismatch`). U9-2, U9-4
and U9-5 agreed before and still agree; U9-4 is
`package_type_subtype_constraint_added`.

Twenty more coercions were run through both compilers. These differed before
and agree now: dropping the first of two constraints, a nested label
(`S with type M.t = int`), another module type path with the same
signature, with and without a constraint, a module type abbreviation, a
module alias, a module type in a nested module, a functor result, and two
applications of one functor. All are in `package_type_subtype`. The missing
coercion hint of `(x: module(S with type t = int)): module(S) => x` also
came from this cause (super_errors `package_type_subtype_coercion_hint`,
`34b2adf70`). Two further candidates differed through unification itself
rather than this arm, and are fixed by `8c2e46d70` (see U10's last
paragraph): `module(S with type t = int) :> module(T with type t =
string)` for two module types (`package_type_subtype_other_path_mismatch`)
and the annotation `(x: module(S)): module(T) => x`. These must be rejected
and agree before and after: adding a constraint, dropping a value from the
signature, a module type with an extra value, an absent constraint label, a
manifest that depends on another type of the signature, and a constraint of
an already manifest type.

#### U9-1 — WITNESS

`Main.res`:

```rescript
module type S = {type t}
let f = (x: module(S with type t = int)) => (x :> module(S))
```

Reachability markers: `PROBE:U9`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:46-59

  1 │ module type S = {type t}
  2 │ let f = (x: module(S with type t = int)) => (x :> module(S))
  3 │ 

  Type module(S with type t = int) is not a subtype of module(S) 

```

#### U9-2 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
module type T = {}
let f = (x: module(S)) => (x :> module(T))
```

Reachability markers: `PROBE:U9`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:28-41

  1 │ module type S = {let x: int}
  2 │ module type T = {}
  3 │ let f = (x: module(S)) => (x :> module(T))
  4 │ 

  Type module(S) is not a subtype of module(T) 

```

#### U9-3 — WITNESS

`Main.res`:

```rescript
module type S = {type t}
let f = (x: module(S with type t = int)) => (x :> module(S with type t = string))
```

Reachability markers: `PROBE:U9`.

OCaml, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:46-80

  1 │ module type S = {type t}
  2 │ let f = (x: module(S with type t = int)) => (x :> module(S with type t =
    │  string))
  3 │ 

  Type module(S with type t = int) is not a subtype of
    module(S with type t = string) 

```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:46-80

  1 │ module type S = {type t}
  2 │ let f = (x: module(S with type t = int)) => (x :> module(S with type t =
    │  string))
  3 │ 

  Type module(S with type t = string) is not a subtype of
    module(S with type t = string) 
  Type int is not compatible with type string 

```

#### U9-4 — outputs agree

`Main.res`:

```rescript
module type S = {type t}
let f = (x: module(S)) => (x :> module(S with type t = int))
```

Reachability markers: `PROBE:U9`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:28-59

  1 │ module type S = {type t}
  2 │ let f = (x: module(S)) => (x :> module(S with type t = int))
  3 │ 

  Type module(S) is not a subtype of module(S with type t = int) 

```

#### U9-5 — outputs agree

`Main.res`:

```rescript
module type S = {type t}
let f = (x: module(S with type t = int)) => (x :> module(S with type t = int))
```

Reachability markers: `PROBE:U9`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### U9-6 — WITNESS

`Main.res`:

```rescript
module type S = {type t; type u}
let f = (x: module(S with type t = int and type u = string)) => (x :> module(S with type t = int))
```

Reachability markers: `PROBE:U9`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:66-97

  1 │ module type S = {type t; type u}
  2 │ let f = (x: module(S with type t = int and type u = string)) => (x :> mo
    │ dule(S with type t = int))
  3 │ 

  Type module(S with type t = int and type u = string) is not a subtype of
    module(S with type t = int) 

```


### U10 — WITNESS

Eliminating an anonymous functor argument must encounter a package path free in that parameter in nondep_type_rec (14650–14654). A path normalizable to a nondependent module-type alias must then be rejected by Rust but normalized by OCaml (4443–4446) to expose the missing attempt.

U10-1, U10-2, U10-3 and U10-7 hit U10. Type-only results still agree, but retaining a package value in U10-7 exposes rejection of parameter elimination. U10-4 is a parser failure in both compilers; replacing semicolon separators with newlines produced U10-7.

Smallest witness found: **U10-7** (full source and both outputs below).

#### Fixed

The `Tpackage` arm of the Rust `nondep_type_rec`
(`compiler-rust/src/types/ctype.rs:14898` after the fix) returned `None` for
any package path free in the eliminated parameter. OCaml first normalizes it
(`compiler/ml/ctype.ml:4443-4446`, `normalize_package_path` at 571-582) and
fails only when the normalized path still depends on the parameter.
`bff7c8c6f` does the same: with the argument bound to the parameter, `X.T`
normalizes to `S`. U10-7 now builds with OCaml's JavaScript
(`tests/tests/src/package_type_nondep`). U10-1 to U10-6 agreed before and
still agree (U10-1 is in the same fixture).

Ten more applications were run through both compilers. These differed
before and agree now: an abstract module type in the parameter, a module
type in a nested module of the parameter, two functors (`G(Y) = F(Y)`), a
constrained package, a chain of module type abbreviations, the parameter's
module type defined through another abbreviation and the unpacked result
used afterwards, and the result used with an annotation and a coercion. All
are in `package_type_nondep`. An argument constrained to an abstract module
type is rejected by both before and after (super_errors
`package_type_nondep_abstract_argument`).

A functor result that declares `module type T = X.T` next to the value
was still rejected by Rust; OCaml accepts it:

```rescript
module type S = {let x: int}
module F = (X: {module type T = S
let p: module(T)}) => {
  module type T = X.T
  let p = X.p
}
module R = F({module type T = S
module M = {let x = 1}
let p = module(M: T)})
```

The failure was in `Mtype.nondep_supertype`, not in the `nondep_type` of
this place. Thirty-six programs around it (abbreviations of the
parameter's module type in the result, nested, through an alias of the
parameter, a functor returning a functor, a module type that mentions a
type of the parameter, covariant, contravariant and strict positions,
extension constructors, and programs OCaml rejects) were run through both
compilers; four arms of the Rust `nondep_mty`/`nondep_sig`
(`compiler-rust/src/types/typemod.rs:2336-2547`) lacked or shortened
OCaml's (`compiler/ml/mtype.ml:107-162`).

Fixed (`797b660e5`): the `MtyIdent` arm (`typemod.rs:2346`) returned `None`
for a module type path of the parameter. OCaml replaces it by its expansion
through the argument bound to the parameter (`mtype.ml:110-113`). The
program above, the same with a result signature, the module type in a
nested module, in a functor parameter of the result, and an expansion that
mentions a type of the parameter now build with OCaml's JavaScript
(`tests/tests/src/functor_parameter_modtype_expansion`).

Fixed (`6b3de53ff`): a module type declaration whose manifest keeps the
parameter failed the elimination. OCaml walks the manifest as strict and in
a covariant position keeps the declaration abstract (`mtype.ml:147-160`);
the walk now carries OCaml's variance (`mtype.ml:105`, flipped for a
functor parameter at 119-123). Accepted programs are in
`tests/tests/src/functor_parameter_modtype_abstract`; super_errors
`functor_parameter_modtype_abstract_fallback` (a structure constrained to
the abstract result) differed before, `functor_parameter_modtype_contravariant`
agreed before and still does.

Fixed (`5038035c3`): `nondep_sig` passed `is_covariant = true` to
`nondep_type_decl` in every position; OCaml passes `va = Co`
(`mtype.ml:139-140`, `ctype.ml:4489-4497`). super_errors
`functor_parameter_modtype_type_contravariant` and
`functor_parameter_modtype_type_strict` differed before;
`functor_parameter_modtype_type_covariant` agreed before.

Fixed (`7375247d4`): extension constructors kept the parameter in their
arguments, result type and extended path; `nondep_extension_constructor`
(`typemod.rs:2494`) ports OCaml's (`ctype.ml:4521-4552`).
`tests/tests/src/functor_parameter_modtype_extension` builds with OCaml's
JavaScript; super_errors `functor_parameter_modtype_extension_argument` and
`functor_parameter_modtype_extension_path` were accepted by Rust before.

Open: the `MtyAlias` arm (`typemod.rs:2359`, OCaml `mtype.ml:114-117`)
still fails for an alias of the parameter. No program reached it with such
a path (a temporary trace over all the programs fired once, for an alias to
a top-level module): OCaml and Rust strengthen an alias of a functor
argument instead of keeping it (`env.ml:926-933`). Two differences found on
the way are outside this function group and differ on trunk without a
functor application: `module R = {module Y = {module type T = S}  module
type T = Y.T}` followed by `module M: R.T = ...` stops Rust with an
internal "Inferred signature inclusion failed" (inferred signature
coercion); `R.E({v: 1})` for `exception E({v: int})` in a module `R` is
rejected by Rust ("v refers to a record field"). An alias `module M = N` in
a functor parameter's signature used as `module Z = X.M` gives OCaml
`Z: undefined` and Rust `Z: X.N` in the JavaScript, before and after.

Unifying, comparing and including two package types had the same kind of
fault as the U9 arm. Unification, `moregen`, `Ctype.equal` and the
inclusion check's type equality asked for the same labels and the same path
before relating the constraint types. `8c2e46d70` routes all four through
`unify_package` (`ctype.rs:7825`, OCaml `ctype.ml:2172-2181`; the arms at
`ctype.rs:9008`, `10411`, `11580`, `includemod.rs:4591`; OCaml 2416-2424,
2969-2974, 3252-3257). It completes both lists, relates the types first,
then accepts the same normalized path or mutual `package_subtype`. Programs
OCaml accepts that Rust rejected are in `tests/tests/src/package_type_unify`
and `package_type_unify_interface` (another module type with the same
signature in an annotation, an array, through an abbreviation, a value and a
type manifest against an interface). The error for two such module types
with mismatched constraints now names the incompatible parts as OCaml does
(super_errors `package_type_unify_constraint_mismatch`).
`package_type_unify_missing_value` (only one module type included in the
other) was rejected before and still is.

#### U10-1 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
module F = (X: {module type T = S}) => {type t = module(X.T)}
module R = F({module type T = S})
```

Reachability markers: `PROBE:U10`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {};
}

let R = {};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

#### U10-2 — outputs agree

`Main.res`:

```rescript
module F = (X: {module type T}) => {type t = module(X.T)}
module R = F({module type T = {let x: int}})
```

Reachability markers: `PROBE:U10`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {};
}

let R = {};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text

  Warning number 32
  Main.res:2:32-41

  1 │ module F = (X: {module type T}) => {type t = module(X.T)}
  2 │ module R = F({module type T = {let x: int}})
  3 │ 

  unused value x.

```

#### U10-3 — outputs agree

`Main.res`:

```rescript
module type S = {type t}
module F = (X: {module type T = S}) => {type t = module(X.T with type t = int)}
module R = F({module type T = S})
```

Reachability markers: `PROBE:U10`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {};
}

let R = {};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

#### U10-4 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
module F = (X: {module type T = S; let p: module(T)}) => {let p = X.p}
module R = F({module type T = S; module M = {let x = 1}; let p = module(M: T)})
```

Reachability markers: none.

Both compilers, implementation exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:2:34

  1 │ module type S = {let x: int}
  2 │ module F = (X: {module type T = S; let p: module(T)}) => {let p = X.p}
  3 │ module R = F({module type T = S; module M = {let x = 1}; let p = module(
    │ M: T)})
  4 │ 

  I'm not sure what to parse here when looking at ";".

```

#### U10-5 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
module A = {module type T = S}
module F = (X: {module type T = S}) => {type t = module(X.T)}
module R = F(A)
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let A = {};

function F(X) {
  return {};
}

let R = {};

exports.A = A;
exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

#### U10-6 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
let p = {module A = {module type T = S; module M = {let x = 1}}; module(A.M: A.T)}
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {
  x: 1
};

let p = M;

exports.p = p;
/* No side effect */
```

stderr:

```text
```

#### U10-7 — WITNESS

`Main.res`:

```rescript
module type S = {let x: int}
module F = (X: {module type T = S
let p: module(T)}) => {let p = X.p}
module R = F({module type T = S
module M = {let x = 1}
let p = module(M: T)})
```

Reachability markers: `PROBE:U10`.

OCaml, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

let M = {
  x: 1
};

let R = {
  p: M
};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

Rust, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:4:12-6:22

  2 │ module F = (X: {module type T = S
  3 │ let p: module(T)}) => {let p = X.p}
  4 │ module R = F({module type T = S
  5 │ module M = {let x = 1}
  6 │ let p = module(M: T)})
  7 │ 

  This functor has type
  (
    X: {
      module type T = S
      let p: module(T)
    },
  ) => {
    let p: module(X.T)
  } The parameter cannot be eliminated in the result type.
   Bind the argument to a module identifier.

```


### U11 — NOT REACHED

Unification must see exactly one empty-binder Tpoly operand after earlier dispatch, reaching Rust's one-sided unwrap arms (8772–8779), rather than the paired-poly arms also present in OCaml (2413–2424). Unwrapping must change the resulting constraint failure or inferred output to demonstrate a difference.

No U11 marker ran in these six candidates. Ordinary object literals, inferred access and polymorphic reads/writes did not leave a one-sided empty-binder Tpoly at those late unify arms; the earlier paired/variable handling or instantiation prevents these candidates from demonstrating the condition. All six outputs agree; no general unreachability claim is made.

#### U11-1 — outputs agree

`Main.res`:

```rescript
let o = {"x": 1}
let n = o["x"]
```

Reachability markers: `PROBE:U3`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let o = {
  x: 1
};

let n = o.x;

exports.o = o;
exports.n = n;
/* n Not a pure module */
```

stderr:

```text
```

#### U11-2 — outputs agree

`Main.res`:

```rescript
let get = o => o["x"]
let n = get({"x": 1})
```

Reachability markers: `PROBE:U3`.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function get(o) {
  return o.x;
}

let n = ({
  x: 1
}).x;

exports.get = get;
exports.n = n;
/* n Not a pure module */
```

stderr:

```text
```

#### U11-3 — outputs agree

`Main.res`:

```rescript
type t = {"id": 'a. 'a => 'a}
let f = (o: t) => o["id"](1)
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(o) {
  return o.id(1);
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### U11-4 — outputs agree

`Main.res`:

```rescript
type t = {@set "id": 'a. 'a => 'a}
let set = (o: t) => o["id"] = (x => x)
```

Reachability markers: none.

Both compilers, implementation exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function set(o) {
  o.id = x => x;
}

exports.set = set;
/* No side effect */
```

stderr:

```text
```

#### U11-5 — outputs agree

`Main.res`:

```rescript
type t = {@set "id": 'a. 'a => 'a}
let set = (o: t) => o["id"] = (x => 1)
```

Reachability markers: none.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:32-37

  1 │ type t = {@set "id": 'a. 'a => 'a}
  2 │ let set = (o: t) => o["id"] = (x => 1)
  3 │ 

  This field value has type [1;31mint => int[0m
  which is less general than [1;33m'a. 'a => 'a[0m

```

#### U11-6 — outputs agree

`Main.res`:

```rescript
let f = (o: {"x": int}) => o["x"]
let n = f({"x": "bad"})
```

Reachability markers: `PROBE:U3`.

Both compilers, implementation exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:11-22

  1 │ let f = (o: {"x": int}) => o["x"]
  2 │ let n = f({"x": "bad"})
  3 │ 

  This has type: [1;31m{"x": string}[0m
  But this function argument is expecting: [1;33m{"x": int}[0m
  
  Types for field [1;33m"x"[0m are incompatible:
  Field [1;33m"x"[0m in the passed object has type [1;31mstring[0m, but is expected to have type [1;33mint[0m.
  
  You can convert [1;33mstring[0m to [1;33mint[0m with [1;33mInt.fromString[0m.

```


## Third round: differences found while fixing

### Q5 — an inline record of an extension constructor through a module path

Commands are the ones in "Scope, calibration and reproducibility". Each program
was run with `bsc -w +A -bs-jsx 4 -color never Main.res` through both
compilers; the program split across two units was built as a project with
`rescript build-reference --bsc <OCaml bsc>` and `rescript build`. Verdicts
before the fixes (trunk `a2777909d`) and after them:

| Program | OCaml | Rust before | Rust after |
| --- | --- | --- | --- |
| `R.E({v: 1})`, `exception E({v: int})` in `R` | accepts | rejects (unbound label `v`) | agrees |
| `R.C({v: 1})`, `type t += C({v: int})` in `R` | accepts | rejects | agrees |
| `R.A({w: 1})`, `type u = A({w: int})` in `R` | accepts | agrees | agrees |
| `E({v: 1})` inside `R` | accepts | agrees | agrees |
| `open R` then `E({v: 1})` (also `open! R`) | accepts | rejects | agrees |
| `open R` then `E(1)` | rejects ("expects an inlined record argument") | accepts, `_1: 1` | agrees |
| `open R` then `E({v: 1, w: ""})` for two fields | accepts | rejects (arity 2) | agrees |
| `module A = R` then `A.E({v: 1})` | accepts | rejects | accepted, JavaScript differs (open, below) |
| `switch x { \| R.E({v}) => v }` | accepts | rejects | agrees |
| `R.S.E({v: 1})` and `\| R.S.E({v})`, two levels | accepts | rejects | agrees |
| punned `R.E({v, w})` | accepts | rejects | agrees |
| optional field `w?: string`, `{v: 1}`, `w: "x"`, `w: ?Some("y")` | accepts | rejects | agrees |
| spread `R.E({...r, v: 2})` of a matched `R.E(r)` | accepts | rejects | agrees |
| field access `r.v` of a matched `R.E(r)` | accepts | rejects | agrees |
| `R.E` next to a local `exception E({w: string})` | accepts | rejects | agrees |
| another unit's `Lib.E({v: 1})`, `Lib.C({v: 2})`, `\| Lib.E({v})` | accepts | rejects | agrees |
| wrong field `R.E({x: 1})` | rejects: "The field x is not part of the record argument for the R.E constructor" | rejects: "x refers to a record field, but no corresponding record type is in scope" | agrees |
| extra field `R.C({v: 1, z: 2})` | rejects | rejects, other text | agrees |
| missing field `R.C({w: 1})` | rejects at 5:13-18: "Some required record fields are missing: v." | rejects at 5:14, unbound label | agrees |
| wrong field `R.A({x: 1})` of a variant | rejects: "...for the R.u.A constructor" | agrees | agrees |

#### Fixed

- `42865599f`: the record type of an inline record is named by the
  constructor's path (`R.E`). OCaml's `Env.find_type_full`
  (`compiler/ml/env.ml:773-811`) classifies that path with
  `Path.constructor_typath` and reads the constructor from the variant's
  declaration (`Cstr`), by exact identifier (`LocalExt`, `find_same`) or
  from the components of the module (`Ext`). The Rust
  `lookup_inline_record_decl_for_path`
  (`compiler-rust/src/types/typecore.rs:16430`, before the fix 16496)
  searched the constructors in scope by the bare name `E`, so through any
  module path it found nothing, `extract_concrete_record_type_info` had no
  record and every label was unbound. It now takes the three cases of
  `find_type_full`; the name-based search it shared with
  `with_record_labels` (typecore.rs:16348) is deleted. Fixtures:
  `tests/tests/src/inline_record_extension_path`,
  `inline_record_extension_second_unit` (with `inline_record_extension_lib`),
  super_errors `inline_record_extension_wrong_field`,
  `inline_record_extension_missing_field` and
  `inline_record_extension_variant_wrong_field` (agreed before).
- `62c757dc0`: `open` installs the module's component table
  (`env.ml:1841-1877`), whose extension constructors come from
  `Datarepr.extension_descr` (`env.ml:1560-1565`, `datarepr.ml:218-240`): an
  inline record is one argument of the record type the constructor's path
  names, with `cstr_inlined` set. The Rust open
  (`add_signature_to_env_with_options_inner`,
  `compiler-rust/src/cmi/persistent_env.rs:8432`) built its own description
  that spread the fields into a tuple and dropped `cstr_inlined`. It now
  uses the component table's `env_lazy::extension_constructor_description`
  (`compiler-rust/src/types/env_lazy.rs:521`). Fixtures:
  `tests/tests/src/inline_record_extension_open`, super_errors
  `inline_record_extension_open_tuple_argument` and
  `inline_record_extension_open_arity`.

#### Open

Through a module alias, `module A = R` then `A.E({v: 1})` is now accepted,
but the JavaScript differs: Rust emits `let e_0 = A.E;` and
`RE_EXN_ID: e_0`, OCaml `RE_EXN_ID: E`. The same difference exists before
these fixes and without an inline record (`exception E(int)`, `A.E(1)`).
Both typed trees hold `Texp_construct "A.E"`; the raw Lambda differs: OCaml
`(makeblock ext (field:E/0 R/1001) 1)`, Rust `(field:E/0 A/1003)`. OCaml
translates the constructor's path with `Transl_path.transl_extension_path`,
which normalizes the prefix through the alias (`compiler/ml/transl_path.ml:43-46`,
`Env.normalize_path_prefix`); the Rust `translate_extension_path_raw`
(`compiler-rust/src/raw_lambda/convert.rs:3705`) does not reach the alias
target for a local `module A = R`. That is the Lambda translation of
modules, not constructor typing.

Fixed under E1 below (`4be340ef5`): the translation now normalizes the path
in the construction's environment; `A.E({v: 1})` through `module A = R`
agrees after the merge of both.

### Q1 — a module type abbreviation of a module type in a submodule

```rescript
module type S = {let x: int}
module R = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
}
module M: R.T = {
  let x = 2
}
```

OCaml compiles the unit; Rust rejected it: "The implementation Main.res does
not match the interface (inferred signature): In module M: Actual module
type: Y.T Expected module type: R.T". The printed `Y.T` was the cause, not a
printing matter: two places read the declaration of `R.T` from `R`'s own
signature, where it is written `Y.T` with the `Y` bound inside `R`, instead
of from `R`'s components, where OCaml's `Env` stores it prefixed as `R.Y.T`
(`Subst.add_module id (Pdot (path, name))` in `components_of_module_maker`,
`compiler/ml/env.ml:1555-1590`). Outside `R`, `Y.T` names nothing, so the
expansion stopped there and the two paths compared unequal.

#### Fixed

- `1399d0e44`: `Mtype.strengthen` scrapes `Mty_ident p` with
  `Env.find_modtype_expansion` (`compiler/ml/mtype.ml:21-25`). The Rust
  scrape (`scrape_modtype_ident_for_strengthen` in
  `strengthen_module_type_for_module_access_path`,
  `compiler-rust/src/types/ctype.rs:3630`) used `Env::lookup_modtype`, whose
  dotted case scans the parent module's raw signature. Strengthening `M`
  when the unit is checked against its inferred signature
  (`Includemod.compunit`, `compiler/ml/typemod.ml:1812-1815`, through
  `module_declarations`, `includemod.ml:396-413`) gave `Y.T`. It now calls
  `typemod::find_modtype_expansion` (`typemod.rs:11011`), which reads the
  parent's components. Fixtures: `tests/tests/src/modtype_abbreviation_submodule`,
  `modtype_abbreviation_submodule_interface`, super_errors
  `modtype_abbreviation_value_mismatch` (agreed before).
- `827faf1c4`: `Includemod.try_modtypes` expands an alias with
  `Env.find_module` and a module type path with `Env.find_modtype_expansion`
  (`includemod.ml:223-236`). The local expansion of the Rust check
  (`expand_local` in `modtypes_inner`, `compiler-rust/src/types/includemod.rs:1287`,
  dotted arm at 1316) scanned the parent's raw signature in the same way, so
  `module N: R.Y.T = M` for `M: R.T` was rejected with "Actual module type:
  Y.T", and a missing value in a constraint on such a module was reported
  as that module type mismatch instead of "The value `y` is required but
  not provided". The dotted arm now reads a module through
  `lookup_module_in_resolved_path` and a module type through
  `find_modtype_expansion`. Fixtures:
  `tests/tests/src/modtype_abbreviation_constraint_target`, super_errors
  `modtype_abbreviation_alias_missing_value` and
  `modtype_abbreviation_abstract_implementation` (agreed before).

Twenty programs around the witness were run through both compilers
(commands as in "Scope, calibration and reproducibility"). Before / after:

| Program | OCaml | Rust before | Rust after |
| --- | --- | --- | --- |
| the witness (one submodule) | accepts | rejects | accepts |
| two submodules (`R.Y.Z.T`) | accepts | rejects | accepts |
| submodule that is a module alias | accepts | rejects | accepts |
| `R` a functor's result | accepts | rejects | accepts |
| `Y.T` used in `R` before `T` is declared | accepts | rejects | accepts |
| through `module type of R` | accepts | accepts | accepts |
| abstract module type through an alias, functor parameter | accepts | accepts | accepts |
| constrained by the abbreviation, its target, `S`, the abbreviation | accepts | rejects | accepts |
| with an interface declaring `M: R.T` | accepts | rejects | accepts |
| with an interface declaring `M: R.Y.T` | accepts | rejects | accepts |
| abbreviation used inside `R` | accepts | accepts | accepts |
| `module M: R.T` as an item of a module type | accepts | rejects | accepts |
| functor parameter of type `R.T` | accepts | rejects | accepts |
| `M: R.T` with `x: string` | rejects | same text | same text |
| `M: R.T` without `x` | rejects | same text | same text |
| interface `M: R.T`, implementation lacks `x` | rejects | same text | same text |
| interface's `R.T` is another module type | rejects | same text | same text |
| abstract `R.T` implemented by a structure | rejects | same text | same text |
| `module N: {x, y} = M` for `M: R.T` | rejects | other text | same text |
| `module N: U = M`, `U` with `x: string` | rejects | other text | same text |

### A3 — module aliases of a functor argument

The witness: a module alias declared in a functor parameter's signature and
re-exported from the functor body.

```rescript
module N = {let x = 1}
module F = (X: {
  module N: {let x: int}
  module M = N
}) => {module Z = X.M}
module R = F({
  module N = N
  module M = N
})
let y = R.Z.x
```

OCaml emitted `Z: undefined` in the body of `F` and in `R`, and `let y = 1`;
Rust emitted `Z: X.N`, `Z: N` and `let y = R.Z.x` read through `R`. Both
compilers' `-drawlambda` show where it starts: OCaml binds
`Z/1008 =a module_alias`, Rust `Z/1008 =a (field:N/0 X/1007)`. The
translation of a module expression (`convert_module_expr_raw0`,
`compiler-rust/src/raw_lambda/convert.rs:4196`, the counterpart of
`transl_module0` at `compiler/ml/translmod.ml:257-261`) compiles any
expression whose type is an alias to `module_alias`, as OCaml does for
`Mty_alias (Mta_absent, _)`; the type of `X.M` was the difference.

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from the thin-LTO release build); each program is
`Main.res` (plus `Main.resi` where noted) compiled by both with
`-I . -I packages/@rescript/runtime/lib/rescript`, and stdout, stderr and the
exit status compared byte for byte.

#### Fixed

- `5d4b69ea3`: eliminating the parameter from the result of a functor
  applied to a structure (`Mtype.nondep_supertype`) replaces an alias of a
  module of the parameter by that module's type, read through the argument
  (`compiler/ml/mtype.ml:114-117`). The alias arm of the Rust `nondep_mty`
  (`compiler-rust/src/types/typemod.rs:2340`) returned `None`, so Rust
  rejected `include X` of a parameter with an alias ("The parameter cannot
  be eliminated in the result type") where OCaml accepts it. It now reads the
  module's type through the argument's component table
  (`tests/tests/src/functor_argument_alias_include`).
- `a5eda8581`: `module Z = path` strengthens the declared module type with
  `Mtype.strengthen ~aliasable`, `aliasable` false for a path into a functor
  parameter (`compiler/ml/typemod.ml:1238-1258`), and `strengthen` leaves an
  alias as it is (`compiler/ml/mtype.ml:30-38`). The Rust call
  (`compiler-rust/src/types/typemod.rs:14861`) scraped the alias to the
  strengthened signature of `X.N` and always strengthened as if the path
  were aliasable. `X.M` now keeps `Mty_alias (Mta_absent, X.N)` and compiles
  to `module_alias`, and `module Z = X.N` keeps the strengthened types of
  `N`'s submodules instead of aliases of the parameter's modules, which
  could not be eliminated from the result. Fixtures:
  `tests/tests/src/functor_argument_alias_module`,
  `functor_argument_alias_interface` (with an interface) and super_errors
  `functor_argument_alias_signature_mismatch`.

Programs run through both compilers, before (at `a2777909d`) and after
`a5eda8581` (exit status of OCaml; DIFFER lists Rust's when it differs):

| Program | Before | After |
| --- | --- | --- |
| the witness | DIFFER (Rust `Z: X.N`) | agree, 0 |
| alias not used in the body (`module Z = X.M` and a value) | DIFFER | agree, 0 |
| alias used in the body (`Z.x`) | DIFFER | agree, 0 |
| alias accessed as a value (`X.M.x`) | agree, 0 | agree, 0 |
| re-exported under a signature (`: {module Z: {let x: int}}`) | agree, 0 | agree, 0 |
| alias of a module outside the parameter (`module M = N`, top-level `N`) | DIFFER | agree, 0 |
| an unused alias outside the parameter next to a value | DIFFER | agree, 0 |
| two levels of alias (`L = M`, `M = N`) | DIFFER | agree, 0 |
| functor applied to a named module | DIFFER | agree, 0 |
| the same alias in an ordinary signature, no functor | agree, 0 | agree, 0 |
| first-class module built from the alias (`module(X.M: T)`) | agree, 0 | agree, 0 |
| interface exporting `F` and `R` | OCaml 2 (crash), Rust 0 | OCaml 2 (crash), Rust 0 |
| interface exporting only `R` | DIFFER | agree, 0 |
| a submodule of the parameter (`module Z = X.N`, `Z.K.x`) | DIFFER (Rust 2) | agree, 0 |
| the parameter itself (`module Z = X`) | agree, 0 | agree, 0 |
| an alias inside a nested functor of the body | DIFFER | agree, 0 |
| `include X` | DIFFER (Rust 2) | agree, 0 |
| `include X` of a named signature, then `M.x` | DIFFER (Rust 2) | agree, 0 |
| parameter's `M` not an alias | agree, 0 | agree, 0 |
| parameter typed `module type of A` | agree, 0 | agree, 0 |
| nested functor with `module type of X` | agree, 0 | agree, 0 |
| alias in a constrained argument inside another functor | DIFFER | agree, 0 |
| argument's `M` not an alias of its `N` (rejected) | agree, 2 | agree, 2 |
| wrong member through the result (`R.Z.z`, rejected) | agree, 2 | agree, 2 |
| wrong type in the body (`let v: string = Z.x`, rejected) | agree, 2 | agree, 2 |
| body against a mismatching result signature (rejected) | agree, 2 | agree, 2 |

#### Open

With an interface that exports `F` itself
(`module F: (X: {module N: {let x: int}
module M = N}) => {module Z: {let x: int}}`), OCaml prints warning 32 and
then stops with `Fatal error: exception Failure("File
\"compiler/core/lam_dce.ml\", line 33, characters 31-38X/1034 not found")`:
the coercion of `Z` against the interface is `Tcoerce_alias (X.N, _)`
(`compiler/ml/includemod.ml:224-237`), which names the parameter `X`
outside the coerced functor's own parameter `funarg`. Rust prints the same
warning, exits 0 and emits `Z: X.N` in `function F(funarg)`, a reference to
an unbound `X`. This is a defect of both compilers, and the reference
crashes; it was left as it is.

### E1 - an extension constructor read through a module alias

The witness: an extension constructor named through a local module alias.

```rescript
module R = { exception E(int) }
module A = R
let e = A.E(1)
```

OCaml emitted `let e = { RE_EXN_ID: E, _1: 1 }` followed by `let A;`; Rust
emitted `let A;`, then `let e_0 = A.E; let e = { RE_EXN_ID: e_0, _1: 1 }`,
a read of a field of `A`, which is undefined at runtime. `-drawlambda`:
OCaml reads `field:E/0 R`, Rust `field:E/0 A`. A value read the same way
(`A.x`) compiled as OCaml compiles it.

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from the thin-LTO release build, the runtime built by
`build-reference` with the OCaml `bsc`); each program is `Main.res`
compiled by both with `-I . -I packages/@rescript/runtime/lib/rescript`,
and stdout, stderr, the exit status and the JavaScript compared byte for
byte. The two-unit program is a project with `Other.res` and `Main.res`,
built by `rescript build-reference --bsc <OCaml bsc>` and by
`rescript build`, its JavaScript compared byte for byte.

#### Fixed

- `4be340ef5`: OCaml's `transl_extension_path` is `transl_value_path`
  (`compiler/ml/transl_path.ml:43-46`), which normalizes the path's prefix
  with `Env.normalize_path_prefix` in the environment it is given: the
  construction's `e.exp_env` (`compiler/ml/translcore.ml:1417`), the
  record's (`translcore.ml:1902`), a local exception's
  (`translcore.ml:1551`), the declaring item's `item.str_env` for a rebind
  (`compiler/ml/translmod.ml:373,381`, `translcore.ml:53`), the pattern's
  `pat_env` (`compiler/ml/matching.ml:2363`). The Rust
  `translate_extension_path_raw`
  (`compiler-rust/src/raw_lambda/convert.rs:3705` before the fix) called
  `translate_value_path_raw`, which normalizes in the converter's
  unit-level environment, where an alias declared in the unit is not
  bound; patterns already used `pat_env` (`raw_lambda/matching.rs:7427`),
  which is why matching agreed. Constructions, records and local
  exceptions now pass the expression's environment. Structure items never
  recorded `str_env` (always `EnvRef(0)` in
  `compiler-rust/src/types/typemod.rs`); an `exception` or `type +=` item
  with a rebind now stores the environment before it
  (`extension_item_env`, `typemod.rs:16484`), and the converter normalizes
  the rebind there. Fixtures: `tests/tests/src/extension_alias_path_construct`,
  `extension_alias_path_rebind`, `extension_alias_path_unit` with
  `extension_alias_path_unit_alias` (an alias of another unit).

Since the merge of trunk at `393969158` (Q5, an inline record of an
extension constructor through a module path), `56053c43c` adds the inline
record through an alias, `AI.E({a: 1, b: "x"})` and `| AI.E({a}) => a`, to
`extension_alias_path_construct`; it needs Q5 to be accepted and this fix to
read `RI`.

Programs run through both compilers, before (at `112f68648`), after
`4be340ef5`, and after the merge of trunk at `393969158` (`dcfa51c78`). OCaml
accepts every one (exit 0); DIFFER is a difference in the JavaScript or the
diagnostics:

| Program | Before | After | After the merge |
| --- | --- | --- | --- |
| the witness, `A.E(1)` | DIFFER | agree | agree |
| constant exception `A.E` | DIFFER | agree | agree |
| `switch x { \| A.E(n) => n }` | agree | agree | agree |
| `try g() catch { \| A.E(n) => n }` | agree | agree | agree |
| extensible type `A.C(1)` | DIFFER | agree | agree |
| extensible constant `A.C`, then `\| A.C =>` | DIFFER | agree | agree |
| inline record `A.E({a: 1, b: "x"})` | DIFFER (Rust 2) | DIFFER (Rust 2) | agree |
| two aliases `B = A`, `B.E(1)`, `\| B.E(n)` | DIFFER | agree | agree |
| alias of a submodule `A = R.S` | DIFFER | agree | agree |
| alias declared after `open O` | DIFFER | agree | agree |
| `open A`, then `E(1)` | DIFFER | agree | agree |
| alias of another unit (`A = Other`, `A.E`, `A.C`, `\| A.E(n)`) | DIFFER | agree | agree |
| alias inside a functor body of a module outside it | DIFFER | agree | agree |
| alias of the functor's parameter (`A = X`, `A.E(1)`, `\| A.E(n)`) | agree | agree | agree |
| `throw(A.E(1))` | DIFFER | agree | agree |
| `include R` in a third module, `I.E(1)` and `A.E(2)` | DIFFER | agree | agree |
| rebind `exception F = A.E` | DIFFER | agree | agree |
| value through the alias, `A.x` | agree | agree | agree |
| `type R.t += D = A.C`, `D(1)` | DIFFER | agree | agree |
| local `exception L = A.E` in a function, `L(1)` | DIFFER (Rust 2) | DIFFER (Rust 2), open | DIFFER (Rust 2), open |
| inline record `R.E({a: 1, b: "x"})`, no alias | DIFFER (Rust 2) | DIFFER (Rust 2) | agree |
| local `exception L = R.E`, no alias | DIFFER (Rust 2) | DIFFER (Rust 2), open | DIFFER (Rust 2), open |
| local `exception L = E`, top-level `E`, no alias | DIFFER (Rust 2) | DIFFER (Rust 2), open | DIFFER (Rust 2), open |

#### Open

- A local `exception L = E` in an expression is typed by Rust as a
  constructor without arguments ("This variant constructor L expects 0
  arguments, but it's being passed 1"), alias or not. OCaml types it with
  `Typedecl.transl_exception` (`compiler/ml/typecore.ml:3763`), whose
  `Pext_rebind` arm reads the rebound constructor's arguments
  (`compiler/ml/typedecl.ml:1694`). The Rust `type_letexception`
  (`compiler-rust/src/types/typecore.rs:17753`) answers `Pext_rebind`
  with no arguments (`typecore.rs:17892`) and builds a `Text_decl`, so it
  also creates a new exception instead of rebinding. The fix is in
  `typecore.rs`, outside this change.

### L1 - a local exception that rebinds another

The witness: a local exception in a function that rebinds a top-level one.

```rescript
exception E(int)
let f = x => {
  exception L = E
  switch x {
  | L(n) => n
  | _ => 0
  }
}
```

OCaml accepted it with warning 38 ("exception L is never used to build
values. (However, this constructor appears in patterns.)", `3:3-17`), and
its JavaScript tests `x.RE_EXN_ID === E` and returns `x._1`. Rust rejected
it at `5:5-8`: "This variant constructor L expects 0 arguments, but it's
being passed 1."

Commands as in "Scope, calibration and reproducibility": the OCaml `bsc`
from `dune build`, Rust from thin-LTO release builds of `acf84ba17` (before)
and of the fix (after), the runtime built by `build-reference` with the
OCaml `bsc`; each program is `Main.res` compiled by both with
`-I . -I packages/@rescript/runtime/lib/rescript`, and stdout (the
JavaScript), stderr (the diagnostics), and the exit status compared byte for
byte.

#### Fixed

- `cd3f30219`: OCaml types `Pexp_letexception` with
  `Typedecl.transl_exception` (`compiler/ml/typecore.ml:3762-3763`), the
  function an `exception` structure item uses
  (`compiler/ml/typedecl.ml:1895-1911`); its `Pext_rebind` arm of
  `transl_extension_constructor` takes the arguments, the result type, the
  inline record and the path of the constructor it rebinds
  (`typedecl.ml:1694-1749`). The Rust `type_letexception`
  (`compiler-rust/src/types/typecore.rs:17753` before the fix) was a copy of
  the item's translation whose `Pext_rebind` arm (`typecore.rs:17892`)
  returned a constructor with no arguments and built a `Text_decl`, so a
  rebind became a new exception without arguments: matching it with an
  argument was rejected, and `exception L = E0` compiled to
  `Primitive_exceptions.create("L")`. The copy also skipped what the item
  checked (the duplicate-label and `@as` checks of an inline record, the
  unbound type variable check, `reset_type_variables`, the lookup of the
  rebound name). The item's translation is now `transl_exception`
  (`compiler-rust/src/types/typemod.rs:16506`), called by the
  `Pstr_exception` item (`typemod.rs:19152`) and by `type_letexception`
  (`typecore.rs:17756`); the copy is deleted. Fixtures:
  `tests/tests/src/local_exception_rebind_cases` (every accepted program
  below in one module, with the controls), and the super_errors fixtures
  `local_exception_rebind_not_exception`, `_unbound`, `_argument_count`,
  `_wrong_field`, `_decl_unbound_type_var`, `_pattern_only` (warning 38 for
  a constructor seen only in patterns) and `_unused` (agreed before).

The three local-exception rows left open under E1 above (`exception L =
A.E`, `= R.E`, `= E`, each with `L(1)`) are programs 8, 9 and 5 below and
now agree.

Programs run through both compilers. OCaml status 0 is accepted, 2
rejected; DIFFER is a difference in the JavaScript, the diagnostics or the
status:

| # | Program | OCaml | Before (Rust) | After (Rust) |
| --- | --- | --- | --- | --- |
| 1 | the witness, one argument, used in a pattern | 0, warning 38 | DIFFER (2) | agree |
| 2 | no argument, `\| L =>` | 0, warning 38 | DIFFER (0, a new exception `"L"`) | agree |
| 3 | two arguments, `\| L(n, s)` | 0, warning 38 | DIFFER (2) | agree |
| 4 | inline record, `\| L({a, b})` and `L({a: 1, b: "x"})` | 0, warning 38 | DIFFER (2) | agree |
| 5 | used only to build, `L(1)` | 0 | DIFFER (2) | agree |
| 6 | pattern and construction, `\| L(n) => L(n + 1)` | 0 | DIFFER (2) | agree |
| 7 | not used at all | 0, warning 38 "unused exception L" | agree | agree |
| 8 | through a module path, `exception L = M.E` | 0, warning 38 | DIFFER (2) | agree |
| 9 | through a module alias, `exception L = A.E` | 0, warning 38 | DIFFER (2) | agree |
| 10 | a local `exception K(int)` rebound by a local `exception L = K` | 0 | DIFFER (2) | agree |
| 11 | control: local declaration `exception L(int, string)` | 0 | agree | agree |
| 12 | in a function called twice, `throw(L(x))` caught as `E1(n)` | 0 | DIFFER (2) | agree |
| 13 | rebind of the predefined `Failure`, `\| L(s)` | 0, warning 38 | DIFFER (2) | agree |
| 14 | control: item rebind `exception F = E` | 0 | agree | agree |
| 15 | rebind of a variant constructor `A` of `type t` | 2, `3:17` "The constructor A has type t but was expected to be of type exn" | DIFFER (0) | agree |
| 16 | rebind of an unbound `Nope` | 2, `2:17-20` "The variant constructor Nope can't be found." | DIFFER (0) | agree |
| 17 | `\| L(n, m)` for one argument | 2, `5:6-11` "This pattern matches values of type ('a, 'b)" | DIFFER (2, `5:5-11` "expects 0 arguments, but it's being passed 2") | agree |
| 18 | `\| L({c})` for an inline record `{a, b}` | 2, `5:8` "The field c is not part of the record argument for the L constructor" | DIFFER (2, `5:5-10` "expects 0 arguments") | agree |
| 19 | local declaration `exception L('a)` | 2, `2:16` "Unbound type parameter 'a" | DIFFER (0) | agree |
| 20 | `L("x")` for an `int` argument | 2, `4:5-7` "This has type: string" | DIFFER (2, `4:3-8` "expects 0 arguments") | agree |
| 21 | rebind of `Nope.E`, an unbound module | 2, `2:17-22` "The module or file Nope can't be found." | DIFFER (0, warning 38) | agree |

#### Fixed: a rebind marks the constructor it rebinds as used

- The commit that adds this paragraph: OCaml's `Pext_rebind` arm marks the constructor it rebinds
  as used: `Env.mark_constructor usage env (Longident.last lid.txt) cdescr`
  (`compiler/ml/typedecl.ml:1694-1700`). The usage is `Positive`, or
  `Privatize` when the new constructor is private and the rebound one is
  not. The Rust `lookup_rebind_constructor`
  (`compiler-rust/src/types/typemod.rs:555`) did not mark it, so every
  rebound constructor kept the warning 38 it would have had without the
  rebind. This applied to exception items, local exceptions and
  `type t += B = A` alike. It now calls `typecore::mark_constructor` with
  that usage. The exception paths pass `Public`, and
  `transl_type_extension` passes the extension's private flag. Fixtures:
  super_errors `local_exception_rebind_marks_use`,
  `local_exception_rebind_marks_use_item` and
  `local_exception_rebind_marks_use_private_extension`. All 21 programs
  above still agree, and every existing super_errors fixture keeps its
  output.

| # | Program | OCaml warnings | Trunk | Previous head | After |
| --- | --- | --- | --- | --- | --- |
| 22 | local `L = E`, local `M = L`, `\| L(n)` | 38 `4:3-17` "unused exception M" | DIFFER | DIFFER (also `3:3-17` "exception L is never used to build values") | agree |
| 23 | item `L = E`, item `M = L` under a signature, `\| L(n)`, `\| M(_)` | 38 `6:3-17` "exception M is never used to build values" | DIFFER (also L, `5:3-17`) | DIFFER (also L, `5:3-17`) | agree |
| 24 | local `L = E`, `M = L`, none used | 38 `4:3-17` "unused exception M" | DIFFER | DIFFER (also `3:3-17` "unused exception L") | agree |
| 25 | local `K(int)` used only by `L = K`, `\| L(n)` | 38 `3:3-17` "exception L is never used to build values" | DIFFER | DIFFER (also `2:3-18` "unused exception K") | agree |
| 26 | `type t += private B = A`, `\| B(n)`, under a signature | 38 `6:13-18` "extension constructor A is never used to build values." and `7:21-25` B | DIFFER ("unused extension constructor A") | DIFFER (same) | agree |
| 27 | `type t += B = A`, `\| B(n)`, under a signature | 38 `7:13-17` for B only | DIFFER (also `6:13-18` "unused extension constructor A") | DIFFER (same) | agree |
| 28 | item `K(int)` used only by item `L = K`, under a signature | 38 `5:3-17` for L only | DIFFER (also `4:3-18` "unused exception K") | DIFFER (same) | agree |

### C1 - constructors and labels through an alias of a module that holds an alias

The witness: a constructor read through an alias (`O`) of a module that
holds an alias (`A = R`).

```rescript
module Outer = {
  module R = {
    type t = A | B
    type r = {f: int}
    exception E(int)
    let x = 1
  }
  module A = R
}
module O = Outer
let v = O.A.A
```

OCaml accepts it; Rust rejected it: "The variant constructor O.A.A can't be
found." The same for `O.A.E(1)`, `| O.A.A =>` and `{O.A.f: 1}`, while
`Outer.A.A`, `let v: O.A.t = Outer.R.A`, `O.A.x`, `module P = O.A` then
`P.A` and `open O` then `A.A` were accepted. OCaml looks up a dotted
constructor or label (`Env.lookup_all_constructors`,
`Env.lookup_all_labels`, `compiler/ml/env.ml:1057-1066`, through
`lookup_all_simple`, env.ml:1028-1045) in the `comp_constrs` and
`comp_labels` tables (env.ml:389-390, filled at env.ml:1544-1554) of the
module descriptor that `lookup_module_descr` (env.ml:952-972) returns for
the prefix, the same descriptor a dotted value reads (`lookup`,
env.ml:1017-1026). The Rust lookup
(`lookup_constructor_in_module_with_ambiguity`,
`compiler-rust/src/types/typecore.rs:23271`) takes the same descriptor
road as values (`with_resolved_module_components_for_lid_inner`,
typecore.rs:26692); a trace showed that road failing for `O.A` for
values too, which recovered through a second lookup by access path
(`resolve_module_access_path_for_lid`, typecore.rs:22657) that
constructors and labels do not have.

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from the thin-LTO release build, the runtime built by
`build-reference` with the OCaml `bsc`); each program is `Main.res`
compiled by both with `-w +A -bs-jsx 4 -color never -I . -I
packages/@rescript/runtime/lib/rescript`, and stdout (the JavaScript),
stderr and the exit status compared byte for byte. The programs of a
second unit compile `Main.res` against a package holding `Lib.res`, built
by `rescript build-reference --bsc <OCaml bsc>`; the projects of two units
are built by `rescript build-reference` and `rescript build` and their
JavaScript compared byte for byte.

#### Fixed

- `7762c22d7`: OCaml builds a child module's component table from the raw
  declaration `md.md_type` and the parent's substitution `sub`, in the
  environment the walk has extended with the raw declarations of the
  earlier items (`components_of_module_maker`, env.ml:1556-1568); the
  table's `scrape_alias` (env.ml:1504, 1350-1362) resolves `module A = R`
  to the sibling `R` there, and `prefix_idents` (env.ml:1369-1410, 1519)
  prefixes the result. For a parent read through an alias, the Rust
  `build_local_module_components` (`compiler-rust/src/types/env_lazy.rs:2123`,
  the child item at 2395 before the fix) gave the child and the evolving
  environment the prefixed item, `Mty_alias O.R`; `O` is not bound in that
  environment, so `resolve_module_type` failed, the child had no
  components and the lookup found nothing. An alias child now keeps its
  raw declaration (`env_lazy.rs:2432`); its components substitute the
  parent's paths themselves, as a child of a parent that is no alias
  already did. Fixtures: `tests/tests/src/alias_chain_constructor_local`,
  `alias_chain_constructor_functor`, `alias_chain_constructor_direct`
  (agreed before), super_errors `alias_chain_constructor_wrong_type`,
  `alias_chain_constructor_misspelled`, `alias_chain_constructor_label_missing`
  and `alias_chain_constructor_direct_missing` (the last three agreed
  before).
- `7ba334589`: through an alias of another unit (`module O = Lib`, `Lib`
  holding `module A = R`), the constructors of `O.A` had the result type
  `O.A.A.t` (OCaml: `O.A.t`), printed in error messages, and a match on
  one stopped with `Fatal error: Parmatch.get_variant_constructors`, before
  the fix above too. The components of an in-process unit read through an
  alias share the unit's signature, where the alias names its sibling by
  identifier; OCaml's `prefix_idents` puts it at `O.R` before the alias is
  scraped. `QualifiedModuleComponents::new_with_child_components_arc_and_value_source_prefix_inner`
  (`env_lazy.rs:1054`, the registration at 1143 before the fix) registered
  the bare `R` as the alias source of `O.A`. The unit's signature keeps the
  stamps of its `.cmi`, `R` had the stamp of the compiling unit's `O`, and
  re-rooting the constructors from `R` to `O.A`
  (`reroot_constructor_descriptions`) rewrote `O.A.t` into `O.A.A.t`. The
  source is now the target with its head put at the access path
  (`env_lazy.rs:1155`, one name probe of the signature index per alias
  of a module that is not a unit).
  Fixtures: `tests/tests/src/alias_chain_constructor_unit` with
  `alias_chain_constructor_unit_lib`, `alias_chain_constructor_unit_direct`
  (agreed before), super_errors_multi `alias_chain_constructor_unit`.

Programs run through both compilers, before (trunk `acf84ba17`), after
`7762c22d7` and after `7ba334589`. Exit status of OCaml; DIFFER is a
difference in the exit status, the diagnostics or the JavaScript:

| Program | OCaml | Before | After `7762c22d7` | After `7ba334589` |
| --- | --- | --- | --- | --- |
| the witness, `O.A.A` | 0 | DIFFER (Rust 2) | agree | agree |
| exception `O.A.E(1)` | 0 | DIFFER (Rust 2) | agree | agree |
| pattern `\| O.A.A => 1 \| O.A.B => 2` | 0 | DIFFER (Rust 2) | agree | agree |
| record `{O.A.f: 1}` | 0 | DIFFER (Rust 2) | agree | agree |
| field access `r.O.A.f` | 0 | DIFFER (Rust 2) | agree | agree |
| record pattern `{O.A.f: f}` | 0 | DIFFER (Rust 2) | agree | agree |
| extensible type `O.A.C(1)`, `\| O.A.C(n)` | 0 | DIFFER (Rust 2) | agree | agree |
| inline record `O.A.I({w: 1})`, `\| O.A.I({w})` | 0 | DIFFER (Rust 2) | agree | agree |
| `try ... catch { \| O.A.E(n) => n }` | 0 | DIFFER (Rust 2) | agree | agree |
| chain of three, `module P = O`, `P.A.A`, `P.A.E(1)`, `{P.A.f: 1}` | 0 | DIFFER (Rust 2) | agree | agree |
| inner chain `B = A`, `A = R`: `O.B.A`, `O.B.E(1)`, `\| O.B.B` | 0 | DIFFER (Rust 2) | agree | agree |
| inner alias of a module outside `Outer` | 0 | agree | agree | agree |
| inner alias of a sibling's submodule, `A = R.S` | 0 | DIFFER (Rust 2) | agree | agree |
| alias of a functor parameter holding an alias, `module Y = X`, `Y.A.A` | 0 | agree | agree | agree |
| alias of a functor application holding an alias, `N.A.K` | 0 | DIFFER (Rust 2) | agree | agree |
| through `include`: `module I = {include Inner}`, `module J = I`, `J.A.Q` | 0 | DIFFER (Rust 2) | agree | agree |
| `Outer.A.A`, `Outer.A.E(1)`, `{Outer.A.f: 1}` (no outer alias) | 0 | agree | agree | agree |
| type `let v: O.A.t = Outer.R.A` | 0 | agree | agree | agree |
| value `O.A.x` | 0 | agree | agree | agree |
| `module P = O.A` then `P.A`, `{P.f: 1}` | 0 | agree | agree | agree |
| `open O` then `A.A`, `A.E(1)` | 0 | agree | agree | agree |
| missing `O.A.Cc` (rejected) | 2 | agree | agree | agree |
| misspelled `O.A.Bb` (rejected) | 2 | agree | agree | agree |
| misspelled `O.A.Bb` with expected type `Outer.R.t` (rejected) | 2 | agree | agree | agree |
| missing label `{O.A.g: 1}` (rejected) | 2 | agree | agree | agree |
| misspelled label `{O.A.ff: 1}`, in an expression and a pattern (rejected) | 2 | agree | agree | agree |
| misspelled field `r.O.A.ff` (rejected) | 2 | agree | agree | agree |
| missing pattern `\| O.A.D =>` (rejected) | 2 | agree | agree | agree |
| missing exception `O.A.Ex(1)` (rejected) | 2 | agree | agree | agree |
| `let v: int = O.A.A` (rejected: "This has type: O.A.t") | 2 | DIFFER (unbound) | agree | agree |
| wrong field `O.A.I({z: 1})` of an inline record (rejected) | 2 | DIFFER (unbound) | agree | agree |
| other unit, `module O = Lib`, `let v: int = O.A.A` (rejected) | 2 | DIFFER (`O.A.A.t`) | DIFFER (`O.A.A.t`) | agree |
| other unit, `\| O.A.B => 1` | 0 | DIFFER (Fatal error) | DIFFER (Fatal error) | agree |
| other unit, constructors, exception, extension, record, field, pattern | 0 | DIFFER | DIFFER | agree |
| other unit, `module P = O`, `P.Outer.A.A`, `\| P.Outer.A.B` | 0 | DIFFER (Rust 2) | agree | agree |
| other unit, misspelled `O.A.Bb` (rejected) | 2 | agree | agree | agree |
| other unit, missing label `{O.A.g: 1}` (rejected) | 2 | agree | agree | agree |
| two-unit project (`Lib.res`, `Main.res`), JavaScript | 0 | DIFFER (Rust 1) | DIFFER | agree |

#### Open

- Not of this place, found while reducing a fixture: an extension of an
  extensible type two modules deep and a functor application in the same
  unit, with no alias at all, is rejected by Rust ("The implementation
  Main.res does not match the interface (inferred signature): In module
  Outer.R: Actual declaration type \"Outer.R.ext\" += C(int) Expected
  declaration type ext += C(int)"); OCaml accepts it. Trunk `acf84ba17`
  does the same:

  ```rescript
  module Outer = {
    module R = {
      type ext = ..
      type ext += C(int)
    }
  }
  module G = (X: {}) => {
    module S = {}
  }
  module M = G({})
  ```

  One module deep (`module R = {...}` at the top) agrees. It was not traced
  here; it lies in the typing of extension declarations or the check of
  the unit against its inferred signature.
  Fixed under X1 below.
- The world view of a unit (`describe_tables`,
  `compiler-rust/src/types/module_view.rs:819`) registers the same bare
  sibling target (`Lib.A` from `R`) as the alias source of its alias
  children. There its access path is the unit itself, and the
  descriptions it re-roots name only that unit's paths, so no program was
  found on which it shows; it was left as it is.
- The second lookup of qualified values by access path
  (`resolve_module_access_path_for_lid`, typecore.rs:22657) is still there.
  The witnesses of this place no longer reach it; whether any program
  still needs it was not measured, and it was not removed.

### X1 - a constructor of an extensible type two modules deep, with a functor application in the unit

The witness (the one found under C1):

```rescript
module Outer = {
  module R = {
    type ext = ..
    type ext += C(int)
  }
}
module G = (X: {}) => {
  module S = {}
}
module M = G({})
```

OCaml accepts it; Rust rejected it: "The implementation Main.res does not
match the interface (inferred signature): In module Outer.R: Actual
declaration `type \"Outer.R.ext" += C(int)`, Expected declaration
`type ext += C(int)`". The same with `let x = 1` as the functor body and
`let c = Outer.R.C(M.x)` after it.

Two things met. (a) A unit without an interface whose inferred signature
holds a functor (the declaration `G`, with or without an application: the
program without `module M = G({})` differed as well) leaves the shortcut
of `inferred_signature_coercion` (`compiler-rust/src/types/includemod.rs`,
`includes_itself_plainly` answers `false` for `MtyFunctor`) and is checked
against its own signature in full, as OCaml always does
(`compiler/ml/typemod.ml:1812-1815`). That is as intended: the shortcut is
taken only for signatures whose check cannot fail, and the full check is
what OCaml runs. (b) The full check failed where OCaml's passes, for two
causes, each fixed below.

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from the thin-LTO release build, the runtime built by
`build-reference` with the OCaml `bsc`); each program is `Main.res`, with
`Main.resi` where the table says so (compiled first by the OCaml `bsc`,
then `Main.res` with `-bs-read-cmi`), compiled by both with `-w +A -bs-jsx
4 -color never -I . -I packages/@rescript/runtime/lib/rescript`, and
stdout (the JavaScript), stderr and the exit status compared byte for
byte.

#### Fixed

- `71003f88f`: OCaml's `Includecore.extension_constructors` compares the
  extended types as types, `Ctype.equal env true (ty1 :: ext1.ext_type_params)
  (ty2 :: ext2.ext_type_params)` (`compiler/ml/includecore.ml:717-728`),
  in the environment `signatures` extends with the implementation's items
  (`compiler/ml/includemod.ml:388-390`), so a path that expands to the
  other one matches it. The Rust `extension_constructors`
  (`compiler-rust/src/types/includemod.rs:4965` before the fix) required
  `Path::same` of the two paths. In the witness the implementation's
  constructor extends `Outer.R.ext` (see the next cause) and the expected
  one `ext`, whose strengthened declaration `type ext = Outer.R.ext` is in
  that environment; `type t = A.ext = ..` with `type A.ext += C(int)`
  against `type t += C(int)` was rejected for the same reason, one module
  deep. The Rust comparison now builds the two constructor types and calls
  `ctype::equal` as OCaml does (`includemod.rs:4965`). Fixtures:
  `tests/tests/src/nested_extension_signature_functor` (the witness),
  `nested_extension_signature_manifest` (the abbreviation, both
  directions), `nested_extension_signature_one_deep` (agreed before),
  super_errors `nested_extension_signature_argument` (a submodule with an
  explicit signature whose argument type differs, agreed before) and
  `nested_extension_signature_manifest_argument` (the abbreviation with a
  differing argument type, agreed before).
- `30651d2f6`: OCaml expands a module alias in an inclusion check with
  `expand_module_alias`, `(Env.find_module path env).md_type`
  (`compiler/ml/includemod.ml:99-101`, used at 228-234): for `Outer.R` that
  is the declaration `Outer`'s components hold, under `Outer`'s
  substitution only (`compiler/ml/env.ml:1555-1557`), so `R`'s own items
  keep their identifiers; `Mtype.strengthen` then adds `type ext =
  Outer.R.ext`. The Rust expansion (`expand_module_type_in_env` in
  `modtypes_inner`, `includemod.rs:1273`) went for a dotted path through
  `ctype::resolve_module_type_through_env`, which reads the components
  view of `Outer.R` itself, whose items are prefixed with it: the
  constructor extended `Outer.R.ext`, a value had type `Outer.R.t`. The
  unit's own check strengthens `Outer` into a structure whose `R` is the
  alias `Outer.R`, so every submodule two or more levels deep went this
  way; against an interface or a signature the diagnostics printed
  `type \"Outer.R.ext" += C(int)` and `let x: Outer.R.t` where OCaml
  prints `type ext += C(int)` and `let x: t`. A dotted module path now
  reads the parent's declaration (`expand_local`, which calls
  `lookup_module_in_resolved_path`); module type paths keep the
  components lookup. Fixtures: super_errors_multi
  `nested_extension_signature_interface` (the interface whose argument
  type differs), `tests/tests/src/nested_extension_signature_interface`
  (an interface that matches), super_errors
  `nested_extension_signature_value_path` (a value two levels deep against
  a signature) and `nested_extension_signature_value_one_deep` (one level,
  agreed before).

Programs run through both compilers, before (trunk `299927cd2`), after
`71003f88f` and after `30651d2f6`. Exit status of OCaml; DIFFER is a
difference in the exit status, the diagnostics or the JavaScript:

| Program | OCaml | Before | After `71003f88f` | After `30651d2f6` |
| --- | --- | --- | --- | --- |
| the witness, functor body `module S = {}` | 0 | DIFFER (Rust 2) | agree | agree |
| the witness, `let x = 1`, then `Outer.R.C(M.x)` | 0 | DIFFER (Rust 2) | agree | agree |
| one module deep, `R.C(1)` | 0 | agree | agree | agree |
| three modules deep, `A.Outer.R.C(M.x)` | 0 | DIFFER (Rust 2) | agree | agree |
| constructor without argument `C` | 0 | DIFFER (Rust 2) | agree | agree |
| tuple `C(int, string)` | 0 | DIFFER (Rust 2) | agree | agree |
| inline record `C({a: int, b: string})`, built and matched | 0 | DIFFER (Rust 2) | agree | agree |
| GADT-style `C: ext<int>`, `D('a): ext<'a>` | 0 | DIFFER (Rust 2) | agree | agree |
| type parameter `ext<'a> += C('a, list<'a>)` | 0 | DIFFER (Rust 2) | agree | agree |
| rebind `type ext += D = C` in `R` | 0 | DIFFER (Rust 2) | agree | agree |
| rebind one level up, `type R.ext += D = R.C` in `Outer` | 0 | DIFFER (Rust 2) | agree | agree |
| `private C(int)`, matched | 0 | DIFFER (Rust 2) | agree | agree |
| functor application before `Outer` | 0 | DIFFER (Rust 2) | agree | agree |
| functor declared, never applied | 0 | DIFFER (Rust 2) | agree | agree |
| functor taking `Outer.R` as its argument, `G(Outer.R)` | 0 | DIFFER (Rust 2) | agree | agree |
| no functor at all | 0 | agree | agree | agree |
| `exception C(int)` two deep, with the application | 0 | agree | agree | agree |
| `Outer` with an explicit signature listing the extension | 0 | DIFFER (Rust 2) | agree | agree |
| the same inside `module Top` | 0 | DIFFER (Rust 2) | agree | agree |
| `type t = A.ext = ..` with `type A.ext += C(int)` against `type t += C(int)` | 0 | DIFFER (Rust 2) | agree | agree |
| `type t = A.ext = ..` with `type t += D(int)` against `type A.ext += D(int)` | 0 | DIFFER (Rust 2) | agree | agree |
| interface that matches (`Main.resi`) | 0 | DIFFER (Rust 2) | agree | agree |
| interface, argument type differs (rejected) | 2 | DIFFER (`Outer.R.ext`) | DIFFER (`Outer.R.ext`) | agree |
| interface, arity differs (rejected) | 2 | DIFFER (`Outer.R.ext`) | DIFFER (`Outer.R.ext`) | agree |
| interface, a constructor missing in the implementation (rejected) | 2 | agree | agree | agree |
| interface, private against public (rejected) | 2 | DIFFER (`Outer.R.ext`) | DIFFER (`Outer.R.ext`) | agree |
| submodule signature, argument type differs (rejected) | 2 | agree | agree | agree |
| submodule signature, private against public (rejected) | 2 | agree | agree | agree |
| abbreviation, argument type differs (rejected) | 2 | agree | agree | agree |
| `module S: {let x: int} = Outer.R` (rejected) | 2 | DIFFER (`Outer.R.t`) | DIFFER (`Outer.R.t`) | agree |
| the same one level deep, `= R` (rejected) | 2 | agree | agree | agree |
| interface, a value three levels deep differs (rejected) | 2 | DIFFER (`A.Outer.R.t`) | DIFFER | agree |
| interface, a value two levels deep differs (rejected) | 2 | DIFFER (`Outer.R.t`) | DIFFER | agree |
| `= Outer.R.S` against a signature, value type differs (rejected) | 2 | DIFFER (`Outer.R.S.u`) | DIFFER | agree |
| `= Outer.R.S` against a signature that matches, and a constrained module | 0 | agree | agree | agree |
| interface, `module S = Outer.R` against a signature (rejected) | 2 | DIFFER | DIFFER | agree |
| `open Outer`, then `module S: {let x: int} = R` (rejected) | 2 | DIFFER (`Outer.R.t`) | DIFFER | agree |
| `JSON.Encode`, `Int.Constants`, `Stdlib.Int.Constants` against signatures | 0 | agree | agree | agree |
| `JSON.Encode` against a signature, argument type differs (rejected) | 2 | agree | agree | agree |
| `open Stdlib`, `Int.Constants` against a signature (rejected) | 2 | agree | agree | agree |

#### Open

Nothing of this place.
