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

### H1 - spelling hints through a module path that ends in an alias

The witness: a misspelled constructor read through a module path of two
components whose last module is an alias.

```rescript
module Outer = {
  module R = {
    type t = Apple | Banana
  }
  module A = R
}
let v = Outer.A.Aple
```

Both compilers reject it with "The variant constructor Outer.A.Aple can't be
found."; OCaml ends the report with "Hint: Did you mean Apple?", Rust printed
no hint. The same for values, exception constructors, record labels, types,
modules and module types, through `Outer.A`, through an alias `O.A` of
`Outer`, and through another unit. `R.Aple` and `A.Aple` with `A = R` at the
top got the hint in both. OCaml's hint is `Typetexp.spellcheck` /
`super_spellcheck` (`compiler/ml/typetexp.ml:779-797`, called for values at
895, modules at 938, constructors at 953, labels at 997, module types at
1000, types at 817) over a fold of the names of that kind: for `Ldot (r, s)`
the folds `find_all`, `find_all_simple_list` and `fold_modules`
(`compiler/ml/env.ml:1985-2056`, `fold_values` ... `fold_modtypes` at
2045-2056) read the component table of the descriptor
`lookup_module_descr r env` returns (env.ml:952-972), the descriptor the
failed lookup itself read, which follows the aliases of the path; the
candidates are matched against the last component `s`.

Commands as in "Scope, calibration and reproducibility"; each program is
`Main.res` compiled by both with `-w +A -bs-jsx 4 -color never -I . -I
packages/@rescript/runtime/lib/rescript` (and `-I` the OCaml-built package
holding `Lib.res` for the paths through another unit), and stderr and the
exit status compared byte for byte.

#### Fixed

- `116817ed9`: the report of an unbound module type
  (`format_unbound_modtype_report`, `compiler-rust/src/driver.rs:4478`)
  spellchecked the whole dotted name (`R.Sigg`) against the candidates,
  where `Typetexp.spellcheck` matches the last component
  (typetexp.ml:790-797); a qualified module type never got a hint, alias or
  not. It now passes the last component (driver.rs:4489), as the report of
  an unbound module does. Fixtures: super_errors
  `alias_path_hint_modtype_qualified`, `alias_path_hint_modtype_unqualified`
  (agreed before).
- `db1a96289`: the candidates for a qualified name
  (`unbound_name_alternatives`, `compiler-rust/src/types/typecore.rs:18141`,
  for values, constructors, labels, types and modules) resolved the prefix
  with `Env::resolve_module_lid_raw`, and those for a module type
  (`unbound_modtype_alternatives`, `typemod.rs:7665`) with
  `lookup_module_type_by_lid`: two roads beside the descriptor lookup the
  failed lookup took, and neither reached the signature of `Outer.A`. Both
  now read the table `with_resolved_module_components_for_lid` gives for the
  prefix, the road of the lookups (the module type candidates are collected
  by `unbound_name_alternatives` too). It runs only after a lookup has
  failed. Fixtures: super_errors `alias_path_hint_constructor`, `_value`,
  `_exception`, `_label`, `_label_pattern`, `_field`, `_type`, `_module`,
  `_modtype_alias`, `_tie`, `_too_far`, `_alias_outside` and `_one_alias`
  (the last three agreed before), super_errors_multi `alias_path_hint_unit`.

Programs run through both compilers, before (trunk `299927cd2`) / after
`db1a96289`, the whole diagnostic and the exit status compared byte for
byte (OCaml rejects every one). Columns are the kinds: a value `aple`,
constructor `Aple`, exception `Meln(1)`, label `{P.aple: 1, banana: 2}`,
field read `r.P.aple`, record pattern `{P.aple: a}`, type `P.frut`, module
`P.Subb.x`, module type `P.Sigg`, `P.Gear` (two candidates at distance 1:
OCaml prints "Bear or Pear"), and three names OCaml gives no hint
(`Zzzzzzzz`, too far; `Ap`, two letters; `X`, one letter). Rows are the
paths: `Outer.A`; `O.A` with `module O = Outer`; `Q.A` with `Q = O`, `O =
Outer` (a chain of three); `O.A` with `A` an alias of a module `Top` outside
`Outer`; `I.A` with `module I = {include Outer}`; `X.A` inside a functor
whose parameter holds `module A = R`; `Lib.A` and `O.A` with `module O = Lib`
in a second unit.

| Path | value | constructor | exception | label | field | labelpat | type | module | modtype | tie | nohint_far | nohint_short | nohint_one |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Outer.A` | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `O.A` | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `Q.A` (three) | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `O.A`, A = Top | agree / agree | agree / agree | agree / agree | agree / agree | agree / agree | agree / agree | agree / agree | agree / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree | agree / agree |
| `I.A` (include) | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `X.A` (functor) | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `Lib.A` | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |
| `O.A`, O = Lib | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | DIFFER / agree | agree / agree | agree / agree | agree / agree |

Controls, agree before and after: `R.Aple` with `R` at the top, `A.Aple`
with `module A = R` at the top, `Outer.R.Aple` with no alias, and the
unqualified module type `Sigg`.

The path through an alias of a module outside `Outer` agreed before except
for the module type: `resolve_module_lid_raw` reached `Top`'s signature, but
the module type report spellchecked `O.A.Sigg` whole.

#### Open

Nothing of this place. The value lookup's own fallback through
`resolve_module_lid_raw` (`typecore.rs:9923`, after the descriptor road and
the access-path road fail) is a lookup, not a candidate fold, and was left
as it is.

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

### R1 - a rebind marks the type path and the modules on its path as used

The place is M6 of "Fourth round: modules, aliases and usage marks" below;
its witnesses are M6-2, M6-3 and M6-5 to M6-9. The smallest:

```rescript
module M: {} = {module N = {exception E}; exception A = N.E}
```

OCaml prints one warning, 38 "unused exception A" at `1:43-59`; Rust also
printed warning 60 "unused module N." at `1:24-40`. Through an `open`
(`module M: {exception A} = {module N = {exception E}; open N; exception A =
E}`) OCaml prints nothing and Rust printed warning 33 "unused open N." at
`1:54-59`.

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from thin-LTO release builds of `8590ce4c03` (before) and
of the fix (after), the runtime built by `build-reference` with the OCaml
`bsc`); each program is `Main.res`, with `Main.resi` where the table says so
(compiled first, then `Main.res` with `-bs-read-cmi` against the interface
the OCaml `bsc` wrote), compiled by both with `-w +A -bs-jsx 4 -color never
-I . -I packages/@rescript/runtime/lib/rescript`, and stdout (the
JavaScript), stderr and the exit status compared byte for byte.

#### Fixed

- `f470283dd`: OCaml's `Pext_rebind` arm finds the constructor with
  `Typetexp.find_constructor` (`compiler/ml/typedecl.ml:1695`,
  `compiler/ml/typetexp.ml:109-110`), that is `Env.lookup_constructor`
  (`compiler/ml/env.ml:1146-1152`): for `N.P.E` it goes through
  `lookup_module_descr` (`env.ml:968-972`), which marks every module on the
  prefix as used and reports a deprecated one; for `E` it calls the `use ()`
  callback of the innermost candidate, which marks the `open` the name came
  from; both mark the type path of the constructor's result
  (`mark_type_path`, `env.ml:1135-1139`). The Rust `lookup_rebind_constructor`
  (`compiler-rust/src/types/typemod.rs:555` before the fix) looked the
  constructor up with `Env::find_constructor` or
  `typecore::lookup_constructor_in_module`, neither of which marks anything,
  and marked only the constructor. It now calls
  `typecore::find_constructor` (`compiler-rust/src/types/typecore.rs:24151`),
  the Rust form of `Typetexp.find_constructor`, made of the helpers the
  constructor lookups of expressions and patterns use: `mark_open_lid_use`
  for the prefix of a qualified name, `use_constructor_candidate` for the
  innermost candidate of an unqualified one, and `mark_type_path_of`. The
  exception item, the local exception (`type_letexception` goes through the
  same `transl_exception`) and `type t += A = N.E` all reach it. Fixtures:
  super_errors `rebind_usage_marks_module_path`, `_open`,
  `_alias_functor`, `_deprecated`, `_type_path`, `_local_exception`, and
  super_errors_multi `rebind_usage_marks_interface` (M6-5). Each fails on
  the base and agrees after.

Programs through both compilers. OCaml status 0 is accepted, 2 rejected;
the warnings are OCaml's (number and location); DIFFER is a difference in
the JavaScript, the diagnostics or the status. In the "Before" column, the
extra Rust warnings are given.

| # | Program | OCaml | Before (Rust) | After (Rust) |
| --- | --- | --- | --- | --- |
| 1 | M6-1, local `exception A = M.E` used | 0 | agree | agree |
| 2 | M6-2, `N.E` hidden, `A` unused | 0, 38 `1:48-64` | DIFFER (60 N) | agree |
| 3 | M6-3, through `open N`, hidden | 0, 38 `1:56-70` | DIFFER (33 open N) | agree |
| 4 | M6-4, `type N.t += A = N.E` hidden | 0, 38 `1:73-79` | agree | agree |
| 5 | M6-5, `exception A = M.E` with `Main.resi` `exception A(int)` | 0 | DIFFER (60 M) | agree |
| 6 | M6-6, two modules `N.P.E`, hidden | 0, 38 `1:61-79` | DIFFER (60 P, 60 N) | agree |
| 7 | M6-7, argument-free, hidden | 0, 38 `1:43-59` | DIFFER (60 N) | agree |
| 8 | M6-8, `A` exported | 0 | DIFFER (60 N) | agree |
| 9 | M6-9, through `open N`, `A` exported | 0 | DIFFER (33 open N) | agree |
| 10 | exception through two modules `P.Q.E`, exported | 0 | DIFFER (60 Q, 60 P) | agree |
| 11 | extension constructor through one module, exported | 0 | DIFFER (60 N) | agree |
| 12 | extension constructor through two modules `P.Q.E` | 0 | DIFFER (60 Q, 60 P) | agree |
| 13 | extension constructor through `open N` | 0 | DIFFER (33 open N) | agree |
| 14 | the task's (3): `type t = ..`, `module N = {type t += E}`, `type t += A = N.E`, exported | 0 | DIFFER (60 N) | agree |
| 15 | exception through `open! N` | 0 | agree | agree |
| 16 | exception through an alias `module L = N; exception A = L.E` (L and N used) | 0 | DIFFER (60 L) | agree |
| 17 | extension constructor through an alias `L.E` | 0 | DIFFER (60 L) | agree |
| 18 | exception through a functor application result `module R = F(X); exception A = R.E` | 0 | DIFFER (60 R) | agree |
| 19 | extension constructor of a functor application result | 0 | DIFFER (60 R) | agree |
| 20 | exception through `module I = {include N}; exception A = I.E` | 0 | DIFFER (60 I) | agree |
| 21 | `include N; exception A = E` (unqualified, after an include) | 0 | DIFFER (2, "The variant constructor E can't be found.") | DIFFER (same); see Open |
| 22 | source module not hidden, `module N = {exception E}; exception A = N.E` | 0 | agree | agree |
| 23 | rebound `A` used, `throw(A)` in an unused `f`, hidden | 0, 32 `1:66` | DIFFER (60 N) | agree |
| 24 | rebound extension constructor used in an exported value | 0 | DIFFER (60 N) | agree |
| 25 | open shadowed by a later local `exception E` | 0, 38 `1:54-64` | DIFFER (33 open N) | agree |
| 26 | two opens of modules that both have `E`: the later one is used | 0, 38 `1:40-50`, 33 `1:80-85` (open N) | DIFFER (33 for O as well) | agree |
| 27 | two modules through `Main.resi` `exception A` | 0 | DIFFER (60 Q, 60 P) | agree |
| 28 | rebind through a `@deprecated` module | 0, 3 `3:15-17` "deprecated: module N" | DIFFER (no warning 3) | agree |
| 29 | extensible type exported abstractly, `A` unused | 0, 38 `1:77-83` | DIFFER (60 N) | agree |
| 30 | rebind of a functor parameter's constructor `X.E` | 0 | agree | agree |
| 31 | local `exception A = N.E` returned from an exported function | 0 | DIFFER (60 N) | agree |
| 32 | local `exception A = E` through `open N` | 0 | DIFFER (33 open N) | agree |
| 33 | local `exception A = P.Q.E` | 0 | DIFFER (60 Q, 60 P) | agree |
| 34 | local `exception A = N.E`, `A` unused | 0, 38 `1:76-92` | DIFFER (60 N) | agree |
| 35 | type-path mark: `module M: {} = {module N = {type t = ..; type t += E}; type N.t += A = N.E}` | 0, 38 `1:68-74` (no unused type) | agree | agree |
| 36 | type-path mark, the type private to an inner signature, M hidden | 0, 38 `1:96-102` | agree | agree |
| 37 | the same, `type t = N.t = ..` exported | 0 | agree | agree |
| 38 | `type t += private A = N.E` of a private `N.E`, exported private | 0, 38 `1:107` | DIFFER (60 N) | agree |
| 39 | rebind of a private extension constructor into a public one, inside a module | 2, `1:117-119` "The constructor N.E is private" | agree | agree |
| 40 | the same at top level | 2, `3:15-17` "The constructor N.E is private" | agree | agree |
| 41 | near-miss `N.Ee` for `N.E` | 2, `2:15-18` "The variant constructor N.Ee can't be found." (no hint) | agree | agree |
| 42 | near-miss `Ex` for `Exx` | 2, `2:15-16` "The variant constructor Ex can't be found." (no hint) | agree | agree |
| 43 | unbound module `Nn.E` | 2, `2:15-18` | agree | agree |
| 44 | constructor `Foo` of an ordinary variant as an exception | 2, `2:15-17` "The constructor Foo has type v but was expected to be of type exn" | agree | agree |
| 45 | constructor `Foo` of an ordinary variant as an extension constructor | 2, `3:15-17` | agree | agree |
| 46 | `type s += A = E` with `E` of `t<_>` | 2, `4:15` "The constructor E has type t<'a> but was expected to be of type s" | agree | agree |
| 47 | `type t<_> += E` for `type t<_, _> = ..` | 2, `2:1-14` | agree | agree |
| 48 | `type u<_, _> += A = E` with `E` of `t<_>` | 2, `4:21` | agree | agree |

#### Open

- Row 21 is a different cause, outside this place: after `include N` an
  unqualified extension constructor of `N` is not found at all, in an
  expression too (`module M: {let v: exn} = {module N = {exception E};
  include N; let v = E}`, and `type t += E` included at top level). OCaml
  accepts each; Rust rejects with "The variant constructor E can't be
  found." at the use. The constructor table of the environment after an
  `include` lacks the included extension constructors, which is the
  structure's `include` typing, not the rebind lookup; it is left for a task
  of its own.
  Fixed under I1 below.
- No program here showed M7 (an extra "unused exception" for a constructor
  matched by an inner signature).

### I1 - an extension constructor brought in by include

Found as row 21 of R1 above. The witnesses:

```rescript
module N = {exception E}
include N
let v = E
```

with `module N = {type t = ..; type t += E}` in place of the exception, and
`module M: {let v: exn} = {module N = {exception E}; include N; let v = E}`.
OCaml accepts all three with no warning; Rust rejected each at the use with
"The variant constructor E can't be found."

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from thin-LTO release builds of `a484dec41d` (before)
and of the fix (after), the runtime built by `build-reference` with the
OCaml `bsc`); each single-unit program is `Main.res`, with `Main.resi`
where the table says so, compiled by both with `-w +A -bs-jsx 4 -color
never -I . -I packages/@rescript/runtime/lib/rescript`, and stdout (the
JavaScript), stderr and the exit status compared byte for byte. Programs
of several units are built as a project (`rescript.json` with
`"warnings": {"number": "+A"}`) by `rescript build-reference --bsc` (OCaml)
and `rescript build` (Rust), comparing `lib/rescript/.compiler.log` and
every generated `.js`.

#### Fixed

- `944264d8f`: OCaml types `include` by adding the included signature with
  `Env.add_signature` (the `Pstr_include` arm of `compiler/ml/typemod.ml`,
  and its `Psig_include` arms), whose `add_item` gives a `Sig_typext` item
  to `add_extension ~check:false` (`compiler/ml/env.ml:1840`, `1791`,
  `store_extension` at `1715`): the constructor enters the constructor
  table under its own name with the description
  `Datarepr.extension_descr (Pident id) ext`. In Rust the `Pstr_include`
  arm (`compiler-rust/src/types/typemod.rs:19613`) adds the included items
  itself and its catch-all arm dropped `SigTypext`; the signature
  `include` goes through `add_signature_items_to_env` (`typemod.rs:7997`),
  which skipped `SigTypext` too. So after an `include` the constructor
  could be read by path (`M.E`, through the module's components) but not
  by its name. Both now call `Env::add_extension`
  (`compiler-rust/src/types/env.rs:2246`), which adds the description
  `env_lazy::extension_descr` (`compiler-rust/src/types/env_lazy.rs:543`)
  builds. That is the builder the `open` road already used, split out of
  `extension_constructor_description`, which now builds its `Pdot` path and
  calls it. `add_extension` registers no unused check, as `~check:false`.
  Cost: one description and one table entry per extension constructor of
  an included signature; nothing for other items or units.
  Fixtures: super_errors `include_extension_constructor_expression`,
  `_pattern`, `_paths`, `_unused`, `_misspelt`, `_arity`, `_wrong_type`,
  and super_errors_multi `include_extension_constructor_unit` (Lib, Main
  with `include Lib`, and Third reading `Main.E`).
- `b37b435e0`: the signature of a recursive module is first approximated,
  and OCaml's `approx_sig` adds an included signature with
  `Env.add_signature` too (`compiler/ml/typemod.ml:567-574`). A
  `module type of` later in that signature types its module expression in
  this environment, so it can name the constructor (row 38). The Rust
  approximation's `Psig_include` arm (`compiler-rust/src/types/typemod.rs`,
  in `approx_signature`) added the items with
  `includemod::add_sig_item_to_env`, which skips `SigTypext`. It now adds
  an extension constructor with `Env::add_extension`. The shared
  `add_sig_item_to_env` is unchanged: it also extends the environment of
  the inclusion check and of module type extraction, where a description
  per extension constructor would cost units that have no `include`.
  Fixture: super_errors `include_extension_constructor_recursive`.

Programs through both compilers. OCaml status 0 is accepted, 2 rejected,
with OCaml's warnings and errors; DIFFER is a difference in the JavaScript,
the diagnostics or the status. The JavaScript of accepted programs reads the
included constructor through the unit's own binding: `let E =
Primitive_exceptions.create("Main.N.E")` once, `exports.E = E`, and uses
`RE_EXN_ID: E`. That is the same in both after the fix.

| # | Program | OCaml | Before (Rust) | After (Rust) |
| --- | --- | --- | --- | --- |
| 1 | witness (1), `exception E`, `include N`, `let v = E` | 0 | DIFFER (2, "can't be found") | agree |
| 2 | witness (2), `type t += E` | 0 | DIFFER (2) | agree |
| 3 | witness (3), inside `M: {let v: exn}` | 0 | DIFFER (2) | agree |
| 4 | `exception E(int, string)`, `E(1, "a")` | 0 | DIFFER (2) | agree |
| 5 | `exception E({a: int, b: string})`, built and matched `E({a})` | 0, 9 `5:5-7` | DIFFER (2) | agree |
| 6 | `type t += E(int)`, `let v: t = E(1)` | 0 | DIFFER (2) | agree |
| 7 | `type t += E({a: int})`, built and matched | 0 | DIFFER (2) | agree |
| 8 | `type t<'a> += E('a)`, `E(1): t<int>` and `E("x"): t<string>` | 0 | DIFFER (2) | agree |
| 9 | pattern, `switch x {\| E => 1 \| _ => 0}` | 0 | DIFFER (2) | agree |
| 10 | pattern, `try g() catch {\| E(n) => n}` | 0 | DIFFER (2) | agree |
| 11 | rebind, `exception A = E` after the include | 0 | DIFFER (2) | agree |
| 12 | `include (N: {exception E})` | 0 | DIFFER (2) | agree |
| 13 | include of a functor application, `include F({})`, `E(1)` | 0 | DIFFER (2) | agree |
| 14 | include of a module alias `module L = N; include L` | 0 | DIFFER (2) | agree |
| 15 | `module M = {include N}`, `M.E` built and matched from outside | 0 | agree | agree |
| 16 | signature include, `module type T = {include S}`, `X: T`, `X.E` | 0 | agree | agree |
| 17 | the same with `let v: exn` in `T` and `X.E` read outside | 0 | agree | agree |
| 18 | `Main.resi` `module type S = {exception E}; include S; let v: exn` | 0 | agree | agree |
| 19 | two includes bringing `E` into one structure | 2, `4:1-9` "Multiple definition of the extension constructor name E" | agree | agree |
| 20 | the same with the first one's type used | 2, `4:1-9` (same) | agree | agree |
| 21 | `include N` at top, `include O` in a submodule using `E("x")`, then `E(1)` outside | 0 | DIFFER (2) | agree |
| 22 | `include N`, `open O`, `E("x")` (the open wins) | 0 | agree | agree |
| 23 | `include N`, local `exception E(string)` in a function, `E(1)` outside | 0 | DIFFER (2) | agree |
| 24 | unused, `module M: {} = {module N = {exception E}; include N}` | 0, 38 `1:29-39` (the declaration in N only) | agree | agree |
| 25 | unused with a value of N used, `M: {let x: int}` | 0, 38 `1:39-49` | agree | agree |
| 26 | unused extension constructor, `M: {type t = ..}` | 0, 38 `1:63` | agree | agree |
| 27 | misspelt `Ex` for `Exc` | 2, `3:9-10` "The variant constructor Ex can't be found." (no hint) | agree | agree |
| 28 | `E(1, 2)` for `E(int)` | 2, `3:10-15` "This has type: ('a, 'b) But it's expected to have type: int" | DIFFER (2, "can't be found") | agree |
| 29 | `E("x")` for `E(int)` | 2, `3:11-13` "This has type: string But it's expected to have type: int" | DIFFER (2, "can't be found") | agree |
| 30 | `let v: int = E` for `type t += E` | 2, `3:14` "This has type: t (defined as N.t) But it's expected to have type: int" | DIFFER (2, "can't be found") | agree |
| 31 | two units, `Main` does `include Lib` with `exception E(int)` and `type t += C`, uses `E(1)` and `C`; `Third` builds and matches `Main.E` and reads `Main.C` (project) | 0 | DIFFER (2 in Main) | agree |
| 32 | `M: {let x: int}` including the unit `Lib` with an exception, nothing used (project) | 0 | agree | agree |
| 33 | `Main.resi` `include Lib.S` (a module type with `exception E(int)`), `Third` reads `Main.E` (project) | 0 | agree | agree |
| 34 | R1's row 21: `M: {exception A}` with `include N; exception A = E` | 0 | DIFFER (2) | agree |
| 35 | `M: {let v: exn}`, `include N; let v = E` | 0 | DIFFER (2) | agree |
| 36 | `include N; exception A = E` at top level | 0 | DIFFER (2) | agree |
| 37 | `type t += E` in N at top, `include N; type t += A = E` | 0 | DIFFER (2) | agree |
| 38 | `module rec A: {include S; module B: module type of {let v = E}}`, `S` has `exception E` | 0 | DIFFER (2, `5:13` "can't be found") | agree after `b37b435e0` |
| 39 | `module rec A: {include S; let f: unit => exn}` | 0 | agree | agree |

Every program of R1 above still agrees, its row 21 now included.

#### Open

- No program here showed M7.

### S1 - an extension constructor declared in a signature gets no unused warning

The place is M7 of "Fourth round: modules, aliases and usage marks" below;
its witnesses are M7-6 and M7-7:

```rescript
module M: {} = {module N: {exception E(int)} = {exception E(int)}}
```

OCaml prints one warning, 60 "unused module N." at `1:24-65`. Rust also
printed warning 38 "unused exception E" at `1:28-43`, the declaration in
the signature of N. The same with `type t += E` in the signature prints 38
"unused extension constructor E". The constructors of a variant declared in
a hidden signature showed the same difference, with warning 37 "unused
constructor A.".

Commands as in "Scope, calibration and reproducibility" (OCaml `bsc` from
`dune build`, Rust from thin-LTO release builds of `3ab5ec3bd3` (before)
and of the fix (after), the runtime built by `build-reference` with the
OCaml `bsc`). Each program is `Main.res`, with `Main.resi` where the table
says so (compiled first, then `Main.res` with `-bs-read-cmi` against the
interface the OCaml `bsc` wrote). Both compile with `-w +A -bs-jsx 4 -color
never -I . -I packages/@rescript/runtime/lib/rescript`, and stdout (the
JavaScript), stderr and the exit status are compared byte for byte.

#### Fixed

- `f64c72ed9`. OCaml translates a signature in `Env.in_signature true
  env` (`compiler/ml/typemod.ml:916`) and clears the flag for the module
  expression of `module type of` (`typemod.ml:776`). The delayed unused
  check of a constructor (`compiler/ml/env.ml:1689`) and of an extension
  constructor (`env.ml:1729`, `store_extension`) reports only when the
  environment the declaration was added to is not in a signature.
- Rust already took this decision: `check_constructor_usages` and
  `check_extension_usage` (`compiler-rust/src/types/typecore.rs`) take
  `env.is_in_signature()`, and the report skips the check when it is set.
  Nothing ever set the flag: `EnvFlags::in_signature` was only read.
  The declarations of a signature stayed quiet only when an inclusion
  check marked them. A signature that is itself checked against an
  outer one (M7-2, M7-3, the unit's interface) gets that mark. A signature
  hidden by an outer one (M7-6, M7-7, functor parameters and results,
  recursive modules and module types inside a hidden module) does not, so
  it kept warnings 37 and 38.
- The new `Env::in_signature` (`compiler-rust/src/types/env.rs`) is
  `Env.in_signature`. `transl_signature`
  (`compiler-rust/src/types/typemod.rs`) starts from
  `env.in_signature(true)`, and its `Pmty_typeof` arm types the module
  expression in `env.in_signature(false)`. This is the mechanism the
  ordinary constructors already read, so both kinds are fixed by one
  change.
- Cost: setting the flag copies the environment's bindings once per
  signature, the copy the signature's first binding makes anyway. An
  empty signature pays one copy. Lookups do not change.
- Fixtures: super_errors `signature_extension_unused_submodule`,
  `_functor`, `_variant` (the ordinary twins) and `_implementation` (an
  implementation's constructor keeps each of its three warning texts:
  "unused exception E", "exception E is never used to build values.
  (However, this constructor appears in patterns.)", and "extension
  constructor E is never used to build values. It is exported or rebound
  as a private extension.", `compiler/ext/warnings.ml:340-352`).

Programs through both compilers. OCaml status 0 is accepted and 2
rejected; the warnings are OCaml's (number and location). DIFFER is a
difference in the JavaScript, the diagnostics or the status; the "Before"
column gives the extra Rust warnings.

| # | Program | OCaml | Before (Rust) | After (Rust) |
| --- | --- | --- | --- | --- |
| 1 | M7-1, `Main.resi` and `Main.res` both `exception E(int)` | 0 | agree | agree |
| 2 | M7-2, `module M: {exception E(int)} = {exception E(int)}` | 0 | agree | agree |
| 3 | M7-3, the same with `type t += E(int)` | 0 | agree | agree |
| 4 | M7-4, interface and implementation with `type t += E(int)` | 0 | agree | agree |
| 5 | M7-5, signature `E(int)` against implementation `E(string)` | 2, `1:32-52` "Signature mismatch" | agree | agree |
| 6 | M7-6, `N: {exception E(int)}` hidden by `M: {}` | 0, 60 `1:24-65` | DIFFER (38 `1:28-43`) | agree |
| 7 | M7-7, the same without an argument | 0, 60 `1:24-55` | DIFFER (38 `1:28-38`) | agree |
| 8 | M7-8, the same with `let e = N.E` | 0, 32 `1:62` | agree | agree |
| 9 | `type t += E` in the hidden signature of N | 0, 60 `3:10-41` | DIFFER (38 `3:24`) | agree |
| 10 | `module N: {exception E} = {exception E}`, no outer signature | 0 | agree | agree |
| 11 | the same with `type t += E` | 0 | agree | agree |
| 12 | hidden N with `N.E` exported through a value | 0 | agree | agree |
| 13 | functor parameter `(X: {exception E}) => {}` | 0 | agree | agree |
| 14 | the same hidden by `M: {}` | 0, 60 `1:24-51` | DIFFER (38 `1:33-43`) | agree |
| 15 | functor parameter `(X: {type t += E})` | 0 | agree | agree |
| 16 | functor parameter `(X: {type t = A \| B})` (ordinary twin of 13) | 0 | agree | agree |
| 17 | functor result `(X: {}): {exception E} => {exception E}` | 0 | agree | agree |
| 18 | the same hidden by `M: {}` | 0, 60 `1:24-66` | DIFFER (38 `1:38-48`) | agree |
| 19 | `module type S = {exception E}`, nothing uses it | 0 | agree | agree |
| 20 | the same inside `M: {}` | 0 | DIFFER (38 `1:34-44`) | agree |
| 21 | `module type S = {type t += E}`, nothing uses it | 0 | agree | agree |
| 22 | `module type S` used by a hidden `module N: S` | 0, 60 `2:24-43` | agree | agree |
| 23 | `module type S = {type t = A \| B}` inside `M: {}` (ordinary twin of 20) | 0, 34 `1:34-47` | DIFFER (37 for A and for B) | agree |
| 24 | first-class module of a type with `exception E`, unpacked | 0, 32 `4:21` | agree | agree |
| 25 | `module rec A: {exception E} = {exception E}` | 0 | agree | agree |
| 26 | the same inside `M: {}` | 0, 60 `1:17-59` | DIFFER (38 `1:32-42`) | agree |
| 27 | `Main.resi` and `Main.res` both `exception E` | 0 | agree | agree |
| 28 | `Main.res` defines `exception F` that `Main.resi` does not list | 0, 38 `2:1-11` "unused exception F" | agree | agree |
| 29 | the same with `type u = C` (ordinary twin of 28) | 0, 34 `2:1-10`, 37 `2:1-10` | agree | agree |
| 30 | `Main.resi` and `Main.res` both `type t = A \| B` | 0 | agree | agree |
| 31 | signature nested two deep, `N: {module P: {exception E}}`, hidden | 0, 60 `1:35-50`, 60 `1:24-80` | DIFFER (38 `1:39-49`) | agree |
| 32 | the same with `type t += E` | 0, 60 `2:35-50`, 60 `2:24-80` | DIFFER (38 `2:49`) | agree |
| 33 | the same with an exception, no outer signature | 0 | agree | agree |
| 34 | `N: {type t += private E} = {type t += E}`, hidden | 0, 38 `2:62` "... is never used to build values. It is exported or rebound as a private extension.", 60 `2:24-63` | DIFFER (38 `2:46` "unused extension constructor E") | agree |
| 35 | the same, no outer signature | 0, 38 `2:46` (private text) | agree | agree |
| 36 | the same matched as `N.E` in an unused value | 0, 38 `2:62` (private text), 32 `2:70` | DIFFER (38 `2:46`) | agree |
| 37 | implementation exception never used, `M: {} = {exception E}` | 0, 38 `1:17-27` "unused exception E" | agree | agree |
| 38 | implementation exception used only in a pattern | 0, 38 `1:34-44` "exception E is never used to build values. (However, this constructor appears in patterns.)" | agree | agree |
| 39 | implementation extension constructor exported as private | 0, 38 `2:46` "extension constructor E is never used to build values. It is exported or rebound as a private extension." | agree | agree |
| 40 | `N: {type t = A \| B}` hidden (ordinary twin of 6) | 0, 34 `1:28-41`, 60 `1:24-61` | DIFFER (37 for A and for B) | agree |
| 41 | the same, no outer signature (ordinary twin of 10) | 0 | agree | agree |
| 42 | the same with `N.A` matched and exported through a value (ordinary twin of 12) | 0 | DIFFER (37 `1:38-51` "constructor B is never used to build values.") | agree |
| 43 | `module type T = module type of {exception E}` | 0 | agree | agree |
| 44 | `module type of {exception E}` inside a signature | 0 | agree | agree |
| 45 | the same with a variant, hidden | 0, 60 `1:24-127` | agree | agree |
| 46 | hidden `N: module type of X` where X has `exception E` | 0, 60 `2:24-58` | agree | agree |

All programs of R1 and I1 above still agree.

#### Open

Nothing of this place.

### P1 - an equation can refine an abstract type reached through a module path

The place is G6 of "Fifth round: patterns, equations and compatibility"
(pull request 337); its witness is G6-2. Reduced:

```rescript
type rec t<_> = I: t<int>
module F = (X: {type t}) => {
  let f = (I: t<X.t>, v: X.t): int => v
}
```

OCaml accepts it: matching `I` adds the equation `X.t = int`. Rust
rejected `v` with "This has type: X.t / But it's expected to have type:
int". With the result annotated `: string` both reject, and OCaml prints
"X.t (defined as int)" and the conversion hint "You can convert int to
string with Int.toString."; Rust printed neither, since it had no equation.

Commands as in "Scope, calibration and reproducibility" of the Fifth round
(OCaml `bsc` from `dune build`, Rust from thin-LTO release builds of
`5fd5b73eb2` (before) and of the fix (after), the runtime built by
`build-reference` with the OCaml `bsc`, `-w +A -bs-jsx 4 -color never`,
stdout, stderr and the exit status compared byte for byte). The program
with a library unit is a project of `Lib.resi`, `Lib.res` and `Main.res`,
built by `rescript build` and by `rescript build-reference` with the OCaml
`bsc`, comparing `Main.js`.

| # | index of the equation | OCaml | before | after |
| --- | --- | --- | --- | --- |
| 1 | functor parameter `X.t`, constructor `I: t<int>` in a parameter | accepted | DIFFER (rejected at `v`) | agree |
| 2 | functor parameter, `eq<X.t, int>` and `eq<X.t, string>` | accepted | DIFFER | agree |
| 3 | 1 with result `: string` | rejected, "(defined as int)" and conversion hint | DIFFER (no note, no hint) | agree |
| 4 | result of a generative functor, `R.t` | accepted | DIFFER | agree |
| 5 | sealed submodule `N: {type t} = {type t = int}`, used outside as `N.t` | accepted | DIFFER | agree |
| 6 | first-class module unpacked, `module M = unpack(m)`, the function returned | rejected, `M.t` would escape | DIFFER (rejected at `v`) | agree |
| 7 | recursive module `A.t`, inside and outside | accepted | DIFFER | agree |
| 8 | two deep, `P.Q.t` | accepted | DIFFER | agree |
| 9 | `type t = private int` (has a manifest) | rejected | agree | agree |
| 10 | private row `type t = private [< #a \| #b]` | rejected at the result | DIFFER (rejected at the pattern) | DIFFER, agrees after P2 |
| 11 | parameterized `X.t<int>` (arity 1) | rejected | agree | agree |
| 12 | top-level abstract `type t` of the same unit, a bare identifier | rejected | agree | agree |
| 13 | locally abstract `(type a)` | accepted | agree | agree |
| 14 | standard library `Date.t` | accepted | DIFFER | agree |
| 15 | two functor parameters, `eq<X.t, Y.u>` | accepted | DIFFER | agree |
| 16 | functor parameter against a locally abstract type | accepted | agree | agree |
| 17 | `switch` over `I: t<int> \| S: t<string>` at `t<X.t>`, one case and both | accepted, warning 8 "\| S" for the one case | agree | agree |
| 18 | the same at the sealed `N.t` | accepted, warning 8 "\| S" | agree | agree |
| 19 | the same at the same unit's abstract `u` | rejected | agree | agree |
| 20 | the same at `type t = private int` | accepted, no warning | agree | agree |
| 21 | the same at `X.t<int>` | accepted, warning 8 "\| S" | agree | agree |
| 22 | the same, `y: X.t` used as `int` and as `string` in the two cases | accepted | DIFFER | agree |
| 23 | 2 with result `: string` | rejected, "(defined as int)" and conversion hint | DIFFER | agree |
| 24 | `eq<Lib.t, int>` with `Lib.resi` declaring `type t`, and a `switch` at `t<Lib.t>` with the case `S` missing | accepted, `Match_failure` for `S` in `Main.js` | DIFFER (rejected at `v`) | agree (JavaScript; Rust reports warning 8, which `build-reference` does not show) |
| 25 | the `switch` of 22 with the case `S` missing, `y + 1` in `I` | accepted, warning 8 "\| S" | DIFFER (rejected at `y`) | agree |

The G6 candidates G6-1 and G6-3 to G6-8 agreed before and agree after.
Program 10 differs because OCaml expands `X.t` to its private row and
reaches the variant arm of `unify3`; that is P2 below.

#### Fixed

- OCaml's `is_instantiable` (`compiler/ml/ctype.ml:1874-1881`) looks up
  the declaration of the whole path with `Env.find_type` and asks that it
  be abstract, public, nullary, without manifest and not `non_aliasable`
  (`ctype.ml:1870-1872`: a bare identifier without a newtype level). So
  `X.t` is instantiable without a newtype level. The Rust
  `is_instantiable` (`compiler-rust/src/types/ctype.rs:579` before the fix)
  differed in two ways: it looked the declaration up by the last name
  alone (`path.head_name()`, "t" for `X.t`), and it required a newtype
  level for every path. A trace (a temporary print in `is_instantiable`)
  showed that each decides alone for programs 1 and 2: in program 1 the
  last-name lookup found the indexed type `t<_>` itself, a variant; in
  program 2 it found no `t`; and the declaration of the whole path `X.t`
  is abstract, without manifest, and has no newtype level, so the level
  test also failed.
- `is_instantiable` (`compiler-rust/src/types/ctype.rs`) now does what
  OCaml's does, on the declaration `lookup_type_decl_for_path` finds for
  the whole path. `find_newtype_level` is OCaml's (`ctype.ml:2084-2091`):
  the declaration's newtype level, else the path's binding time twice;
  the equation's declaration gets it, and the choice between two
  instantiable sides compares it. `add_gadt_equation` is OCaml's
  (`ctype.ml:2093-2100`); the caller reifies the destination first, as
  `unify3` does (`ctype.ml:2382-2389`), in `unify_gadt_equation`, which
  replaces the two copies of these arms in `unify_types`. Commit
  `4a248ec60`.
- Fixtures: `tests/tests/src/pattern_equation_module_path.res` (the
  accepted programs), super_errors
  `pattern_equation_module_path_mismatch` (program 3),
  `pattern_equation_same_unit_abstract` (program 12) and
  `pattern_equation_module_path_unused_case` (program 25).

#### Open

Nothing of this place.

### P2 - a row clash in a pattern is retried as OCaml retries it

The place is G3 of "Fifth round: patterns, equations and compatibility"
(pull request 337); its witnesses are G3-1 to G3-4 and G3-7. Reduced:

```rescript
type rec t<_> = A: t<[#a]>
let f = (x: t<[#a | #b]>) => switch x { | A => 0 }
```

Both reject the pattern with "This pattern matches values of type
t<[#a]> / but a pattern was expected which matches values of type
t<[#a | #b]>"; Rust then also printed "The first polymorphic variant is
closed and doesn't include the constructor: #b." and its "Possible
solutions:" lines (at `t<[#b]>`: "These polymorphic variants are
incompatible - they share no common constructors."). Where the rows clash
but are compatible, OCaml accepts the pattern and Rust rejected it: an
index that is a functor parameter's private row, as P1's program 10.

Commands as in P1, Rust from the P1 commit (before) and from the fix
(after).

| # | program | OCaml | before | after |
| --- | --- | --- | --- | --- |
| 1 | `A: t<[#a]>` at `t<[#a \| #b]>` | rejected, no row detail | DIFFER (closed-row detail) | agree |
| 2 | the same at `t<[#b]>` | rejected, no row detail | DIFFER ("share no common constructors") | agree |
| 3 | at `t<[> #a]>` | accepted | agree | agree |
| 4 | at `t<[< #a \| #b]>` | accepted | agree | agree |
| 5 | `A: t<[#a(int)]>` at `t<[#a(string)]>` | rejected | agree | agree |
| 6 | `A: t<[#a(int)]>` at `t<[#a(b)]>`, `(type b)`, `y: b` used as `int` | accepted | agree | agree |
| 7 | `A: t<[> #a]>` at `t<[#b]>` | rejected, no row detail | DIFFER | agree |
| 8 | `A: t<[< #a \| #b]>` at `t<[#a]>` | accepted | agree | agree |
| 9 | `A \| B` one case at `[#a]`, `[#b]`, `[#a \| #b]`, `[> #a]` in one unit | rejected | DIFFER | agree |
| 10 | `A \| B` both cases at `[#a]` (G3-4) | rejected | DIFFER | agree |
| 11 | no index (`generate_equations` off): `type u = U([#a])` in a function parameter, a `let` and a `switch` | accepted | agree | agree |
| 12 | the same, `U(#c)` against `U([#a \| #b])` | rejected | agree | agree |
| 13 | the clash inside a tuple index `t<([#a \| #b], int)>` | rejected, no row detail | DIFFER | agree |
| 14 | the clash inside a record index `t<r<[#b]>>` | rejected, no row detail | DIFFER | agree |
| 15 | the row variable bound by an earlier equation, `eq<r, [#a \| #b]>` then `t<r>` | rejected, no row detail | DIFFER | agree |
| 16 | `[#a(X.b)]` with a functor parameter's `X.b` (an equation, P1) | accepted | agree | agree |
| 17 | `t<r>` with `(type r)` | accepted | agree | agree |
| 18 | `A \| B` both cases at `[#a \| #b]` and at `[> #a]` | rejected | DIFFER | agree |
| 19 | `let A = x` at `t<[#a \| #b]>` | rejected, no row detail | DIFFER | agree |
| 20 | `A: t<[#a(int)]> \| B: t<[#a(string)]>`, one case at `[#a(int)]` | accepted, no warning | agree | agree |
| 21 | `eq<X.t, [#a]>` with `X.t = private [< #a \| #b]` | accepted | DIFFER (rejected) | agree |
| 22 | `eq<X.t, [#a \| #b]>` with `X.t = private [> #a]` | accepted | DIFFER (rejected) | agree |
| 23 | `A \| B` at `t<X.t>`, `X.t = private [< #a \| #b]`, both cases and one | accepted, warning 8 "\| B" for the one case | DIFFER (rejected) | agree |
| 24 | the same with `X.t = private [> #a]` | rejected | DIFFER | agree |
| 25 | the same with `X.t = private [< #a]` | rejected | DIFFER | agree |
| 26 | `A: t<[#a(int)]>` at `X.t = private [< #a(int) \| #b]` | accepted | DIFFER (rejected) | agree |
| 27 | the same at `X.t = private [< #a(string) \| #b]` | rejected | DIFFER | agree |
| 28 | `A: t<([#a], [#b])>` at `t<(X.t, X.t)>`, `X.t = private [< #a \| #b]` | accepted | DIFFER (rejected) | agree |
| 29 | `A \| B`, `[> #a]` with only `A`, `[#a \| #b]` with only `B` | rejected | DIFFER | agree |
| 30 | `U(A)` with `type u = U(t<[#a \| #b]>)` in a parameter | rejected | DIFFER | agree |
| 31 | `switch U(x) { \| U(#a) => 0 }` with `x: [#a \| #b]` | rejected | agree | agree |
| 32 | `A \| B` both cases at `[< #a \| #b]` | rejected | DIFFER | agree |
| 33 | `A \| B` one case `A` at `[#a]`, `B` at `[#b]`, `A` at `[> #a]`, `A` at `[< #a \| #b]` | accepted, no warning | agree | agree |
| 34 | `A \| B` one case `A` at `[#a \| #b]`, `B` at `[> #a]` | rejected, no row detail | DIFFER | agree |

The G3 candidates G3-5, G3-6 and G3-8 agreed before and agree after; P1's
programs all agree after this commit, program 10 included.

#### Fixed

- In Pattern mode OCaml's variant arm of `unify3`
  (`compiler/ml/ctype.ml:2400-2411`) takes a snapshot, and when
  `unify_row` raises it backtracks, reifies both sides and, when equations
  are generated, tests only `mcomp`; the error, if any, carries no row
  detail, and a compatible pair is accepted. The Rust variant arm of
  `unify_types` (`compiler-rust/src/types/ctype.rs`) called `unify_rows`
  and returned its error, row detail included, in both modes.
- The arm now does what OCaml's does in Pattern mode: the type snapshot
  the constructor arguments already use (`snapshot_type_state`), taken
  only in Pattern mode, is restored on a clash and the pair goes to
  `unify_pattern_constructor_mismatch`, the reify-and-`mcomp` step of the
  constructor arm (`ctype.ml:2396-2399`). Expression mode is unchanged.
  Commit `b22d458c9`.
- Fixtures: `tests/tests/src/pattern_equation_private_row.res` (programs
  21, 22, 23, 26 and 28), super_errors `pattern_equation_row_closed`
  (program 1), `pattern_equation_row_disjoint` (2),
  `pattern_equation_row_nested` (13),
  `pattern_equation_row_private_unused_case` (23) and
  `pattern_equation_row_private_payload` (27).

#### Open

Nothing of this place.

### A1 - an instance of a type that is ambiguous outside its equation is refused

Found while fixing: the Rust compiler accepted, and compiled, programs whose
value has a type known only through a GADT equation and leaves the case of
that equation. OCaml refuses them. Witnesses, both verified on trunk
`109b2bd4c`:

```rescript
type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => if true { y } else { 0 }
  }
```

OCaml refuses at 4:33: "This has type: int / But this if statement is
expected to return: a (defined as int) / This instance of int is ambiguous:
/ it would escape the scope of its equation / if expressions must return
the same type in all branches (if, else if, else)." Rust emitted
`function f(x, y) { return y; }`. The second witness, `[y, 0]` under
`Int =>` next to `Str => []`, is refused at 4:16 ("This array item has
type: int / But this array is expected to have items of type: a (defined
as int)" and the same two lines, then the array advice and its "Possible
solutions:"); Rust accepted it.

Commands are the ones in "Scope, calibration and reproducibility": each
program is `Main.res` alone, run with `bsc -w +A -bs-jsx 4 -color never
Main.res` through both compilers; "agree" is the same exit status and the
same output byte for byte (the whole diagnostic, its location, the
JavaScript and every warning). Rust before is trunk `109b2bd4c`, after is
the second commit below. The witnesses are p01 and p02; p03 to p30 are the
shapes asked for (each expression form whose branches are unified, the
`eq<'a, 'b>` witness, a nested constructor pattern, two equations for one
type, an outer function's locally abstract type, the programs that must
stay accepted, an object and a variant row, abbreviations as the
equation's right side); q01 to q18 and r01 to r16 probe the remaining
OCaml sites. `T` is `type rec t<_> = Int: t<int>` and the function is
`(type a, x: t<a>, y: a) => switch x { ... }` unless the row says
otherwise.

| # | program | OCaml | Rust before | Rust after |
| --- | --- | --- | --- | --- |
| p01 | `if true { y } else { 0 }` under `Int =>` (witness 1) | refused at 4:33 | DIFFER (accepted) | agree |
| p02 | `[y, 0]` under `Int =>`, `Str => []` (witness 2) | refused at 4:16 | DIFFER (accepted) | agree |
| p03 | witness 1 with `: int` on `f` | accepted | agree | agree |
| p04 | `Int => y + 1` | accepted | agree | agree |
| p05 | a `switch b` inside the branch returning `y` and `0` | refused at 7:16 | DIFFER (accepted) | agree |
| p06 | `(0, 1)` and `(y, 2)` from two cases of `t<int>` | accepted | agree | agree |
| p07 | `{a: y, b: 0}` of `r<'a>` | refused at 5:12-23 | DIFFER (accepted) | agree |
| p08 | `let z = switch ...` unannotated, used after it | refused at 6:28 | DIFFER (accepted) | agree |
| p09 | `b => if b { y } else { 0 }` returned | refused at 4:35 | DIFFER (accepted) | agree |
| p10 | `r := Some(if true { y } else { 0 })` | refused at 5:43 | DIFFER (accepted) | agree |
| p11 | `eq<a, b>`, `Refl => if true { x } else { y }` | accepted | agree | agree |
| p12 | `eq<a, int>`, `Refl => if true { y } else { 0 }` | refused at 4:34 | DIFFER (accepted) | agree |
| p13 | `Some(Int) =>` (nested constructor) | refused at 4:39 | DIFFER (accepted) | agree |
| p14 | `Int` and `Str` cases, each mixing `y` and a literal | refused at 4:33 | DIFFER (accepted) | agree |
| p15 | `a` of the outer function, `switch` in an inner one | refused at 5:35 | DIFFER (accepted) | agree |
| p16 | `(y: int)` in the branch | accepted | agree | agree |
| p17 | `h(y)` with `h: int => int` | accepted | agree | agree |
| p18 | `Ex(Int, v) => v + 1` | accepted | agree | agree |
| p19 | `{"f": y}` and `{"f": 0}` (object row) | refused at 4:40-47 | DIFFER (accepted) | agree |
| p20 | `#A(y)` and `#A(0)` (variant row) | refused at 4:40 | DIFFER (accepted) | agree |
| p21 | `type u = int`, `U: t<u>`, `y` and `0` | refused at 5:31 | DIFFER (accepted) | agree |
| p22 | the same with `(1: u)` first | refused at 5:36 | DIFFER (accepted) | agree |
| p23 | witness 2 with `: array<int>` | accepted | agree | agree |
| p24 | `Ex(Int, v) => ignore(v)` | accepted | agree | agree |
| p25 | `#A(y)` and `#B(0)` | accepted | agree | agree |
| p26 | witness 1 with `: a` on `f` | accepted | agree | agree |
| p27 | an open object parameter and `{"f": y}` | refused at 6:28-35 | DIFFER (accepted) | agree |
| p28 | `type v = u`, `type u = int`, `V: t<v>`, `[y, 0]` | refused at 6:14 | DIFFER (accepted) | agree |
| p29 | `{v: 0}` and `{v: y}` from `Int` and `Str` | refused at 6:16 | agree | agree |
| p30 | `let k = switch x { \| Int => y }; k + 1` | refused at 6:3 | agree | agree |
| q01 | `let k = () => if true { y } else { 0 }; k()` | refused at 6:7-9 | DIFFER (accepted) | agree |
| q02 | `let k = z => if true { z } else { 0 }; [k(y)]` | refused at 6:8-11 | DIFFER (accepted) | agree |
| q03 | `{"f": 0, "g": y}` against an open object | accepted | agree | agree |
| q04 | `r := Some({"f": if true { y } else { 1 }})` | refused at 5:22-52 | DIFFER (accepted) | agree |
| q05 | `#A(0)`, `#A(y)` and a variant parameter | refused at 6:52 | DIFFER (accepted) | agree |
| q06 | `[< #A(int) \| #B]` parameter, `#A(n)` or `#A(y)` | accepted | agree | agree |
| q07 | `let z: u = y; [z, y]` | refused at 7:11 | DIFFER (accepted) | agree |
| q08 | `let z: u = y; r := [z]` | accepted | agree | agree |
| q09 | `g(y, ...)`, `g: (int, 'm) => int` | accepted | agree | agree |
| q10 | `g(y, ...)`, `g = (n, m: int) => if ... n else m` | refused at 5:12-20 | DIFFER (accepted) | agree |
| q11 | `L: t<list<'b>>`, `List.length(y)` | accepted | agree | agree |
| q12 | `id(if true { y } else { 0 })` | refused at 5:12-39 | DIFFER (accepted) | agree |
| q13 | `Some(if true { 1 } else { y })` | refused at 4:38 | DIFFER (accepted) | agree |
| q14 | two switches, two equations, `(y + 1, w ++ "")` | accepted | agree | agree |
| q15 | the same returning `(y, w)` or `(0, "")` | refused at 7:41 | DIFFER (accepted) | agree |
| q16 | `Box(y)` or `Box(0)` | refused at 5:42 | DIFFER (accepted) | agree |
| q17 | `o["m"] + 0` with `o = {"m": y}` | accepted | agree | agree |
| q18 | `r = ref(y)` outside, `r.contents + 1` inside | accepted | agree | agree |
| r01 | `let w = 1; y == w; w` | accepted | agree | agree |
| r02 | `let _ = [y, w]; w` | accepted | agree | agree |
| r03 | `let w: u = 1; y == w; [w]` | accepted | agree | agree |
| r04 | `y == w` with a parameter `w: int` | accepted | agree | agree |
| r05 | `o["g"] == 1`, `{"f": y, "g": 0}` | accepted | agree | agree |
| r06 | `o := Some({"f": y})`, read after the switch | refused at 9:13 | agree | agree |
| r07 | `v == #A(1)`, then `v` or `#A(y)` | refused at 6:31 | DIFFER (accepted) | agree |
| r08 | `r := Some(#A(y))` | accepted | agree | agree |
| r09 | `g(y) + 1` then `g(0)`, `g` a parameter | refused at 6:9 | DIFFER (accepted) | agree |
| r10 | `g(if true { y } else { 0 })` | refused at 4:35 | DIFFER (accepted) | agree |
| r11 | `Lst: t<list<int>>`, `List.length(y)` | accepted | agree | agree |
| r12 | `eq<a, int>`, `y == w; w` | accepted | agree | agree |
| r13 | `let w = ref(1); y == w.contents; w.contents` | accepted | agree | agree |
| r14 | `let w = [1]`, `y == w[0]...`, `w` | accepted | agree | agree |
| r15 | `let g = n => n; g(y) == 1; g` | accepted | agree | agree |
| r16 | `w.contents == y; w` | accepted | agree | agree |

There is no principal mode in this compiler, and none of the sites below
reads one.

#### Fixed

- `92862d207`. OCaml keeps, per `switch` (or function) whose patterns may
  add equations, a set of the types known only through an equation
  (`gadt_instances`, `compiler/ml/env.ml:368`, `1305-1345`; a level is
  added by `type_cases` and the function form,
  `compiler/ml/typecore.ml:4034-4042`, `4822-4828`). While tracing is on
  (under local constraints, `compiler/ml/ctype.ml:176-191`, which also
  forgets the memorized expansions), `expand_abbrev_gen`
  (`ctype.ml:1215-1227`) refuses to expand a type whose level is below the
  equation's expansion level or its set's, and adds the type and its
  expansion to the set; `try_expand_head` (`ctype.ml:1270-1276`) adds the
  chain of an expansion that ends in an instance; `update_level`
  (`ctype.ml:587-589`) refuses to lower an instance below its set's level.
  The refusal is `Unify [(ty, newvar2 level)]`, which `printtyp.ml:1340-1362`
  prints as "This instance of ... is ambiguous". Rust's
  `Env::add_gadt_instance_level` took no level and tracked nothing. Now
  the sets are in the type context (`TypeContext::new_gadt_instance_scope`,
  `gadt_instance_level`, `add_gadt_instances`, `add_gadt_instance_chain`,
  `compiler-rust/src/types/context.rs:5725-5845`), each scope holding its
  enclosing one's handle, and the environment holds the innermost handle
  (`compiler-rust/src/types/env.rs:2810`). Both callers of
  `add_gadt_instance_level` (`typecore.rs:11976`, `13625`) build the case
  environment as a clone of the outer one; with the handle in the shared
  bindings record, a clone copies a `u32` and never a set, and every
  environment of a case sees the set as OCaml's share its `ref`. Additions
  are journaled (`TypeMutation::GadtInstance`) and undone on backtrack, as
  OCaml trails `set_typeset`. The equation records the pattern's newtype
  level as its expansion level (`env.ml:1805-1810`;
  `add_gadt_equation`, `ctype.rs:1839`); `check_trace_gadt_instances`
  forgets the memorized expansions (`ctype.ml:182`); the expansion test is
  `try_expand_head_traced`, which wraps trunk's `try_expand_head_with_mode`
  (since `cbaf8d70d`) and, while tracing, tests an equation before the
  expansion, which it does not affect; the traced head expansion
  (`expand_head_traced`) adds the chain; the unifier's expansions
  (`unify2`, `ctype.ml:2289-2292`) propagate the refusal
  (`expand_heads_unif`, `expand_head_in_unify`);
  `update_level_pass` (`ctype.rs:2999`) makes the level test. Without OCaml's arm of `unify`
  for two nullary locally abstract types (`ctype.ml:2255-2268`: expand
  only the later one, lower nothing first), p11 became refused. A trace
  with the arm disabled shows `unify_types` lowering the copy of `b`
  (level 2008) and `a` to the outer level 1005 before expanding, and the
  expansion of the copy of `b` then refused (1005 below the instance
  level 1008); OCaml's arm expands that copy at its own level.
  `unify_newtypes` (`ctype.rs:610`) is that arm. The level test costs one load (`has_gadt_instances`) and one
  branch per level update in a unit where no type has joined a set.
- `22a53a612`. OCaml's `copy ?env` (`ctype.ml:770-774`), reached through
  `instance env` and `instance_list env` (`ctype.ml:877-894`), adds the
  copy of an instance to its set under local constraints. A function
  generalized inside a case (q01) gave Rust copies that were no instances.
  `instance_in` and `instance_list_in` (`ctype.rs:12451`) take the
  environment and, only under local constraints with an instance scope,
  walk the finished copy's table once (`add_copied_gadt_instances`,
  `ctype.rs:12503`); the typecore sites of OCaml's `instance env` use them.
- `752db1e00` keeps these tests off the default path (see "Cost" below);
  `b46a3af77` adds nothing where an environment has an equation but no
  instance scope at its level, a state OCaml asserts against
  (`env.ml:1326-1328`), which the type checker does not build and the
  checker tests on trunk do.
- Fixtures: super_errors `gadt_instance_ambiguous_*` (the 30 programs
  refused by OCaml that Rust accepted: p01, p02, p05, p07-p10, p12-p15,
  p19-p22, p27, p28, q01, q02, q04, q05, q07, q10, q12, q13, q15, q16, r07,
  r09, r10), and `tests/tests/src/gadt_instance_ambiguous_accepted.res`
  (31 accepted programs, the JavaScript of each compared by the
  JavaScript parity suite).

#### Open

No program of the 64 shows a difference at these OCaml sites, which are
not ported: the chain of `unify2` after expansion (`ctype.ml:2293-2298`:
r01-r04, r12-r16 were written for it and agree), the level test of
`unify_fields` (`ctype.ml:2490`: q03, r05, r06), of `unify_row`'s row
variable (`ctype.ml:2609-2611`: q05, q06, r07, r08), the tracing wrappers
of `unify_var` (`ctype.ml:2759-2766`), `expand_head_trace`
(`ctype.ml:2782-2784`), the application's `lower_args`
(`typecore.ml:2828`: q09, q10, r09, r10) and `local_non_recursive_abbrev`
(`ctype.ml:1533-1534`: q11, r11), and `copy ?env ~partial` through
`instance ~partial env` (Rust's `instance_partial`). The level updates
that Rust makes without an environment (`update_level`, for the same
nullary constructor, universal variables, object and row variables) make
no level test; no program here reaches one with an instance. The port
was stopped at the sites a program shows, as the size limit of the task
asks. The chain of `try_expand_head` (`ctype.ml:1273-1275`) is added
whenever the environment at hand has an instance scope
(`expand_head_traced`, since `c3cd63b5d`), as OCaml adds it whatever the
tracing flag, for example while the result of a `switch` is lowered in
the outer environment after its cases. Five programs aimed at that moment
(an abbreviation whose expansion is the instance: a local module's
`type u = a`, `type box<'a> = 'a` returned from the case, compared, and
bound in a `let` used after the `switch`, with and without a result
annotation) are accepted by OCaml and by Rust.

Two programs aimed at the guard (see "Cost" below) agree. In the first,
the unit's first `switch` (on an `option<int>`) has no generalized
constructor and its second, `switch x { | Int => if true { y } else { 0 } }`
with `x: t<a>` and `y: a`, refuses the instance: OCaml and Rust both
print "This instance of int is ambiguous" at `9:33`. In the second, a
first function adds the instance (`[y, 0]` under `Int`) and two later
functions with no generalized constructor lower types through a `switch`
(`Some(n) => [n, f(Int, n)]`, and a `ref([])` assigned in a case): both
compilers accept it with the same JavaScript.

Cost: open. Every read of an instance set answers nothing while every set
is empty, and a set gets its first member only from the test of
`expand_abbrev_gen` (`ctype.ml:1217-1227`) while tracing. So the type
context's flag is "a type has been added to an instance set in this
unit" (`has_gadt_instances`, set in `push_gadt_instance`, since
`82e309f01`), kept in one byte with the tracing flag. Copies and level
updates test it, then the environment's scope handle; the expansion sites
test the byte (`expands_gadt_instances`: tracing or a member), so the
test that adds the first member still runs. Scopes are created as before:
434 of the 788 units of `tests/tests` add one, 2,169 in all, because
OCaml's `type_cases` adds an instance level for a `switch` without a
generalized constructor whenever the exhaustiveness check will run
(`typecore.ml:4814-4818`, `4913-4914`; Rust `typecore.rs` at the
`needs_exhaust_check` test). 7 of the 788 units add an instance.

The CI `Instruction count` check on a clean `tests/tests` build:
+12,960,104 (+0.313%) for `7d08707fd`, +11,397,960 (+0.276%) for
`c0daf094f`, +7,466,613 (+0.181%) for `4679c1d94`, +5,138,728
(+0.124%) for `fe245f217` (base 4,134,734,897, head 4,139,873,625). The
last, split into the guard sites (one load and one branch each), (a) the
rest of what a unit pays that adds no instance, and (b) the work while
tracing or after a member:

| | function | change |
| --- | --- | ---: |
| site | the unifier's pairs (`expand_heads_unif`) | +497,792 |
| site | `instance_in` / `instance_list_in` at typecore's sites: `type_application_parts` +398,277, `type_identifier` +130,678, `type_function_nary` +96,633, `instance_in` +65,613, `instance_list_in` +44,386 | +735,587 |
| site | `update_level_checked_above` | +140,409 |
| site | `expand_head_with_mode`'s guard, inlined into `moregen` at its two `expand_head` calls | +129,160 |
| site | `try_expand_head` | +56,221 |
| a | `unify`: the newtype arm (`unify_newtypes`, `is_newtype`, `find_newtype_level`) is inlined into it since `82e309f01`, its frame grows from 0x1e8 to 0x238 bytes and every call spills more | +1,130,695 |
| a | `expand_head_plain` +12,100,981 against `expand_head_with_mode` -12,250,409 | -149,428 |
| a | scope creation: `Env::data_mut` +190,067, `Env::add_gadt_instance_level` +89,597, `make_mut` +76,159 and +46,401 | +402,224 |
| a | `restore_type_state` (the journal's new entry) | +97,242 |
| a | `unify_types` -166,879, `lower_plain_levels::lower` -54,768 | -221,647 |
| b | `gadt_instance_level` +679,023, `repr_chain` +642,364 | +1,321,387 |
| b | `try_expand_head_traced` +242,590, `expand_head_traced::<true>` +108,040, `::<false>` +64,273, `Env::find_local_constraint` +46,958 | +461,861 |
| b | `update_level_pass` +89,441, `instance_with_gadt_instances` +45,419 | +134,860 |

The sites come to +1,559,169, (a) to +1,259,086 (+0.0305%, 18,666 above
+0.03%) and (b) to +1,918,108. The remaining +402,365 is
`IdTbl::find_by_ident` (-501,294) and the allocator, which move by as
much between runs.

Measured locally (fat LTO, one codegen unit, five runs a side; trunk
459b87ca5 as base): `bcc2a4ef4` +4,401,645, the flag `82e309f01`
+6,529,629 (not lower, kept because the flag defines (a)), one
instantiation of the expansion `cbaf8d70d` +5,694,179, trunk's calls at
the unifier's sites `fe245f217` +5,213,073.

## Fourth round: modules, aliases and usage marks

### Scope, commands and calibration

Tested commit: `8590ce4c03`. This is an investigation, not a compiler fix. Each candidate below was actually run with a ten-second per-compiler timeout; every source ends with a newline. Captured stdout and stderr are pasted verbatim, including ANSI escapes emitted despite `-color never`; empty fences mean empty streams. Exit status, both streams, and (where requested) the JavaScript file were compared. M3 JavaScript comparisons also remove blank lines. Repeated setup attempts are retained and excluded from witness attribution. No OCaml internal error is used as a reference.

The ten places were investigated in order, with reductions, reachability probes and dependency-setup repairs afterwards. The counts include those repairs and syntax failures, not just successful checker entries. All source instrumentation was restored byte-for-byte before writing this section; the committed diff contains only this document and the internal changelog fragment.

```sh
export PATH="$HOME/.cargo/bin:$PATH"
export ROOT="$PWD"
export RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime"
export TERM=dumb NO_COLOR=1
unset MODULE_SEARCH_TRACE
eval $(opam env)
dune build --root .
CARGO_TARGET_DIR="$TMPDIR/modules-target" CARGO_PROFILE_RELEASE_LTO=thin \
  cargo build --release --manifest-path rewatch/Cargo.toml
export OCAML_BSC="$ROOT/_build/install/default/bin/bsc"
export RUST="$TMPDIR/modules-target/release/rescript"
"$RUST" build-reference --bsc "$OCAML_BSC" packages/@rescript/runtime
# RUST_BSC is an executable wrapper: exec "$RUST" bsc "$@"
RUST_BSC="$SCRATCH/bsc" PARITY_JOBS=1 bash scripts/test_error_output_parity.sh \
  --release --compiler-only access_functor_as_structure.res
```

The first Cargo build using the prepopulated default target failed writing a cached dependency file (`No such file or directory`); the fresh target above succeeded. OCaml build exited 0 with empty output. The successful Rust build ended with:

```text
warning: `rescript` (lib) generated 1 warning (run `cargo fix --lib -p rescript` to apply 1 suggestion)
warning: `rescript` (lib) generated 1 warning (1 duplicate)
    Finished `release` profile [optimized] target(s) in 2m 59s
```

The warning is the existing unused `console::style` import at `rewatch/src/build/packages.rs:12`. Runtime preparation and parity calibration (terminal styling and the machine-specific cache-location line omitted from this summary only):

```text
OCaml reference build: 113 of 113 modules built
Compiler diagnostics parity

Error output parity summary
  total:  2
  pass:   2
  fail:   0
SUCCESS: OCaml and Rust diagnostic output match for tested fixtures.
```

An initial direct calibration invocation lacked the runtime: OCaml reported missing Pervasives and Rust requested RESCRIPT_RUNTIME. It was corrected by building and exporting the runtime above; those setup failures are not checker results. The calibrated fixture is `tests/build_tests/super_errors/fixtures/access_functor_as_structure.res`:

```rescript
module F = (
  M: {
    let x: int
  },
) => {
  let v = M.x
}

let _: F.v = 1
```

Both compilers, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  tests/build_tests/super_errors/fixtures/access_functor_as_structure.res:9:8-10

   7 │ }
   8 │ 
   9 │ let _: F.v = 1
  10 │ 

  The module F is a functor, not a structure

```

Each candidate uses a fresh directory under `$TMPDIR`, with the listed sources and this `rescript.json`:

```json
{"name":"checker-probe","sources":["."]}
```

The working directory is the candidate directory. The ordinary invocation for each listed file, in listed order, is:

```sh
timeout 10 "$OCAML_BSC" -w +A -bs-jsx 4 -color never \
  -I . -I "$RESCRIPT_RUNTIME/lib/rescript" [EXTRA] FILE
timeout 10 "$RUST" bsc -w +A -bs-jsx 4 -color never \
  -I . -I "$RESCRIPT_RUNTIME/lib/rescript" [EXTRA] FILE
```

Compile an interface first; append `-bs-read-cmi` to EXTRA only for an implementation with its matching interface. OCaml runs the whole source sequence first, then Rust runs the sequence against the OCaml-built interface. A compiler sequence stops after its first nonzero status. Each Rust invocation is repeated with `MODULE_SEARCH_TRACE=1` for reachability; those trace lines are not included in the comparison streams. No diagnostic is filtered from a comparison run.

For dependency-package runs, `dependency/` contains copies of the listed Lib.res/Lib.resi and its own rescript.json; run `"$RUST" build-reference --bsc "$OCAML_BSC" dependency` before either compiler and add `-I dependency/lib/rescript`. This is the parity script’s package protocol: OCaml reads the compiled package, while Rust builds it in memory. Dependency configuration and the exact EXTRA variant for every multi-unit attempt are specified below. The final setup explicitly requests CommonJS for the dependency, passes `-bs-project-root . -bs-package-name checker-probe -bs-package-output commonjs:.`, and removes only the generated root Lib.cmi/Lib.cmj/Lib.js before compiling Main.res so both read the same dependency rather than two different copies.

### Reachability measurements

The single successful Rust release build included temporary, environment-guarded eprintln markers. With MODULE_SEARCH_TRACE unset the markers do not print; there is no alternate compiler behavior. The guarded inserts were removed from the source after building. The markers report branch entry, not causality or numeric node-level differences.

| Marker | Inserted at |
| --- | --- |
| M1 | nondep_sig before its item loop, typemod.rs:2461 |
| M2 | nondep_mty functor arm, typemod.rs:2415 |
| M3 plus alias presence | convert_module_expr_raw0 before its alias test, convert.rs:4227 |
| M4 | lookup_modtype dotted arm, env.rs:2701 |
| M5 | describe_tables before alias_sources.push, module_view.rs:819 |
| M6 | lookup_rebind_constructor entry, typemod.rs:561 |
| M7-M8 | extension_constructors entry, includemod.rs:4948 |
| M9 | package arm before level reads, ctype.rs:9074 |
| M10-entry/full/shortcut | inferred_signature_coercion entry, fallback return, and shortcut mark, includemod.rs:2218-2221 |

M5 is also hit while initializing the runtime. Control-1 below logs it 60 times; local-only candidates do not establish world-table reachability merely by logging that same count. The final dependency Main.res logs 63. No claim is made about the uninstrumented value-lookup fallback.

### Summary

| Place | Verdict | Candidates |
| --- | --- | ---: |
| M1 | REACHED, NO DIFFERENCE SEEN | 13 |
| M2 | REACHED, NO DIFFERENCE SEEN | 9 |
| M3 | NOT REACHED | 16 |
| M4 | REACHED, NO DIFFERENCE SEEN | 10 |
| M5 | REACHED, NO DIFFERENCE SEEN | 11 |
| M6 | WITNESS | 9 |
| M7 | WITNESS | 8 |
| M8 | REACHED, NO DIFFERENCE SEEN | 6 |
| M9 | REACHED, NO DIFFERENCE SEEN | 12 |
| M10 | REACHED, NO DIFFERENCE SEEN | 6 |

### M1 — REACHED, NO DIFFERENCE SEEN

Apply a functor to a non-path argument so that `nondep_supertype` eliminates the parameter from a result signature (`typemod.rs:15287`, `nondep_sig:2452`; `mtype.ml:126-160`). Check the exposed dependent types, aliases and exceptions, including rejected uses, for an order-sensitive change in diagnostics or JavaScript.

M1-7–9 and M1-11–13 hit M1 and agree. Correction to the proposed premise: OCaml does recurse into the remainder first, but neither implementation extends the environment per item here; `mtype.ml:101-103` explicitly says that the environment need not be kept up to date. M1-1–6 were invalid same-line declarations; M1-10 was an invalid separator repair. They are retained rather than counted as reachability evidence.

#### M1-1 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t let x: t}) => {type t = X.t let x = X.x}
module R = F({type t = int let x = 1})
let y: int = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:23-26

  1 │ module F = (X: {type t let x: t}) => {type t = X.t let x = X.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: int = R.x

  consecutive specifications on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:51-54

  1 │ module F = (X: {type t let x: t}) => {type t = X.t let x = X.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: int = R.x

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:2:27-30

  1 │ module F = (X: {type t let x: t}) => {type t = X.t let x = X.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: int = R.x
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-2 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t let x: t}) => {let x = X.x type t = X.t}
module R = F({type t = int let x = 1})
let y: string = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:23-26

  1 │ module F = (X: {type t let x: t}) => {let x = X.x type t = X.t}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: string = R.x

  consecutive specifications on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:50-54

  1 │ module F = (X: {type t let x: t}) => {let x = X.x type t = X.t}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: string = R.x

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:2:27-30

  1 │ module F = (X: {type t let x: t}) => {let x = X.x type t = X.t}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: string = R.x
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-3 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t let x: t}) => {module A = X module B = A let x = B.x}
module R = F({type t = int let x = 1})
let y = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:23-26

  1 │ module F = (X: {type t let x: t}) => {module A = X module B = A let x = 
    │ B.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y = R.x

  consecutive specifications on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:51-57

  1 │ module F = (X: {type t let x: t}) => {module A = X module B = A let x = 
    │ B.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y = R.x

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:64-67

  1 │ module F = (X: {type t let x: t}) => {module A = X module B = A let x = 
    │ B.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y = R.x

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:2:27-30

  1 │ module F = (X: {type t let x: t}) => {module A = X module B = A let x = 
    │ B.x}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y = R.x
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-4 — outputs agree

`Main.res`:

```rescript
module F = (X: {module type S module A: S}) => {module type T = X.S module B = X.A}
module R = F({module type S = {let x: int} module A = {let x = 1}})
let y = R.B.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:68-74

  1 │ module F = (X: {module type S module A: S}) => {module type T = X.S modu
    │ le B = X.A}
  2 │ module R = F({module type S = {let x: int} module A = {let x = 1}})
  3 │ let y = R.B.x

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:2:43-49

  1 │ module F = (X: {module type S module A: S}) => {module type T = X.S modu
    │ le B = X.A}
  2 │ module R = F({module type S = {let x: int} module A = {let x = 1}})
  3 │ let y = R.B.x
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-5 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t let x: t}) => {type a = X.t type b = a let pair = (X.x, X.x)}
module R = F({type t = int let x = 1})
let y: (int, string) = R.pair
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:23-26

  1 │ module F = (X: {type t let x: t}) => {type a = X.t type b = a let pair =
    │  (X.x, X.x)}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: (int, string) = R.pair

  consecutive specifications on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:51-55

  1 │ module F = (X: {type t let x: t}) => {type a = X.t type b = a let pair =
    │  (X.x, X.x)}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: (int, string) = R.pair

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:62-65

  1 │ module F = (X: {type t let x: t}) => {type a = X.t type b = a let pair =
    │  (X.x, X.x)}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: (int, string) = R.pair

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:2:27-30

  1 │ module F = (X: {type t let x: t}) => {type a = X.t type b = a let pair =
    │  (X.x, X.x)}
  2 │ module R = F({type t = int let x = 1})
  3 │ let y: (int, string) = R.pair
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-6 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t}) => {type a = X.t exception E(a) module N = {type b = a}}
module R = F({type t = int})
let e = R.E(1)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:42-51

  1 │ module F = (X: {type t}) => {type a = X.t exception E(a) module N = {typ
    │ e b = a}}
  2 │ module R = F({type t = int})
  3 │ let e = R.E(1)

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:1:57-63

  1 │ module F = (X: {type t}) => {type a = X.t exception E(a) module N = {typ
    │ e b = a}}
  2 │ module R = F({type t = int})
  3 │ let e = R.E(1)

  Consecutive statements on a line must be separated by ';' or a newline

```

#### M1-7 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {type t = X.t; let x = X.x}
module R = F({type t = int; let x = 1})
let y: int = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x1, TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return X;
}

let R = {
  x: 1
};

let y = 1;

exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M1-8 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {let x = X.x; type t = X.t}
module R = F({type t = int; let x = 1})
let y: string = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:17-19

  1 │ module F = (X: {type t; let x: t}) => {let x = X.x; type t = X.t}
  2 │ module R = F({type t = int; let x = 1})
  3 │ let y: string = R.x
  4 │ 

  This has type: [1;31mint[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M1-9 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {module A = X; module B = A; let x = B.x}
module R = F({type t = int; let x = 1})
let y = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {
    A: X,
    B: undefined,
    x: X.x
  };
}

let X = {
  x: 1
};

let R = {
  A: X,
  B: undefined,
  x: 1
};

let y = 1;

exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M1-10 — outputs agree

`Main.res`:

```rescript
module F = (X: {module; type S; module A: S}) => {module; type T = X.S; module B = X.A}
module R = F({module; type S = {let x: int}; module A = {let x = 1}})
let y = R.B.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:1:23

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x

  At this point, I'm looking for an uppercased name like `Array` or `Math`


  Syntax error!
  Main.res:1:30

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x

  Did you mean `s` instead of `S`?


  Syntax error!
  Main.res:1:57

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x

  At this point, I'm looking for an uppercased name like `Array` or `Math`


  Syntax error!
  Main.res:1:64

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x

  Did you mean `t` instead of `T`?


  Syntax error!
  Main.res:2:21

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x
  4 │ 

  At this point, I'm looking for an uppercased name like `Array` or `Math`


  Syntax error!
  Main.res:2:28

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x
  4 │ 

  Did you mean `s` instead of `S`?


  Syntax error!
  Main.res:2:43

  1 │ module F = (X: {module; type S; module A: S}) => {module; type T = X.S; 
    │ module B = X.A}
  2 │ module R = F({module; type S = {let x: int}; module A = {let x = 1}})
  3 │ let y = R.B.x
  4 │ 

  Did you forget a `=` here?

```

#### M1-11 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {type a = X.t; type b = a; let pair = (X.x, X.x)}
module R = F({type t = int; let x = 1})
let y: (int, string) = R.pair
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:24-29

  1 │ module F = (X: {type t; let x: t}) => {type a = X.t; type b = a; let pai
    │ r = (X.x, X.x)}
  2 │ module R = F({type t = int; let x = 1})
  3 │ let y: (int, string) = R.pair
  4 │ 

  This has type: [1;31m(int, int)[0m
  But it's expected to have type: [1;33m(int, string)[0m
  
  The incompatible parts:
    [1;31mint[0m vs [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M1-12 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t}) => {type a = X.t; exception E(a); module N = {type b = a}}
module R = F({type t = int})
let e = R.E(1)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

function F(X) {
  let E = /* @__PURE__ */Primitive_exceptions.create("Main.F(X).E");
  let N = {};
  return {
    E: E,
    N: N
  };
}

let E = /* @__PURE__ */Primitive_exceptions.create("Main.F(X).E");

let N = {};

let R = {
  E: E,
  N: N
};

let e = {
  RE_EXN_ID: E,
  _1: 1
};

exports.F = F;
exports.R = R;
exports.e = e;
/* No side effect */
```

stderr:

```text
```

#### M1-13 — outputs agree

`Main.res`:

```rescript
module F = (X: {
module type S
module A: S
}) => {
module type T = X.S
module B = X.A
}
module R = F({
module type S = {let x: int}
module A = {let x = 1}
})
let y = R.B.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x3, TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {
    B: X.A
  };
}

let A = {
  x: 1
};

let R = {
  B: A
};

let y = 1;

exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

### M2 — REACHED, NO DIFFERENCE SEEN

Make that non-path application return an inner functor, whose parameter or result mentions the eliminated outer parameter (`nondep_mty`, `typemod.rs:2410-2448`; `mtype.ml:118-125`). Then re-export or include a module of the inner parameter and compare its aliasability, resulting types and JavaScript.

M2-1–5 and the corrected dependency-package run M2-9 agree and hit M2. M2-6–8 are setup attempts, not checker witnesses.

#### M2-1 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {type u = X.t}) => {module A = Y}
}
module R = F({type t = int})
module Q = R.G({type u = int})
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x6, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

let Q = {
  A: {}
};

exports.F = F;
exports.R = R;
exports.Q = Q;
/* No side effect */
```

stderr:

```text
```

#### M2-2 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {
module G = (Y: {let y: X.t}) => {module A = Y; let x = X.x}
}
module R = F({type t = int; let x = 1})
module Q = R.G({let y = 2})
let x = Q.A.y
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x6, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y,
    x: X.x
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y,
    x: 1
  };
}

let R = {
  G: G
};

let Y = {
  y: 2
};

let Q = {
  A: Y,
  x: 1
};

let x = Y.y;

exports.F = F;
exports.R = R;
exports.Q = Q;
exports.x = x;
/* No side effect */
```

stderr:

```text
```

#### M2-3 — outputs agree

`Main.res`:

```rescript
module F = (X: {module type S}) => {
module G = (Y: X.S) => {module A = Y}
}
module R = F({module type S = {let x: int}})
module Q = R.G({let x = 1})
let x = Q.A.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x6, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

let Q = {
  A: {
    x: 1
  }
};

let x = Q.A.x;

exports.F = F;
exports.R = R;
exports.Q = Q;
exports.x = x;
/* No side effect */
```

stderr:

```text
```

#### M2-4 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {module N: {type t = X.t}; module A = N}) => {module B = Y.A}
}
module R = F({type t = int})
module Q = R.G({module N = {type t = int}; module A = N})
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x6, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M3 MtaAbsent x2, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    B: undefined
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    B: undefined
  };
}

let R = {
  G: G
};

let Q = {
  B: undefined
};

exports.F = F;
exports.R = R;
exports.Q = Q;
/* No side effect */
```

stderr:

```text
```

#### M2-5 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t; let x: t}) => {
module G = (Y: {let y: X.t}) => {module A = Y; let x = X.x}
}
module R = F({type t = int; let x = 1})
module Q = R.G({let y = "wrong"})
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x8, TRACE M2 x2, TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:5:16-32

  3 │ }
  4 │ module R = F({type t = int; let x = 1})
  5 │ module Q = R.G({let y = "wrong"})
  6 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:5:21):
    let y: string
  
  Expected declaration (Main.res:2:17-26):
    let y: int

```

#### M2-6 — setup attempt

`Lib.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {type u = X.t; let y: u}) => {module A = Y}
}
module R = F({type t = int})
```

`Main.res`:

```rescript
module Q = Lib.R.G({type u = int; let y = 2})
let y: string = Q.A.y
```

Setup: plain `-I .`, no dependency package. These attempts cannot supply a dependency to the in-process Rust CLI. M2-6/M3-6 also cleaned the OCaml artifacts before Rust; M4-5 retained them.

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M1 x4, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
Main.res: TRACE M5 x60
```

OCaml, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

OCaml, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-21

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  This has type: [1;31mQ.A.u[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:12-18

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  [1;33mThe module or file Lib can't be found.[0m
  - If it's a third-party dependency:
    - Did you add it to the "dependencies" or "dev-dependencies" in rescript.json?
  - Did you include the file's directory to the "sources" in rescript.json?
  

```

#### M2-7 — setup attempt

`Lib.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {type u = X.t; let y: u}) => {module A = Y}
}
module R = F({type t = int})
```

`Main.res`:

```rescript
module Q = Lib.R.G({type u = int; let y = 2})
let y: string = Q.A.y
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M1 x8, TRACE M10-entry x2, TRACE M10-full x2, TRACE M2 x2, TRACE M5 x60
Main.res: TRACE M1 x8, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-21

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  This has type: [1;31mQ.A.u[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-21

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  This has type: [1;31mQ.A.u[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M2-8 — no reference (OCaml internal setup error)

`Lib.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {type u = X.t; let y: u}) => {module A = Y}
}
module R = F({type t = int})
```

`Main.res`:

```rescript
module Q = Lib.R.G({type u = int; let y = 2})
let y: string = Q.A.y
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:.`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M1 x8, TRACE M10-entry x2, TRACE M10-full x2, TRACE M2 x2, TRACE M5 x60
Main.res: TRACE M1 x8, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

OCaml, Lib.res, exit 2; stdout:

```text
```

stderr:

```text
Fatal error: exception Failure("File \"compiler/ext/ext_path.ml\", line 122, characters 27-34bsc was invoked without -bs-project-root; cannot determine the package root. Pass -bs-project-root <dir> or invoke bsc via rewatch / cli/bsc.js.")
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

exports.F = F;
exports.R = R;
/* No side effect */
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-21

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  This has type: [1;31mQ.A.u[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M2-9 — outputs agree

`Lib.res`:

```rescript
module F = (X: {type t}) => {
module G = (Y: {type u = X.t; let y: u}) => {module A = Y}
}
module R = F({type t = int})
```

`Main.res`:

```rescript
module Q = Lib.R.G({type u = int; let y = 2})
let y: string = Q.A.y
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M1 x8, TRACE M10-entry x2, TRACE M10-full x2, TRACE M2 x2, TRACE M5 x60
Main.res: TRACE M1 x8, TRACE M10-entry x1, TRACE M10-full x1, TRACE M2 x1, TRACE M5 x60
```

Both compilers, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let G = Y => ({
    A: Y
  });
  return {
    G: G
  };
}

function G(Y) {
  return {
    A: Y
  };
}

let R = {
  G: G
};

exports.F = F;
exports.R = R;
/* No side effect */
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-21

  1 │ module Q = Lib.R.G({type u = int; let y = 2})
  2 │ let y: string = Q.A.y
  3 │ 

  This has type: [1;31mQ.A.u[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

### M3 — NOT REACHED

Give `convert_module_expr_raw0` a module expression whose type is `MtyAlias(MtaPresent, _)` (`convert.rs:4221-4240`), rather than the absent aliases that OCaml erases (`translmod.ml:257-267`). Check the emitted JavaScript, including functor bodies, includes, packing and an interface boundary, for an incorrectly erased module value.

No candidate logged `TRACE M3 MtaPresent`; the logged aliases are all `MtaAbsent`. The unsatisfied condition is the present-alias expression type at `convert.rs:4229`, not the ability to write an ordinary alias: `typemod.ml:1269` initially gives a module identifier an absent alias and the following aliasability/coercion logic can replace it with a signature. M3-1–5, 7–8, 13–14 and the repaired two-unit M3-16 agree in JavaScript, also after removing blank lines. M3-6, 9–11 and 15 are setup attempts; M3-12 is invalid inline package-type syntax.

#### M3-1 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
let y = A.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

let y = 1;

exports.N = N;
exports.A = A;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-2 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module F = (X: {let x: int}) => {module A = X; let y = A.x}
module R = F(N)
let y = R.y
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

function F(X) {
  return {
    A: X,
    y: X.x
  };
}

let R = {
  A: N,
  y: 1
};

let y = 1;

exports.N = N;
exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-3 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module R = {module A = N; include A}
let y = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x2, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let R = {
  A: undefined,
  x: 1
};

let y = 1;

exports.N = N;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-4 — outputs agree

`Main.resi`:

```rescript
module N: {let x: int}
module A = N
let y: int
```

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
let y = A.x
```

Trace counts from the separate instrumented invocations:

```text
Main.resi: TRACE M5 x60
Main.res: TRACE M3 MtaAbsent x1, TRACE M5 x60
```

Both compilers, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

let y = 1;

exports.N = N;
exports.A = A;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-5 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module F = (X: {module N: {let x: int}; module M = N}) => {module Z = X.M}
module R = F({module N = N; module M = N})
let y = R.Z.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x1, TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x3, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

function F(X) {
  return {
    Z: undefined
  };
}

let R = {
  Z: undefined
};

let y = 1;

exports.N = N;
exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-6 — setup attempt

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

Setup: plain `-I .`, no dependency package. These attempts cannot supply a dependency to the in-process Rust CLI. M2-6/M3-6 also cleaned the OCaml artifacts before Rust; M4-5 retained them.

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x1, TRACE M5 x60
Main.res: TRACE M5 x60
```

OCaml, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

OCaml, Main.res, exit 2; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Lib.js not found, needed in script mode 

```

Rust, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:12-16

  1 │ module B = Lib.A
  2 │ module R = {include B}
  3 │ let y = R.x

  [1;33mThe module or file Lib can't be found.[0m
  - If it's a third-party dependency:
    - Did you add it to the "dependencies" or "dev-dependencies" in rescript.json?
  - Did you include the file's directory to the "sources" in rescript.json?
  

```

#### M3-7 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
module R = {include A}
module type S = module type of A
module P: S = N
let y = P.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x3, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let R = {
  x: 1
};

let A;

let P = N;

let y = 1;

exports.N = N;
exports.A = A;
exports.R = R;
exports.P = P;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-8 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
module type S = {module M: module type of A}
module F = (X: S) => {include X.M}
module R = F({module M = N})
let y = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x1, TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x2, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

function F(X) {
  return {
    x: X.M.x
  };
}

let R = {
  x: 1
};

let A;

let y = 1;

exports.N = N;
exports.A = A;
exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-9 — setup attempt

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M3 MtaAbsent x1, TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x61
```

OCaml, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M3-10 — no reference (OCaml internal setup error)

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:.`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M3 MtaAbsent x1, TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x61
```

OCaml, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Lib.res, exit 2; stdout:

```text
```

stderr:

```text
Fatal error: exception Failure("File \"compiler/ext/ext_path.ml\", line 122, characters 27-34bsc was invoked without -bs-project-root; cannot determine the package root. Pass -bs-project-root <dir> or invoke bsc via rewatch / cli/bsc.js.")
```

Rust, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M3-11 — setup attempt

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M3 MtaAbsent x1, TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x61
```

OCaml, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("./Lib.js");

let x = Lib.N.x;

let R = {
  x: x
};

let B;

let y = x;

exports.B = B;
exports.R = R;
exports.y = y;
/* No side effect */
```

Rust, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M3-12 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
let p = module(A: {let x: int})
```

Trace counts from the separate instrumented invocations:

```text
Main.res: (none)
```

Both compilers, Main.res, exit 1; stdout:

```text
```

stderr:

```text

  Syntax error!
  Main.res:3:19

  1 │ module N = {let x = 1}
  2 │ module A = N
  3 │ let p = module(A: {let x: int})
  4 │ 

  At this point, I'm looking for an uppercased name like `Array` or `Math`


  Syntax error!
  Main.res:3:18-19

  1 │ module N = {let x = 1}
  2 │ module A = N
  3 │ let p = module(A: {let x: int})
  4 │ 

  Consecutive statements on a line must be separated by ';' or a newline


  Syntax error!
  Main.res:3:30

  1 │ module N = {let x = 1}
  2 │ module A = N
  3 │ let p = module(A: {let x: int})
  4 │ 

  Did you forget a `=` here?

```

#### M3-13 — outputs agree

`Main.res`:

```rescript
module N = {let x = 1}
module A = N
module F = (X: {module M = N}) => {include X.M}
module R = F({module M = A})
let y = R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x1, TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x3, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

function F(X) {
  return {
    x: 1
  };
}

let R = {
  x: 1
};

let A;

let y = 1;

exports.N = N;
exports.A = A;
exports.F = F;
exports.R = R;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M3-14 — outputs agree

`Main.res`:

```rescript
module type S = {let x: int}
module N = {let x = 1}
module A = N
let p = module(A: S)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x1, TRACE M5 x60, TRACE M9 x2
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

let p = N;

exports.N = N;
exports.A = A;
exports.p = p;
/* No side effect */
```

stderr:

```text
```

#### M3-15 — setup attempt

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."],"package-specs":{"module":"commonjs","in-source":true}}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M3 MtaAbsent x1, TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x61
```

OCaml, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("./Lib.js");

let x = Lib.N.x;

let R = {
  x: x
};

let B;

let y = x;

exports.B = B;
exports.R = R;
exports.y = y;
/* No side effect */
```

Rust, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

Rust, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("probe-dependency/Lib.js");

let x = Lib.N.x;

let R = {
  x: x
};

let B;

let y = x;

exports.B = B;
exports.R = R;
exports.y = y;
/* No side effect */
```

#### M3-16 — outputs agree

`Lib.resi`:

```rescript
module N: {let x: int}
module A = N
```

`Lib.res`:

```rescript
module N = {let x = 1}
module A = N
```

`Main.res`:

```rescript
module B = Lib.A
module R = {include B}
let y = R.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."],"package-specs":{"module":"commonjs","in-source":true}}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

Before Main.res, remove root Lib.cmi, Lib.cmj and Lib.js (the separate dependency copies remain).

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.resi: TRACE M3 MtaAbsent x1, TRACE M5 x60
Lib.res: TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x61
```

Both compilers, Lib.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let N = {
  x: 1
};

let A;

exports.N = N;
exports.A = A;
/* No side effect */
```

Both compilers, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("probe-dependency/Lib.js");

let x = Lib.N.x;

let R = {
  x: x
};

let B;

let y = x;

exports.B = B;
exports.R = R;
exports.y = y;
/* No side effect */
```

### M4 — REACHED, NO DIFFERENCE SEEN

Use a dotted module type inside a module expression retained as `MtyIdent`, so a caller reaches the raw-signature dotted arm of `Env::lookup_modtype` (`env.rs:2700-2720`) instead of the component lookup (`env.ml:1555-1585`). Then use its dependent types, nested modules or recursive-module initialization and compare rejection diagnostics and generated JavaScript for a missing access-path substitution.

M4-8–10 hit the actual M4 marker and agree; M4-1–4, 6–7 agree without that marker. Merely writing `A.S` did not suffice: the functor parameter containing a submodule and the recursive modules retained the dotted module type until a raw lookup. M4-5 is a dependency setup attempt.

#### M4-1 — outputs agree

`Main.res`:

```rescript
module M = {type t = int; module type S = {let x: t}}
module A = M
module N: A.S = {let x = 1}
let y: string = N.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:4:17-19

  2 │ module A = M
  3 │ module N: A.S = {let x = 1}
  4 │ let y: string = N.x
  5 │ 

  This has type: [1;31mA.t[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M4-2 — outputs agree

`Main.res`:

```rescript
module M = {module Y = {module type S = {let x: int}}; module type S = Y.S}
module A = M
module N: A.S = {let x = 1}
let y = N.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let Y = {};

let M = {
  Y: Y
};

let N = {
  x: 1
};

let A;

let y = 1;

exports.M = M;
exports.A = A;
exports.N = N;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M4-3 — outputs agree

`Main.res`:

```rescript
module F = (X: {type t}) => {module type S = {let x: X.t}}
module M = F({type t = int})
module N: M.S = {let x = 1}
let y = N.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  return {};
}

let M = {};

let N = {
  x: 1
};

let y = 1;

exports.F = F;
exports.M = M;
exports.N = N;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M4-4 — outputs agree

`Main.res`:

```rescript
module M = {type t = int; module type S = {let x: t}}
module A: module type of M = M
module N: A.S = {let x = "bad"}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:17-31

  1 │ module M = {type t = int; module type S = {let x: t}}
  2 │ module A: module type of M = M
  3 │ module N: A.S = {let x = "bad"}
  4 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:3:22):
    let x: string
  
  Expected declaration (Main.res:1:44-51):
    let x: A.t

```

#### M4-5 — setup attempt

`Lib.res`:

```rescript
module M = {type t = int; module type S = {let x: t}}
module A = M
```

`Main.res`:

```rescript
module N: Lib.A.S = {let x = 1}
let y: string = N.x
```

Setup: plain `-I .`, no dependency package. These attempts cannot supply a dependency to the in-process Rust CLI. M2-6/M3-6 also cleaned the OCaml artifacts before Rust; M4-5 retained them.

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x1, TRACE M5 x60
Main.res: TRACE M5 x60
```

OCaml, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let A;

exports.M = M;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

OCaml, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-19

  1 │ module N: Lib.A.S = {let x = 1}
  2 │ let y: string = N.x
  3 │ 

  This has type: [1;31mLib.A.t[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let A;

exports.M = M;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:11-17

  1 │ module N: Lib.A.S = {let x = 1}
  2 │ let y: string = N.x
  3 │ 

  [1;33mThe module or file Lib can't be found.[0m
  - If it's a third-party dependency:
    - Did you add it to the "dependencies" or "dev-dependencies" in rescript.json?
  - Did you include the file's directory to the "sources" in rescript.json?
  

```

#### M4-6 — outputs agree

`Main.res`:

```rescript
module M = {module Y = {type t = int; module type S = {let x: t}}; module type S = Y.S}
module A = M
module type T = A.S
let unpack = (p: module(T)) => {module N = unpack(p: T); N.x}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x1, TRACE M5 x60, TRACE M9 x2
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let Y = {};

let M = {
  Y: Y
};

function unpack(p) {
  return p.x;
}

let A;

exports.M = M;
exports.A = A;
exports.unpack = unpack;
/* No side effect */
```

stderr:

```text
```

#### M4-7 — outputs agree

`Lib.res`:

```rescript
module M = {type t = int; module type S = {let x: t}}
module A = M
```

`Main.res`:

```rescript
module N: Lib.A.S = {let x = 1}
let y: string = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x2, TRACE M5 x60
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x1, TRACE M5 x61
```

Both compilers, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let A;

exports.M = M;
exports.A = A;
/* No side effect */
```

stderr:

```text
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:17-19

  1 │ module N: Lib.A.S = {let x = 1}
  2 │ let y: string = N.x
  3 │ 

  This has type: [1;31mLib.A.t[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M4-8 — outputs agree

`Main.res`:

```rescript
module M = {type t = int; module type S = {module N: {let x: t}}}
module F = (X: M.S) => {module A = X.N; let x = A.x}
module R = F({module N = {let x = 1}})
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x2, TRACE M10-entry x1, TRACE M10-full x1, TRACE M4 x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

function F(X) {
  let A = X.N;
  return {
    A: A,
    x: A.x
  };
}

let N = {
  x: 1
};

let R = {
  A: N,
  x: 1
};

exports.M = M;
exports.F = F;
exports.R = R;
/* No side effect */
```

stderr:

```text
```

#### M4-9 — outputs agree

`Main.res`:

```rescript
module M = {module Y = {module type S = {let f: int => int}}; module type S = Y.S}
module rec A: M.S = {let f = x => B.f(x)}
and B: M.S = {let f = x => x}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M4 x6, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let Y = {};

let M = {
  Y: Y
};

function f(x) {
  return x;
}

let B = {
  f: f
};

function f$1(x) {
  return x;
}

let A = {
  f: f$1
};

exports.M = M;
exports.A = A;
exports.B = B;
/* No side effect */
```

stderr:

```text
```

#### M4-10 — outputs agree

`Main.res`:

```rescript
module M = {module Y = {module type S = {let f: int => int}}; module type S = Y.S}
module O = M
module rec A: O.S = {let f = x => B.f(x)}
and B: O.S = {let f = x => x}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M3 MtaAbsent x1, TRACE M4 x4, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let Y = {};

let M = {
  Y: Y
};

function f(x) {
  return x;
}

let B = {
  f: f
};

function f$1(x) {
  return x;
}

let A = {
  f: f$1
};

let O;

exports.M = M;
exports.O = O;
exports.A = A;
exports.B = B;
/* No side effect */
```

stderr:

```text
```

### M5 — REACHED, NO DIFFERENCE SEEN

Read values, types or module types through an alias of a module containing a sibling alias, and through a persisted dependency so `describe_tables` registers its alias source (`module_view.rs:817-823`; `env.ml:1369-1410,1519`). Compare the accessed type identities, spelling hints and JavaScript, while distinguishing that table registration from the separate value-lookup fallback at `typecore.rs:22671`.

M5-1–5 agree locally; M5-11 agrees across the dependency package. The empty-value control and all local-only candidates log M5 60 times from runtime setup; that alone is not evidence for the candidate. M5-11 logs it 63 times for Main.res, registering the dependency aliases in addition to the 60 runtime registrations. The verdict covers `describe_tables`; the separate value-lookup fallback was not instrumented and its reachability is not claimed. M5-6–10 are retained setup attempts.

#### M5-1 — outputs agree

`Main.res`:

```rescript
module Outer = {module R = {type t = int; let x: t = 1}; module A = R}
module O = Outer
let y: int = O.A.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x2, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

let y = 1;

exports.Outer = Outer;
exports.O = O;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M5-2 — outputs agree

`Main.res`:

```rescript
module Outer = {module R = {type t = int; let x: t = 1}; module A = R}
module O = Outer
let y: string = O.A.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:17-21

  1 │ module Outer = {module R = {type t = int; let x: t = 1}; module A = R}
  2 │ module O = Outer
  3 │ let y: string = O.A.x
  4 │ 

  This has type: [1;31mO.A.t[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M5-3 — outputs agree

`Main.res`:

```rescript
module Outer = {module R = {type t = int; let x: t = 1}; module A = R}
module O = Outer
let y: O.A.t = Outer.R.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x2, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

let y = 1;

exports.Outer = Outer;
exports.O = O;
exports.y = y;
/* No side effect */
```

stderr:

```text
```

#### M5-4 — outputs agree

`Main.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}}; module A = R}
module O = Outer
module N: O.A.S = {let x = 1}
let y: string = N.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:4:17-19

  2 │ module O = Outer
  3 │ module N: O.A.S = {let x = 1}
  4 │ let y: string = N.x
  5 │ 

  This has type: [1;31mO.A.t[0m [2m(defined as[0m [1;31mint[0m[2m)[0m
  But it's expected to have type: [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M5-5 — outputs agree

`Main.res`:

```rescript
module Outer = {module R = {type thing = int; let value = 1}; module A = R}
module O = Outer
let y = O.A.vaule
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:9-17

  1 │ module Outer = {module R = {type thing = int; let value = 1}; module A =
    │  R}
  2 │ module O = Outer
  3 │ let y = O.A.vaule
  4 │ 

  The value vaule can't be found in O.A
  
  [1;33mHint: Did you mean value?[0m

```

#### M5-6 — setup attempt

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

OCaml, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

stderr:

```text
```

OCaml, Main.res, exit 2; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Lib.js not found, needed in script mode 

```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M5-7 — setup attempt

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Lib.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M5-8 — no reference (OCaml internal setup error)

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:.`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

OCaml, Lib.res, exit 2; stdout:

```text
```

stderr:

```text
Fatal error: exception Failure("File \"compiler/ext/ext_path.ml\", line 122, characters 27-34bsc was invoked without -bs-project-root; cannot determine the package root. Pass -bs-project-root <dir> or invoke bsc via rewatch / cli/bsc.js.")
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M5-9 — setup attempt

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."]}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("./Lib.js");

let x = Lib.Outer.R.x;

let N = {
  x: x
};

let P;

let y = x;

exports.P = P;
exports.N = N;
exports.y = y;
/* No side effect */
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

Rust, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res

  Missing dependency Lib in search path

```

#### M5-10 — setup attempt

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."],"package-specs":{"module":"commonjs","in-source":true}}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

This attempt leaves the root Lib artifacts in the load path.

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

OCaml, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

OCaml, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("./Lib.js");

let x = Lib.Outer.R.x;

let N = {
  x: x
};

let P;

let y = x;

exports.P = P;
exports.N = N;
exports.y = y;
/* No side effect */
```

Rust, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

Rust, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("probe-dependency/Lib.js");

let x = Lib.Outer.R.x;

let N = {
  x: x
};

let P;

let y = x;

exports.P = P;
exports.N = N;
exports.y = y;
/* No side effect */
```

#### M5-11 — outputs agree

`Lib.res`:

```rescript
module Outer = {module R = {type t = int; module type S = {let x: t}; let x = 1}; module A = R}
module O = Outer
```

`Main.res`:

```rescript
module P = Lib.O
module N: P.A.S = {let x = P.A.x}
let y: P.A.t = N.x
```

`dependency/rescript.json` (Lib sources copied unchanged):

```json
{"name":"probe-dependency","sources":["."],"package-specs":{"module":"commonjs","in-source":true}}
```

Additional flags: `-I dependency/lib/rescript -bs-package-name checker-probe -bs-package-output commonjs:. -bs-project-root .`.

Before Main.res, remove root Lib.cmi, Lib.cmj and Lib.js (the separate dependency copies remain).

Dependency OCaml prebuild, exit 0; stdout:

```text
OCaml reference build: 1 of 1 modules built
```

stderr:

```text
```

Trace counts from the separate instrumented invocations:

```text
Lib.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M3 MtaAbsent x4, TRACE M5 x60
Main.res: TRACE M10-entry x2, TRACE M10-full x1, TRACE M10-shortcut x1, TRACE M3 MtaAbsent x3, TRACE M5 x63
```

Both compilers, Lib.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let R = {
  x: 1
};

let Outer = {
  R: R,
  A: undefined
};

let O;

exports.Outer = Outer;
exports.O = O;
/* No side effect */
```

Both compilers, Main.res, exit 0; stdout:

```text
```

stderr:

```text
```

Generated JavaScript file:

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Lib = require("probe-dependency/Lib.js");

let x = Lib.Outer.R.x;

let N = {
  x: x
};

let P;

let y = x;

exports.P = P;
exports.N = N;
exports.y = y;
/* No side effect */
```

### M6 — WITNESS

Rebind an exception or extension constructor through a module path or an open, with the source module hidden by a signature so unused warnings remain observable (`lookup_rebind_constructor`, `typemod.rs:555-610`; `typedecl.ml:1694-1700`). Compare all usage warnings because OCaml constructor lookup marks the type path and modules (`typetexp.ml:109`, `env.ml:952-970,1147-1152`) in addition to the constructor mark.

M6-2, 3, 5–9 are witnesses; M6-1 and M6-4 agree. Smallest witness found: M6-7 (argument-free exceptions, no extra value); M6-8 isolates the extra module warning without the common unused-A warning, and M6-9 isolates the extra unused-open warning. M6-6 also shows the missing use marks at both levels of a module path. These all hit M6.

#### Fixed

Fixed by `f470283dd`; see "R1 - a rebind marks the type path and the modules
on its path as used" in "Third round: differences found while fixing". All
nine candidates agree after it.

#### M6-1 — outputs agree

`Main.res`:

```rescript
let f = () => {module M = {exception E(int)}; exception A = M.E; A(1)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

function f() {
  let E = /* @__PURE__ */Primitive_exceptions.create("E");
  return {
    RE_EXN_ID: E,
    _1: 1
  };
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### M6-2 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N = {exception E(int)}; exception A = N.E}
let x = 1
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:48-64

  1 │ module M: {} = {module N = {exception E(int)}; exception A = N.E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:24-45

  1 │ module M: {} = {module N = {exception E(int)}; exception A = N.E}
  2 │ let x = 1
  3 │ 

  unused module N.


  Warning number 38
  Main.res:1:48-64

  1 │ module M: {} = {module N = {exception E(int)}; exception A = N.E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

#### M6-3 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N = {exception E(int)}; open N; exception A = E}
let x = 1
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:56-70

  1 │ module M: {} = {module N = {exception E(int)}; open N; exception A = E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 33
  Main.res:1:48-53

  1 │ module M: {} = {module N = {exception E(int)}; open N; exception A = E}
  2 │ let x = 1
  3 │ 

  unused open N.


  Warning number 38
  Main.res:1:56-70

  1 │ module M: {} = {module N = {exception E(int)}; open N; exception A = E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

#### M6-4 — outputs agree

`Main.res`:

```rescript
module M: {} = {module N = {type t = ..; type t += E(int)}; type N.t += A = N.E}
let x = 1
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:73-79

  1 │ module M: {} = {module N = {type t = ..; type t += E(int)}; type N.t += 
    │ A = N.E}
  2 │ let x = 1
  3 │ 

  unused extension constructor A

```

#### M6-5 — WITNESS

`Main.resi`:

```rescript
exception A(int)
```

`Main.res`:

```rescript
module M = {exception E(int)}
exception A = M.E
```

Trace counts from the separate instrumented invocations:

```text
Main.resi: TRACE M5 x60, TRACE M7-M8 x1
Main.res: TRACE M5 x60, TRACE M6 x1, TRACE M7-M8 x2
```

OCaml, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let A = E;

exports.A = A;
/* No side effect */
```

stderr:

```text
```

Rust, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let A = E;

exports.A = A;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:8-29

  1 │ module M = {exception E(int)}
  2 │ exception A = M.E
  3 │ 

  unused module M.

```

#### M6-6 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N = {module P = {exception E(int)}}; exception A = N.P.E}
let x = 1
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:61-79

  1 │ module M: {} = {module N = {module P = {exception E(int)}}; exception A 
    │ = N.P.E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

let x = 1;

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:36-57

  1 │ module M: {} = {module N = {module P = {exception E(int)}}; exception A 
    │ = N.P.E}
  2 │ let x = 1
  3 │ 

  unused module P.


  Warning number 60
  Main.res:1:24-58

  1 │ module M: {} = {module N = {module P = {exception E(int)}}; exception A 
    │ = N.P.E}
  2 │ let x = 1
  3 │ 

  unused module N.


  Warning number 38
  Main.res:1:61-79

  1 │ module M: {} = {module N = {module P = {exception E(int)}}; exception A 
    │ = N.P.E}
  2 │ let x = 1
  3 │ 

  unused exception A

```

#### M6-7 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N = {exception E}; exception A = N.E}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:43-59

  1 │ module M: {} = {module N = {exception E}; exception A = N.E}
  2 │ 

  unused exception A

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:24-40

  1 │ module M: {} = {module N = {exception E}; exception A = N.E}
  2 │ 

  unused module N.


  Warning number 38
  Main.res:1:43-59

  1 │ module M: {} = {module N = {exception E}; exception A = N.E}
  2 │ 

  unused exception A

```

#### M6-8 — WITNESS

`Main.res`:

```rescript
module M: {exception A} = {module N = {exception E}; exception A = N.E}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1, TRACE M7-M8 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.N.E");

let M = {
  A: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.N.E");

let M = {
  A: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:35-51

  1 │ module M: {exception A} = {module N = {exception E}; exception A = N.E}
  2 │ 

  unused module N.

```

#### M6-9 — WITNESS

`Main.res`:

```rescript
module M: {exception A} = {module N = {exception E}; open N; exception A = E}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M6 x1, TRACE M7-M8 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.N.E");

let M = {
  A: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text
```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.N.E");

let M = {
  A: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 33
  Main.res:1:54-59

  1 │ module M: {exception A} = {module N = {exception E}; open N; exception A
    │  = E}
  2 │ 

  unused open N.

```

### M7 — WITNESS

Match an implementation extension constructor against an explicit interface or module signature (`extension_constructors`, `includemod.rs:4940`; `includecore.ml:711-740`), including an inner signature hidden by an outer one. Compare delayed unused-constructor warnings after inclusion, not just the inclusion result.

M7-1–5 agree and reach extension inclusion; M7-6–7 produce an extra Rust warning 38 at the inner signature declaration, while M7-8 uses the exported constructor and agrees. Smallest witness found: M7-7. The premise that Rust never marks the constructor is stale: lines 4950–4965 do mark it unless the coercion is implicit. The witness is an observable usage-mark discrepancy in this area, not proof that the implementation declaration lacks the mark; the warning location is the signature declaration.

#### Fixed

Fixed by `f64c72ed9`; see "S1 - an extension constructor declared in a
signature gets no unused warning" in "Third round: differences found while
fixing". All eight candidates agree after it.

#### M7-1 — outputs agree

`Main.resi`:

```rescript
exception E(int)
```

`Main.res`:

```rescript
exception E(int)
```

Trace counts from the separate instrumented invocations:

```text
Main.resi: TRACE M5 x60, TRACE M7-M8 x1
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.E");

exports.E = E;
/* No side effect */
```

stderr:

```text
```

#### M7-2 — outputs agree

`Main.res`:

```rescript
module M: {exception E(int)} = {exception E(int)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let M = {
  E: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text
```

#### M7-3 — outputs agree

`Main.res`:

```rescript
type t = ..
module M: {type t += E(int)} = {type t += E(int)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let M = {
  E: E
};

exports.M = M;
/* No side effect */
```

stderr:

```text
```

#### M7-4 — outputs agree

`Main.resi`:

```rescript
type t = ..
type t += E(int)
```

`Main.res`:

```rescript
type t = ..
type t += E(int)
```

Trace counts from the separate instrumented invocations:

```text
Main.resi: TRACE M5 x60, TRACE M7-M8 x1
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.E");

exports.E = E;
/* No side effect */
```

stderr:

```text
```

#### M7-5 — outputs agree

`Main.res`:

```rescript
module M: {exception E(int)} = {exception E(string)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:32-52

  1 │ module M: {exception E(int)} = {exception E(string)}
  2 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:1:33-51):
    type exn += E(string)
  
  Expected declaration (Main.res:1:12-27):
    type exn += E(int)

```

#### M7-6 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N: {exception E(int)} = {exception E(int)}}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:24-65

  1 │ module M: {} = {module N: {exception E(int)} = {exception E(int)}}
  2 │ 

  unused module N.

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:28-43

  1 │ module M: {} = {module N: {exception E(int)} = {exception E(int)}}
  2 │ 

  unused exception E


  Warning number 60
  Main.res:1:24-65

  1 │ module M: {} = {module N: {exception E(int)} = {exception E(int)}}
  2 │ 

  unused module N.

```

#### M7-7 — WITNESS

`Main.res`:

```rescript
module M: {} = {module N: {exception E} = {exception E}}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

OCaml, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 60
  Main.res:1:24-55

  1 │ module M: {} = {module N: {exception E} = {exception E}}
  2 │ 

  unused module N.

```

Rust, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 38
  Main.res:1:28-38

  1 │ module M: {} = {module N: {exception E} = {exception E}}
  2 │ 

  unused exception E


  Warning number 60
  Main.res:1:24-55

  1 │ module M: {} = {module N: {exception E} = {exception E}}
  2 │ 

  unused module N.

```

#### M7-8 — outputs agree

`Main.res`:

```rescript
module M: {} = {module N: {exception E} = {exception E}; let e = N.E}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {};

exports.M = M;
/* No side effect */
```

stderr:

```text

  Warning number 32
  Main.res:1:62

  1 │ module M: {} = {module N: {exception E} = {exception E}; let e = N.E}
  2 │ 

  unused value e.

```

### M8 — REACHED, NO DIFFERENCE SEEN

Include constructors of parameterized extensible types, with parameter-dependent argument types and explicit result types, through `extension_constructors` (`includemod.rs:4967-5034`; `includecore.ml:717-740`). Compare both successful alpha-renaming and rejected swapped parameters or incompatible results to expose a parameter-map error in equality.

M8-1–6 all reach extension inclusion and agree, including the interface file in M8-4, reversed parameter order in M8-3, and accepted/rejected explicit result types in M8-5–6.

#### M8-1 — outputs agree

`Main.res`:

```rescript
type t<'a> = ..
module M: {type t<'a> += E('a)} = {type t<'a> += E('a)}
let e = M.E(1)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let M = {
  E: E
};

let e = {
  RE_EXN_ID: E,
  _1: 1
};

exports.M = M;
exports.e = e;
/* No side effect */
```

stderr:

```text
```

#### M8-2 — outputs agree

`Main.res`:

```rescript
type t<'a, 'b> = ..
module M: {type t<'a, 'b> += E('a, 'b)} = {type t<'x, 'y> += E('x, 'y)}
let e = M.E(1, "x")
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let M = {
  E: E
};

let e = {
  RE_EXN_ID: E,
  _1: 1,
  _2: "x"
};

exports.M = M;
exports.e = e;
/* No side effect */
```

stderr:

```text
```

#### M8-3 — outputs agree

`Main.res`:

```rescript
type t<'a, 'b> = ..
module M: {type t<'a, 'b> += E('a, 'b)} = {type t<'x, 'y> += E('y, 'x)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:43-71

  1 │ type t<'a, 'b> = ..
  2 │ module M: {type t<'a, 'b> += E('a, 'b)} = {type t<'x, 'y> += E('y, 'x)}
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:2:62-70):
    type t<'x, 'y> += E('y, 'x)
  
  Expected declaration (Main.res:2:30-38):
    type t<'a, 'b> += E('a, 'b)

```

#### M8-4 — outputs agree

`Main.resi`:

```rescript
type t<'a, 'b> = ..
type t<'a, 'b> += E('b, 'a)
```

`Main.res`:

```rescript
type t<'x, 'y> = ..
type t<'x, 'y> += E('y, 'x)
```

Trace counts from the separate instrumented invocations:

```text
Main.resi: TRACE M5 x60, TRACE M7-M8 x1
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.resi, exit 0; stdout:

```text
```

stderr:

```text
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.E");

exports.E = E;
/* No side effect */
```

stderr:

```text
```

#### M8-5 — outputs agree

`Main.res`:

```rescript
type t<'a> = ..
module M: {type t<'a> += E: t<int>} = {type t<'a> += E: t<int>}
let e = M.E
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M7-M8 x1
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';

let Primitive_exceptions = require("@rescript/runtime/lib/js/Primitive_exceptions.cjs");

let E = /* @__PURE__ */Primitive_exceptions.create("Main.M.E");

let M = {
  E: E
};

let e = {
  RE_EXN_ID: E
};

exports.M = M;
exports.e = e;
/* No side effect */
```

stderr:

```text
```

#### M8-6 — outputs agree

`Main.res`:

```rescript
type t<'a> = ..
module M: {type t<'a> += E: t<int>} = {type t<'a> += E: t<string>}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M7-M8 x2
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:2:39-66

  1 │ type t<'a> = ..
  2 │ module M: {type t<'a> += E: t<int>} = {type t<'a> += E: t<string>}
  3 │ 

  Signature mismatch:
  
  Actual declaration (Main.res:2:54-65):
    type t<'a> += E: t<string>
  
  Expected declaration (Main.res:2:26-34):
    type t<'a> += E: t<int>

```

### M9 — REACHED, NO DIFFERENCE SEEN

Unify a package reached through a type abbreviation with another package listing more constraints at a nested level (`ctype.rs:9061-9102`, `unify_package:7905`; `ctype.ml:2416-2423`). Then generalize the function or retain a weak reference and use incompatible instantiations, checking whether constraint completion at the expanded-node level changes types or diagnostics.

M9-7–12 reach the package-unification arm and agree, including generalization in M9-9 and the weak-reference rejection in M9-12. M9-1–6 expose a constraint-translation obstacle: directly constraining a manifest component of S is rejected before the intended comparison; M9-5 also logs M9 during an earlier package operation. The repaired programs use a second module type T with abstract components and complete its constraints against the manifests in S. The marker proves the package arm, not that the two candidate node levels were numerically unequal.

#### M9-1 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: p<'a>): module(S with type t = int and type u = 'a) => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:21-63

  1 │ module type S = {type t = int; type u; let x: u}
  2 │ type p<'a> = module(S with type u = 'a)
  3 │ let f = (p: p<'a>): module(S with type t = int and type u = 'a) => p
  4 │ 

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:3:21-63):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-2 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: module(S with type t = int and type u = 'a)): p<'a> => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:13-55

  1 │ module type S = {type t = int; type u; let x: u}
  2 │ type p<'a> = module(S with type u = 'a)
  3 │ let f = (p: module(S with type t = int and type u = 'a)): p<'a> => p
  4 │ 

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:3:13-55):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-3 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = () => {let g = (p: p<'a>): module(S with type t = int and type u = 'a) => p; g}
let a = f()(module({type t = int; type u = int; let x = 1}: S with type u = int))
let b = f()(module({type t = int; type u = string; let x = "s"}: S with type u = string))
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:36-78

  1 │ module type S = {type t = int; type u; let x: u}
  2 │ type p<'a> = module(S with type u = 'a)
  3 │ let f = () => {let g = (p: p<'a>): module(S with type t = int and type u
    │  = 'a) => p; g}
  4 │ let a = f()(module({type t = int; type u = int; let x = 1}: S with type 
    │ u = int))
  5 │ let b = f()(module({type t = int; type u = string; let x = "s"}: S with 
    │ type u = string))

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:3:36-78):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-4 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: p<int>): module(S with type t = int and type u = string) => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:22-68

  1 │ module type S = {type t = int; type u; let x: u}
  2 │ type p<'a> = module(S with type u = 'a)
  3 │ let f = (p: p<int>): module(S with type t = int and type u = string) => 
    │ p
  4 │ 

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:3:22-68):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-5 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
type q<'a> = p<'a>
let f = (p: q<'a>) => {let g = () => (p: module(S with type t = int and type u = 'a)); g()}
let use = (p: q<int>): q<string> => f(p)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M9 x2
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:4:42-84

  2 │ type p<'a> = module(S with type u = 'a)
  3 │ type q<'a> = p<'a>
  4 │ let f = (p: q<'a>) => {let g = () => (p: module(S with type t = int and 
    │ type u = 'a)); g()}
  5 │ let use = (p: q<int>): q<string> => f(p)
  6 │ 

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:4:42-84):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-6 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let make = () => {let r = ref(None); let f = (p: p<'a>) => {r := Some(p); (p: module(S with type t = int and type u = 'a))}; f}
let f = make()
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:3:79-121

  1 │ module type S = {type t = int; type u; let x: u}
  2 │ type p<'a> = module(S with type u = 'a)
  3 │ let make = () => {let r = ref(None); let f = (p: p<'a>) => {r := Some(p)
    │ ; (p: module(S with type t = int and type u = 'a))}; f}
  4 │ let f = make()
  5 │ 

  In this `with' constraint, the new definition of t
  does not match its original definition in the constrained signature:
  
  Actual declaration (Main.res:3:79-121):
    type t
  
  Expected declaration (Main.res:1:18-29):
    type t = int

```

#### M9-7 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: p<'a>): module(T with type t = int and type u = 'a) => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M9 x2
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(p) {
  return p;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### M9-8 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: module(T with type t = int and type u = 'a)): p<'a> => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M9 x2
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(p) {
  return p;
}

exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### M9-9 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = () => {let g = (p: p<'a>): module(T with type t = int and type u = 'a) => p; g}
let a = f()(module({type t = int; type u = int; let x = 1}: S with type u = int))
let b = f()(module({type t = int; type u = string; let x = "s"}: S with type u = string))
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60, TRACE M9 x8
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f() {
  return p => p;
}

let a = {
  x: 1
};

let b = {
  x: "s"
};

exports.f = f;
exports.a = a;
exports.b = b;
/* No side effect */
```

stderr:

```text
```

#### M9-10 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let f = (p: p<int>): module(T with type t = int and type u = string) => p
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M9 x3
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:4:73

  2 │ module type T = {type t; type u; let x: u}
  3 │ type p<'a> = module(S with type u = 'a)
  4 │ let f = (p: p<int>): module(T with type t = int and type u = string) => 
    │ p
  5 │ 

  This has type: [1;31mp<int>[0m [2m(defined as[0m [1;31mmodule(S with type u = int)[0m[2m)[0m
  But it's expected to have type:
    [1;33mmodule(T with type t = int and type u = string)[0m
  
  The incompatible parts:
    [1;31mint[0m vs [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M9-11 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
type q<'a> = p<'a>
let f = (p: q<'a>) => {let g = () => (p: module(T with type t = int and type u = 'a)); g()}
let use = (p: q<int>): q<string> => f(p)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M5 x60, TRACE M9 x11
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:6:37-40

  4 │ type q<'a> = p<'a>
  5 │ let f = (p: q<'a>) => {let g = () => (p: module(T with type t = int and 
    │ type u = 'a)); g()}
  6 │ let use = (p: q<int>): q<string> => f(p)
  7 │ 

  This has type: [1;31mmodule(T with type t = int and type u = int)[0m
  But it's expected to have type:
    [1;33mq<string>[0m [2m(defined as[0m [1;33mmodule(S with type u = string)[0m[2m)[0m
  
  The incompatible parts:
    [1;31mint[0m vs [1;33mstring[0m
  
  You can convert [1;33mint[0m to [1;33mstring[0m with [1;33mInt.toString[0m.

```

#### M9-12 — outputs agree

`Main.res`:

```rescript
module type S = {type t = int; type u; let x: u}
module type T = {type t; type u; let x: u}
type p<'a> = module(S with type u = 'a)
let make = () => {let r = ref(None); let f = (p: p<'a>) => {r := Some(p); (p: module(T with type t = int and type u = 'a))}; f}
let f = make()
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M5 x60, TRACE M9 x4
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:5:5

  3 │ type p<'a> = module(S with type u = 'a)
  4 │ let make = () => {let r = ref(None); let f = (p: p<'a>) => {r := Some(p)
    │ ; (p: module(T with type t = int and type u = 'a))}; f}
  5 │ let f = make()
  6 │ 

  This expression's type contains type variables that cannot be generalized:
  [1;31mp<'_weak1> => module(T with type t = int and type u = '_weak1)[0m
  
  This happens when the type system senses there's a mutation/side-effect,
  in combination with a polymorphic value.
  [1;33mUsing or annotating that value usually solves it.[0m

```

### M10 — REACHED, NO DIFFERENCE SEEN

Compile a unit without an interface or explicitly bound polymorphic field, allowing weak variables, late row closing, private rows, recursive modules or functor results to reach the inferred-signature check (`driver.rs:7395`, `includemod.rs:2212`; `typemod.ml:1812-1815`). Check whether OCaml rejects at self-inclusion while Rust takes the shortcut, separating that from the subsequent non-generalizable-type check.

M10-1–6 agree; M10-1–3 and M10-5 take the shortcut, while M10-4 and M10-6 take the full check despite having no explicit polymorphic field. The proposed “only with bound variables” condition omits `!includes_itself_plainly(simple_sig)` at includemod.rs:2218. M10-1 is rejected by both for a non-generalizable type, not as an inferred-signature mismatch. No candidate produced the requested OCaml self-inclusion rejection.

#### M10-1 — outputs agree

`Main.res`:

```rescript
module M = {let r = ref(None)}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x2, TRACE M10-shortcut x2, TRACE M5 x60
```

Both compilers, Main.res, exit 2; stdout:

```text
```

stderr:

```text

  We've found a bug for you!
  Main.res:1:8-30

  1 │ module M = {let r = ref(None)}
  2 │ 

  The type of this module contains type variables that cannot be generalized:
  [1;31m{
    let r: ref<option<'_weak1>>
  }[0m
  
  This happens when the type system senses there's a mutation/side-effect,
  in combination with a polymorphic value.
  [1;33mUsing or annotating that value usually solves it.[0m

```

#### M10-2 — outputs agree

`Main.res`:

```rescript
module M = {let r = ref(None)}
let set = () => M.r := Some(1)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let r = {
  contents: undefined
};

let M = {
  r: r
};

function set() {
  r.contents = 1;
}

exports.M = M;
exports.set = set;
/* No side effect */
```

stderr:

```text
```

#### M10-3 — outputs agree

`Main.res`:

```rescript
module M = {let f = x => switch x {| #A(y) => y | #B => 0}}
let f: [#A(int) | #B] => int = M.f
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  if (typeof x === "object") {
    return x.VAL;
  } else {
    return 0;
  }
}

let M = {
  f: f
};

exports.M = M;
exports.f = f;
/* No side effect */
```

stderr:

```text
```

#### M10-4 — outputs agree

`Main.res`:

```rescript
module M: {type t = private [> #A]; let x: t} = {type t = [#A]; let x = #A}
let x = M.x
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let M = {
  x: "A"
};

let x = "A";

exports.M = M;
exports.x = x;
/* No side effect */
```

stderr:

```text
```

#### M10-5 — outputs agree

`Main.res`:

```rescript
module rec A: {type t = B.t; let f: t => t} = {type t = B.t; let f = x => B.f(x)}
and B: {type t = int; let f: t => t} = {type t = int; let f = x => x}
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x;
}

let B = {
  f: f
};

function f$1(x) {
  return x;
}

let A = {
  f: f$1
};

exports.A = A;
exports.B = B;
/* No side effect */
```

stderr:

```text
```

#### M10-6 — outputs agree

`Main.res`:

```rescript
module F = (X: {}) => {let r = ref(None)}
module M = F({})
let set = () => M.r := Some(1)
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M1 x1, TRACE M10-entry x1, TRACE M10-full x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let r = {
    contents: undefined
  };
  return {
    r: r
  };
}

let r = {
  contents: undefined
};

let M = {
  r: r
};

function set() {
  r.contents = 1;
}

exports.F = F;
exports.M = M;
exports.set = set;
/* No side effect */
```

stderr:

```text
```

### Control

#### Control-1 — outputs agree

`Main.res`:

```rescript
let x = 1
```

Trace counts from the separate instrumented invocations:

```text
Main.res: TRACE M10-entry x1, TRACE M10-shortcut x1, TRACE M5 x60
```

Both compilers, Main.res, exit 0; stdout:

```text
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let x = 1;

exports.x = x;
/* No side effect */
```

stderr:

```text
```

### No reference and setup failures

M2-8, M3-10 and M5-8 stop in OCaml with `Failure` from ext_path.ml:122 because `-bs-package-output` requires `-bs-project-root`. Their full programs and both outputs are above; none is a reference-backed witness.

The remaining dependency setup attempts expose different inputs to the compilers, not an attributable checker departure: plain -I directories do not build a Rust dependency registry; script-mode OCaml requires Lib.js; a dependency without an explicit CommonJS output does not supply the requested Rust import mode; finally, root Lib artifacts shadow the dependency package only for the file-based compiler. The last problem gives `./Lib.js` versus `probe-dependency/Lib.js`, and disappears when both compilers read the same dependency. M2-9, M3-16 and M5-11 are the repaired comparisons. Generated-file text is recorded only for successful commands; a failed invocation cannot establish that a pre-existing JavaScript file is its output.

### Found on the way

No additional reference-backed compiler difference outside M6/M7 was established. Syntax failures, incompatible package setup and the three no-reference OCaml failures are retained above instead of misclassified as witnesses. M7’s signature-location warning needs its own causal investigation; this search does not claim that the existing implementation-side mark is absent.

### Gates and limits

The OCaml build, fresh-target thin-LTO Rust release build, runtime reference build and named fixture parity calibration passed. All candidate invocations are recorded above; no whole compiler test suite was run, no manifest was touched, and no compiler/test/fixture source changed. The permitted single successful release build contains disabled-by-default reachability markers; this is not a release-performance comparison. No two-binary application benchmark or signature comparison was run: this documentation-only task provides no changed compiler candidate, and the permitted build budget was used for the witness-search executable. CI is a separate publication gate; its result is reported on the pull request rather than asserted here.

## Fifth round: patterns, equations and compatibility

### Summary

| Place | Verdict | Number of candidates | Witness name |
| --- | --- | ---: | --- |
| G1 | REACHED, NO DIFFERENCE SEEN | 16 | — |
| G2 | REACHED, NO DIFFERENCE SEEN | 8 | — |
| G3 | WITNESS | 8 | row-closed; row-disjoint |
| G4 | REACHED, NO DIFFERENCE SEEN | 8 | — |
| G5 | REACHED, NO DIFFERENCE SEEN | 8 | — |
| G6 | WITNESS | 8 | abstract-index |
| G7 | REACHED, NO DIFFERENCE SEEN | 11 | — |
| G8 | REACHED, NO DIFFERENCE SEEN | 16 | — |
| G9 | REACHED, NO DIFFERENCE SEEN | 8 | — |
| G10 | REACHED, NO DIFFERENCE SEEN | 16 | — |

### Scope, calibration and reproducibility

Both compilers are from `5fd5b73eb2`. This is a search, not a proof of
unification equivalence: REACHED certifies the operations specified below,
not every arm or every state precondition in the inventory. There are 107
numbered candidates, all parsed, plus the explicitly listed reduction trials.
No compiler source was changed, including for tracing. No OCaml internal
error was observed. No additional unrelated departure was found on the way.

The existing third-round examples and fourth-round summary informed the
module-abstraction and diagnostic probes. Syntax was checked against
`gadt_rec_missing.res`, `warning_62_constraint_on_gadt.res`,
`gadt_partial_match_failure_test.res`, `gadt_refined_option_pattern_test.res`
and `gadt_test.res` before writing the candidates.

Build commands (one heavy build at a time):

```sh
export PATH="$HOME/.cargo/bin:$PATH"
CARGO_PROFILE_RELEASE_LTO=thin cargo build --release --manifest-path rewatch/Cargo.toml
eval $(opam env)
dune build --root .
scripts/rust_compiler_shims.sh release
RESCRIPT_RUNTIME="$PWD/packages/@rescript/runtime" \
  rewatch/target/release/rescript build-reference \
  --bsc "$PWD/_build/install/default/bin/bsc" packages/@rescript/runtime
```

Rust finished successfully, with the existing unused `console::style` import
warning in rewatch. Dune exited 0 without output. Runtime preparation printed:

```text
OCaml reference build: 113 of 113 modules built
```

Each candidate has a fresh directory under `${TMPDIR:-/tmp}`, containing the
pasted `Main.res`, an empty `src/` directory, and this `rescript.json`:

```json
{"name":"pattern-search","sources":["."]}
```

With `ROOT` the checkout's absolute path and the working directory the
candidate's project, every candidate uses the fixture commands from
`scripts/test_error_output_parity.sh`, independently:

```sh
timeout 10 "$ROOT/_build/install/default/bin/bsc" -w +A -bs-jsx 4 -color never Main.res >ocaml.stdout 2>ocaml.stderr
timeout 10 "$ROOT/rewatch/target/release/bsc" -w +A -bs-jsx 4 -color never Main.res >rust.stdout 2>rust.stderr
```

Exit status and complete stderr are compared. With these flags generated
JavaScript is stdout, not a file under `src/`: accepted candidates compare
stdout after removing blank lines. All pasted outputs are complete, with
terminal SGR escapes stripped (`sed 's/\x1b\[[0-9;]*m//g'`); empty streams
are empty fences, not omitted output. Candidate runs are not debugger runs.

Calibration is `tests/build_tests/super_errors/fixtures/warning_62_constraint_on_gadt.res`
copied to `Main.res`. Both exit 2, with empty stdout and identical stderr:

```rescript
type rec t<'a> =
  | Int(int): t<int>
  | Bool(bool): t<bool> constraint 'a = int
```

```text

  Warning number 62
  Main.res:3:25-43

  1 │ type rec t<'a> =
  2 │   | Int(int): t<int>
  3 │   | Bool(bool): t<bool> constraint 'a = int
  4 │ 

  Type constraints do not apply to GADT cases of variant types.


  We've found a bug for you!
  Main.res:3:17-23

  1 │ type rec t<'a> =
  2 │   | Int(int): t<int>
  3 │   | Bool(bool): t<bool> constraint 'a = int
  4 │ 

  Constraints are not satisfied in this type.
  Type t<bool> should be an instance of t<int>

```


The fixture itself was also run with the parity script:

```sh
PARITY_JOBS=1 scripts/test_error_output_parity.sh --release --compiler-only warning_62_constraint_on_gadt
```

```text
Compiler diagnostics parity

Error output parity summary
  total:  1
  pass:   1
  fail:   0
```

### Reachability method

GDB breakpoints use the release executable's symbol table; no rebuild or
instrumentation patch is involved. The debugger counts function entries,
classifying a hit as `:gadt` only if its current stack contains
`unify_pattern_types_gadt`, otherwise `:other`. `:other` alone is not a proof
of Expression mode. Error runs can execute a second diagnostic attempt;
counts include it. A missing key means zero hits. The following script was
used as `trace.py` in separate invocations (it writes only scratch files):

```python
import gdb,json,collections,os
counts=collections.Counter()
class Probe(gdb.Breakpoint):
 def __init__(self,symbol,label):
  super().__init__(symbol,internal=True);self.label=label
 def stop(self):
  f=gdb.newest_frame();gadt=False
  while f:
   if 'unify_pattern_types_gadt' in (f.name() or ''):gadt=True
   f=f.older()
  counts[self.label+(':gadt' if gadt else ':other')]+=1
  return False
for symbol,label in [('unify','unify'),('unify_types::{closure#3}','arrow'),('unify_types::{closure#4}','tuple'),('unify_rows','rows'),('is_instantiable','instantiable'),('add_gadt_equation','equation'),('unify_same_path_constructor_args','same_path'),('occur_check','occur'),('mcomp_rec','mcomp'),('mcomp_enter_poly','mcomp_poly')]:
 try:Probe('rescript_compiler::types::ctype::'+symbol,label)
 except Exception as e: print('PROBE ERROR',label,str(e))
Probe('rescript_compiler::types::typecore::unify_pattern_types_gadt','gadt')
Probe("*'rescript_compiler::types::ctype::unify'+426",'pair_lookup')
Probe("*'rescript_compiler::types::ctype::unify'+551",'pair_compare')
Probe("*'rescript_compiler::types::ctype::occur_check'+177",'occur_shortcut')
gdb.execute('run',to_string=True)
open('trace.json','w').write(json.dumps(dict(counts),sort_keys=True))
print('TRACE',json.dumps(dict(counts),sort_keys=True))
```

```sh
timeout 15 gdb -q -batch -ex 'set pagination off' -x "$TRACE_SCRIPT" \
  --args "$ROOT/rewatch/target/release/rescript" bsc \
  -w +A -bs-jsx 4 -color never Main.res
```

The three instruction-offset probes are specific to this thin-LTO build.
They were identified with `disassemble 'rescript_compiler::types::ctype::unify'`
and `disassemble 'rescript_compiler::types::ctype::occur_check'`:
`unify+426` tests the pair-table size after ruling out identical representatives;
`unify+551` branches after comparing the stored key; `occur_check+177` is the
successful shortcut return after testing the cheap walk's result. The pair
comparison probe does not claim that the comparison succeeded.

### G1 — REACHED, NO DIFFERENCE SEEN

Unify two structural indices of `Refl` under locally abstract binders so that Pattern mode enters the arrow, tuple, row or object arm of `unify_types` (Rust ctype.rs:8660–9105; OCaml ctype.ml:2328–2424). Check the branch body both when it uses the resulting equality and when it demands an incompatible `int`, including the type names in that error.

G1-1/6 hit the arrow closure, G1-2/5 the tuple closure, and G1-3/7 row unification under `unify_pattern_types_gadt`; all agree. G1-9–16 are controls with a structural index against one abstract index: they add an equation, but do not establish that the structural-vs-structural arm ran. Object cases are included, but no separate object-arm breakpoint was installed. Nil, package and polymorphic-type arms are not individually certified by this set.

#### G1-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a => a, b => b>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:gadt": 1, "arrow:other": 7, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:gadt": 1, "occur:other": 21, "occur_shortcut:gadt": 1, "occur_shortcut:other": 21, "pair_compare:other": 1, "pair_lookup:gadt": 5, "pair_lookup:other": 53, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 5, "unify:other": 57}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G1-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<(a, a), (b, b)>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:gadt": 1, "occur:other": 21, "occur_shortcut:gadt": 1, "occur_shortcut:other": 21, "pair_compare:other": 1, "pair_lookup:gadt": 5, "pair_lookup:other": 53, "same_path:gadt": 2, "same_path:other": 4, "tuple:gadt": 1, "tuple:other": 4, "unify:gadt": 5, "unify:other": 57}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G1-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<[#a(a)], [#a(b)]>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 21, "occur_shortcut:other": 21, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 49, "rows:gadt": 1, "rows:other": 4, "same_path:gadt": 1, "same_path:other": 4, "unify:gadt": 4, "unify:other": 51}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G1-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<{"x": a}, {"x": b}>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 25, "occur_shortcut:other": 25, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 57, "same_path:gadt": 1, "same_path:other": 4, "unify:gadt": 7, "unify:other": 63}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G1-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<(a, a), (b, b)>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:gadt": 2, "occur:other": 22, "occur_shortcut:gadt": 2, "occur_shortcut:other": 22, "pair_lookup:gadt": 10, "pair_lookup:other": 68, "same_path:gadt": 4, "same_path:other": 2, "tuple:gadt": 2, "unify:gadt": 10, "unify:other": 68}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:82

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<(a, a), (b, b)>, b) => int = (e, v) => switch e { |
    │  Refl => v }
  3 │ 

  This has type: b (defined as a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a => a, b => b>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:gadt": 2, "arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:gadt": 2, "occur:other": 22, "occur_shortcut:gadt": 2, "occur_shortcut:other": 22, "pair_lookup:gadt": 10, "pair_lookup:other": 68, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 10, "unify:other": 68}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:82

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a => a, b => b>, b) => int = (e, v) => switch e { |
    │  Refl => v }
  3 │ 

  This has type: b (defined as a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<[#a(a)], [#a(b)]>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 8, "pair_lookup:other": 64, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 8, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:84

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<[#a(a)], [#a(b)]>, b) => int = (e, v) => switch e {
    │  | Refl => v }
  3 │ 

  This has type: b (defined as a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<{"x": a}, {"x": b}>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:gadt": 2, "pair_lookup:gadt": 12, "pair_lookup:other": 64, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 14, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:86

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<{"x": a}, {"x": b}>, b) => int = (e, v) => switch e
    │  { | Refl => v }
  3 │ 

  This has type: b (defined as a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-9 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a => a, b>, a) => b = (e, v) => switch e { | Refl => y => y }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 7, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 23, "occur_shortcut:other": 23, "pair_compare:other": 3, "pair_lookup:gadt": 3, "pair_lookup:other": 55, "same_path:gadt": 1, "same_path:other": 3, "unify:gadt": 3, "unify:other": 58}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:48

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a => a, b>, a) => b = (e, v) => switch e { | Refl =
    │ > y => y }

  unused variable v.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_v`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return y => y;
}

exports.f = f;
/* No side effect */
```

#### G1-10 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<(a, a), b>, a) => b = (e, v) => switch e { | Refl => (v, v) }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 19, "occur_shortcut:other": 19, "pair_compare:other": 2, "pair_lookup:gadt": 3, "pair_lookup:other": 53, "same_path:gadt": 1, "same_path:other": 3, "tuple:other": 3, "unify:gadt": 3, "unify:other": 56}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return [
    v,
    v
  ];
}

exports.f = f;
/* No side effect */
```

#### G1-11 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<[#a(a)], b>, a) => b = (e, v) => switch e { | Refl => #a(v) }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 18, "occur_shortcut:other": 18, "pair_compare:other": 1, "pair_lookup:gadt": 3, "pair_lookup:other": 47, "rows:other": 2, "same_path:gadt": 1, "same_path:other": 3, "unify:gadt": 3, "unify:other": 50}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return {
    NAME: "a",
    VAL: v
  };
}

exports.f = f;
/* No side effect */
```

#### G1-12 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<{"x": a}, b>, a) => b = (e, v) => switch e { | Refl => {"x": v} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:other": 3, "pair_lookup:gadt": 3, "pair_lookup:other": 54, "same_path:gadt": 1, "same_path:other": 3, "unify:gadt": 3, "unify:other": 59}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return {
    x: v
  };
}

exports.f = f;
/* No side effect */
```

#### G1-13 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<(a, a), b>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:gadt": 1, "pair_lookup:gadt": 6, "pair_lookup:other": 66, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 66}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:77

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<(a, a), b>, b) => int = (e, v) => switch e { | Refl
    │  => v }

  This has type: b (defined as (a, a))
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-14 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a => a, b>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:gadt": 1, "pair_lookup:gadt": 6, "pair_lookup:other": 67, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 67}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:77

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a => a, b>, b) => int = (e, v) => switch e { | Refl
    │  => v }

  This has type: b (defined as a => a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-15 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<[#a(a)], b>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 6, "pair_lookup:other": 64, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:78

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<[#a(a)], b>, b) => int = (e, v) => switch e { | Ref
    │ l => v }

  This has type: b
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G1-16 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<{"x": a}, b>, b) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 6, "pair_lookup:other": 64, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:79

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<{"x": a}, b>, b) => int = (e, v) => switch e { | Re
    │ fl => v }

  This has type: b
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

### G2 — REACHED, NO DIFFERENCE SEEN

Use a pattern equality again in an expression annotation, a nested match or a let pattern to exercise `unify` in both contexts (Rust ctype.rs:7978–7987; OCaml ctype.ml:2205–2214). Check that repeated annotations still bind or reject the expression rather than accepting a stale assumed pair.

All eight reach the pair-table lookup both under GADT unification and outside it; the traces report `pair_lookup`. `pair_compare` is a hash-key comparison, not proof of an equal-key hit or of a pair surviving from Pattern into Expression mode. These programs establish execution of the differing lookup code, not a stale-pair lifetime counterexample.

#### G2-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 17, "occur_shortcut:other": 17, "pair_compare:other": 4, "pair_lookup:gadt": 3, "pair_lookup:other": 45, "same_path:gadt": 1, "same_path:other": 4, "unify:gadt": 3, "unify:other": 47}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G2-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => {let z: b = v; z} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 17, "occur_shortcut:other": 17, "pair_compare:other": 2, "pair_lookup:gadt": 3, "pair_lookup:other": 48, "same_path:gadt": 1, "same_path:other": 4, "unify:gadt": 3, "unify:other": 50}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G2-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => {let z: b = v; let bad: int = z; bad} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 26, "occur_shortcut:other": 26, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 73, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 73}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:100

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => {le
    │ t z: b = v; let bad: int = z; bad} }
  3 │ 

  This has type: b (defined as a)
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### G2-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => {let z: b = v; let bad: string = z; bad} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 26, "occur_shortcut:other": 26, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 73, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 73}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:103

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a, b>, a) => b = (e, v) => switch e { | Refl => {le
    │ t z: b = v; let bad: string = z; bad} }
  3 │ 

  This has type: b (defined as a)
  But it's expected to have type: string

```

stdout (empty):

```text
```

#### G2-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, b) => a = (e, v) => switch e { | Refl => switch e { | Refl => v } }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:gadt": 1, "occur:other": 17, "occur_shortcut:gadt": 1, "occur_shortcut:other": 17, "pair_compare:other": 3, "pair_lookup:gadt": 6, "pair_lookup:other": 49, "same_path:gadt": 3, "same_path:other": 4, "unify:gadt": 6, "unify:other": 51}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G2-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, b) => a = (e, v) => switch e { | Refl => {let Refl = e; v} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:gadt": 1, "occur:other": 17, "occur_shortcut:gadt": 1, "occur_shortcut:other": 17, "pair_compare:other": 3, "pair_lookup:gadt": 6, "pair_lookup:other": 49, "same_path:gadt": 3, "same_path:other": 4, "unify:gadt": 6, "unify:other": 51}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G2-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, b) => a = (e, v) => switch e { | Refl => {let z: a = v; z} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 17, "occur_shortcut:other": 17, "pair_compare:other": 2, "pair_lookup:gadt": 3, "pair_lookup:other": 48, "same_path:gadt": 1, "same_path:other": 4, "unify:gadt": 3, "unify:other": 50}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G2-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<a, b>, b) => a = (e, v) => switch e { | Refl => {let z: a = v; z + 1} }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 69, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 69}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:85

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<a, b>, b) => a = (e, v) => switch e { | Refl => {le
    │ t z: a = v; z + 1} }
  3 │ 

  This has type: a
  But it's expected to have type: int

```

stdout (empty):

```text
```

### G3 — WITNESS

Match a result-indexed constructor whose polymorphic-variant row clashes with the scrutinee index, reaching Rust `unify_rows` in Pattern mode (ctype.rs:9019–9025) and OCaml’s recovery arm (ctype.ml:2400–2411). Compare the entire trace-derived error after the row clash, not just the accept/reject result.

#### Fixed

Fixed by `b22d458c9`; see "P2 - a row clash in a pattern is retried as
OCaml retries it" in "Third round: differences found while fixing". All
eight candidates agree after it.

G3-1–4 and G3-7 differ; G3-5/6/8 agree. All eight hit `rows:gadt`. The two reduced witnesses below distinguish a missing closed-row tag from disjoint rows. Rust preserves extra row-detail advice where the OCaml recovery/reification/compatibility path emits only the outer mismatch; both reject.

#### G3-1 — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]> | B: t<[#b]>
let f = (x: t<[#a | #b]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 4, "pair_lookup:other": 40, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 4, "unify:other": 42}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:43

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[#a | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#a | #b]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:43

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[#a | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#a | #b]>
  
  The first polymorphic variant is closed and doesn't include the constructor: #b.
  
  Possible solutions:
  - Either make the first variant open so it can accept additional constructors. To do this, make sure the type starts with [> instead of [
  - Or add the missing constructor to it.

```

stdout (empty):

```text
```

#### G3-2 — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]> | B: t<[#b]>
let f = (x: t<[> #a]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 4, "occur:other": 10, "occur_shortcut:other": 10, "pair_compare:other": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 40, "rows:gadt": 4, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 8, "unify:other": 42}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:49

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[> #a]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:49

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[> #a]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>
  
  These polymorphic variants are incompatible - they share no common constructors.

```

stdout (empty):

```text
```

#### G3-3 — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]> | B: t<[#b]>
let f = (x: t<[< #a | #b]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 4, "occur:other": 10, "occur_shortcut:other": 10, "pair_compare:other": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 40, "rows:gadt": 4, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 8, "unify:other": 42}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:54

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[< #a | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:54

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[< #a | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>
  
  These polymorphic variants are incompatible - they share no common constructors.

```

stdout (empty):

```text
```

#### G3-4 — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]> | B: t<[#b]>
let f = (x: t<[#a]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 4, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 8, "pair_lookup:other": 40, "rows:gadt": 4, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 8, "unify:other": 42}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:47

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[#a]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:47

  1 │ type rec t<_> = A: t<[#a]> | B: t<[#b]>
  2 │ let f = (x: t<[#a]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#b]>
  but a pattern was expected which matches values of type t<[#a]>
  
  These polymorphic variants are incompatible - they share no common constructors.

```

stdout (empty):

```text
```

#### G3-5 — outputs agree

`Main.res`:

```rescript
type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
let f = (x: t<[#a(int)]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 4, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 12, "pair_lookup:other": 54, "rows:gadt": 4, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 12, "unify:other": 56}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:52

  1 │ type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
  2 │ let f = (x: t<[#a(int)]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a(string)]>
  but a pattern was expected which matches values of type t<[#a(int)]>
  
  Both polymorphic variants have the constructor #a, but their payload types are incompatible.
  Make sure the payload types for #a match exactly in both polymorphic variants.

```

stdout (empty):

```text
```

#### G3-6 — outputs agree

`Main.res`:

```rescript
type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
let f = (x: t<[#a(string)]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 6, "pair_lookup:other": 54, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 56}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:46

  1 │ type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
  2 │ let f = (x: t<[#a(string)]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a(int)]>
  but a pattern was expected which matches values of type t<[#a(string)]>
  
  Both polymorphic variants have the constructor #a, but their payload types are incompatible.
  Make sure the payload types for #a match exactly in both polymorphic variants.

```

stdout (empty):

```text
```

#### G3-7 — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
let f = (x: t<[#a(int) | #b]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 4, "pair_lookup:other": 54, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 4, "unify:other": 56}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:48

  1 │ type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
  2 │ let f = (x: t<[#a(int) | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a(int)]>
  but a pattern was expected which matches values of type t<[#a(int) | #b]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:48

  1 │ type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
  2 │ let f = (x: t<[#a(int) | #b]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a(int)]>
  but a pattern was expected which matches values of type t<[#a(int) | #b]>
  
  The first polymorphic variant is closed and doesn't include the constructor: #b.
  
  Possible solutions:
  - Either make the first variant open so it can accept additional constructors. To do this, make sure the type starts with [> instead of [
  - Or add the missing constructor to it.

```

stdout (empty):

```text
```

#### G3-8 — outputs agree

`Main.res`:

```rescript
type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
let f = (x: t<[> #a(int)]>) => switch x { | A => 0 | B => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 4, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_compare:gadt": 4, "pair_lookup:gadt": 12, "pair_lookup:other": 54, "rows:gadt": 4, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 12, "unify:other": 56}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:54

  1 │ type rec t<_> = A: t<[#a(int)]> | B: t<[#a(string)]>
  2 │ let f = (x: t<[> #a(int)]>) => switch x { | A => 0 | B => 1 }
  3 │ 

  This pattern matches values of type t<[#a(string)]>
  but a pattern was expected which matches values of type t<[#a(int)]>
  
  Both polymorphic variants have the constructor #a, but their payload types are incompatible.
  Make sure the payload types for #a match exactly in both polymorphic variants.

```

stdout (empty):

```text
```

#### Reduced witnesses and reduction evidence

Removing the other constructor and the other match branch preserves the mismatch. Removing the payload in G3-7 yields row-closed; closing the row and removing the first case in G3-2–4 yields row-disjoint. Removing the scrutinee index or replacing the indexed constructor with a direct row pattern eliminates the discrepancy (controls below). Rust is at fault relative to the reference: its Pattern row-clash diagnostic retains advice that OCaml’s recovery path drops.

#### row-closed — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]>
let f = (x: t<[#a | #b]>) => switch x { | A => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 6, "occur_shortcut:other": 6, "pair_lookup:gadt": 4, "pair_lookup:other": 28, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 30}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:43

  1 │ type rec t<_> = A: t<[#a]>
  2 │ let f = (x: t<[#a | #b]>) => switch x { | A => 0 }

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#a | #b]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:43

  1 │ type rec t<_> = A: t<[#a]>
  2 │ let f = (x: t<[#a | #b]>) => switch x { | A => 0 }

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#a | #b]>
  
  The first polymorphic variant is closed and doesn't include the constructor: #b.
  
  Possible solutions:
  - Either make the first variant open so it can accept additional constructors. To do this, make sure the type starts with [> instead of [
  - Or add the missing constructor to it.

```

stdout (empty):

```text
```

#### row-disjoint — outputs differ

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]>
let f = (x: t<[#b]>) => switch x { | A => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 6, "occur_shortcut:other": 6, "pair_lookup:gadt": 4, "pair_lookup:other": 28, "rows:gadt": 2, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 30}
```

Ocaml, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec t<_> = A: t<[#a]>
  2 │ let f = (x: t<[#b]>) => switch x { | A => 0 }

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#b]>

```

stdout (empty):

```text
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec t<_> = A: t<[#a]>
  2 │ let f = (x: t<[#b]>) => switch x { | A => 0 }

  This pattern matches values of type t<[#a]>
  but a pattern was expected which matches values of type t<[#b]>
  
  These polymorphic variants are incompatible - they share no common constructors.

```

stdout (empty):

```text
```

#### row-no-index — outputs agree

`Main.res`:

```rescript
type rec t<_> = A: t<[#a]>
let f = x => switch x { | A => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "occur:other": 2, "occur_shortcut:other": 2, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 1, "pair_lookup:other": 12, "same_path:other": 1, "unify:gadt": 1, "unify:other": 13}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return 0;
}

exports.f = f;
/* No side effect */
```

#### row-direct — outputs agree

`Main.res`:

```rescript
let f = (x: [#b]) => switch x { | #a => 0 }
```

Debugger counts (separate invocation):

```json
{"occur:other": 2, "occur_shortcut:other": 2, "pair_compare:other": 2, "pair_lookup:other": 14, "rows:other": 2, "unify:other": 16}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:1:35-36

  1 │ let f = (x: [#b]) => switch x { | #a => 0 }

  This pattern matches values of type [? #a]
  but a pattern was expected which matches values of type [#b]
  
  The second polymorphic variant is closed and doesn't include the constructor: #a.
  
  Possible solutions:
  - Either make the second variant open so it can accept additional constructors. To do this, make sure the type starts with [> instead of [
  - Or add the missing constructor to it.

```

stdout (empty):

```text
```

### G4 — REACHED, NO DIFFERENCE SEEN

Match equality witnesses with two indices having the same parameterized constructor path, including an alias and a recursive datatype (Rust ctype.rs:8932–8955; OCaml ctype.ml:2328–2374). Check argument clashes and the exposed abbreviation spelling after the body asks for an incompatible result.

All eight hit `same_path:gadt` and agree. Correction to the proposed premise: in Pattern mode OCaml adds an equality instead of linking, and the Rust same-path arm also explicitly skips its final link in Pattern mode. The link-order departure is in Expression mode; these programs additionally execute same-path expression calls, but establish no order-sensitive witness.

#### G4-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<option<a>, option<b>>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 25, "occur_shortcut:other": 25, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 57, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 4, "unify:other": 59}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G4-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<option<a>, option<b>>, a) => b = (e, v) => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 30, "occur_shortcut:other": 30, "pair_compare:gadt": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 78, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 8, "unify:other": 78}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:86

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<option<a>, option<b>>, a) => b = (e, v) => switch e
    │  { | Refl => 0 }
  3 │ 

  This has type: int
  But this switch is expected to return: b (defined as a)

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G4-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<array<a>, array<b>>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 25, "occur_shortcut:other": 25, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 57, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 4, "unify:other": 59}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G4-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<array<a>, array<b>>, a) => b = (e, v) => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 30, "occur_shortcut:other": 30, "pair_compare:gadt": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 78, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 8, "unify:other": 78}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:84

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<array<a>, array<b>>, a) => b = (e, v) => switch e {
    │  | Refl => 0 }
  3 │ 

  This has type: int
  But this switch is expected to return: b (defined as a)

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G4-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<list<a>, list<b>>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:other": 25, "occur_shortcut:other": 25, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 57, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 4, "unify:other": 59}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G4-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b. (eq<list<a>, list<b>>, a) => b = (e, v) => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 30, "occur_shortcut:other": 30, "pair_compare:gadt": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 78, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 8, "unify:other": 78}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:82

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b. (eq<list<a>, list<b>>, a) => b = (e, v) => switch e { |
    │  Refl => 0 }
  3 │ 

  This has type: int
  But this switch is expected to return: b (defined as a)

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G4-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type alias<'a> = option<'a>
let f: type a b. (eq<alias<a>, option<b>>, a) => b = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 2, "occur:gadt": 2, "occur:other": 41, "occur_shortcut:gadt": 2, "occur_shortcut:other": 41, "pair_compare:other": 3, "pair_lookup:gadt": 4, "pair_lookup:other": 65, "same_path:gadt": 2, "same_path:other": 9, "unify:gadt": 4, "unify:other": 67}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G4-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type rec tree<'a> = Leaf('a) | Branch(tree<'a>)
let f: type a b. (eq<tree<a>, tree<b>>, a) => b = (e, v) => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 34, "occur_shortcut:other": 34, "pair_lookup:gadt": 8, "pair_lookup:other": 98, "same_path:gadt": 4, "same_path:other": 4, "unify:gadt": 8, "unify:other": 98}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:82

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ type rec tree<'a> = Leaf('a) | Branch(tree<'a>)
  3 │ let f: type a b. (eq<tree<a>, tree<b>>, a) => b = (e, v) => switch e { |
    │  Refl => 0 }
  4 │ 

  This has type: int
  But this switch is expected to return: b (defined as a)

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

### G5 — REACHED, NO DIFFERENCE SEEN

Make two locally abstract types equal and then equate a third type in both orientations and nesting orders (OCaml ctype.ml:2258–2270; Rust ctype.rs:8848–8860 and 9192–9204). Compare whether the chain is accepted and which abstract name remains in an incompatible result or arithmetic diagnostic.

Every candidate hits equation addition, with two additions per successful chain and four across the failed-build replay. All outputs agree. These probes cover chained equations and the Rust equation-selection path; no separately instrumented expansion-orientation branch proves that every OCaml level comparison was exercised.

#### G5-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (Refl, Refl, v) => v
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:gadt": 1, "occur:other": 27, "occur_shortcut:gadt": 1, "occur_shortcut:other": 27, "pair_lookup:gadt": 7, "pair_lookup:other": 69, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 7, "unify:other": 72}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(param, param$1, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G5-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<b, a>, eq<c, b>, a) => c = (Refl, Refl, v) => v
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:gadt": 1, "occur:other": 27, "occur_shortcut:gadt": 1, "occur_shortcut:other": 27, "pair_lookup:gadt": 7, "pair_lookup:other": 69, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 7, "unify:other": 72}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(param, param$1, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G5-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<c, b>, a) => c = (Refl, Refl, v) => 0
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:gadt": 2, "occur:other": 34, "occur_shortcut:gadt": 2, "occur_shortcut:other": 34, "pair_lookup:gadt": 14, "pair_lookup:other": 99, "same_path:gadt": 4, "same_path:other": 6, "unify:gadt": 14, "unify:other": 99}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:70

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b c. (eq<a, b>, eq<c, b>, a) => c = (Refl, Refl, v) => 0
  3 │ 

  This has type: int
  But it's expected to have type: c (defined as a)

```

stdout (empty):

```text
```

#### G5-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<b, a>, eq<b, c>, a) => c = (Refl, Refl, v) => "x"
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:gadt": 2, "occur:other": 34, "occur_shortcut:gadt": 2, "occur_shortcut:other": 34, "pair_lookup:gadt": 14, "pair_lookup:other": 99, "same_path:gadt": 4, "same_path:other": 6, "unify:gadt": 14, "unify:other": 99}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:70-72

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b c. (eq<b, a>, eq<b, c>, a) => c = (Refl, Refl, v) => "x"
  3 │ 

  This has type: string
  But it's expected to have type: c (defined as a)

```

stdout (empty):

```text
```

#### G5-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch e { | Refl => switch d { | Refl => v } }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:gadt": 1, "occur:other": 24, "occur_shortcut:gadt": 1, "occur_shortcut:other": 24, "pair_compare:other": 2, "pair_lookup:gadt": 7, "pair_lookup:other": 65, "same_path:gadt": 2, "same_path:other": 6, "unify:gadt": 7, "unify:other": 68}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, d, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G5-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch d { | Refl => switch e { | Refl => v } }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 25, "occur_shortcut:other": 25, "pair_compare:other": 3, "pair_lookup:gadt": 6, "pair_lookup:other": 65, "same_path:gadt": 2, "same_path:other": 6, "unify:gadt": 6, "unify:other": 68}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(e, d, v) {
  return v;
}

exports.f = f;
/* No side effect */
```

#### G5-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch e { | Refl => switch d { | Refl => v + 1 } }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:gadt": 2, "occur:other": 26, "occur_shortcut:gadt": 2, "occur_shortcut:other": 26, "pair_lookup:gadt": 14, "pair_lookup:other": 87, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 14, "unify:other": 87}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:106

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch e 
    │ { | Refl => switch d { | Refl => v + 1 } }
  3 │ 

  This has type: a
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### G5-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch d { | Refl => switch e { | Refl => v ++ "x" } }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:other": 26, "occur_shortcut:other": 26, "pair_lookup:gadt": 12, "pair_lookup:other": 87, "same_path:gadt": 4, "same_path:other": 2, "unify:gadt": 12, "unify:other": 87}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:106

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a b c. (eq<a, b>, eq<b, c>, a) => c = (e, d, v) => switch d 
    │ { | Refl => switch e { | Refl => v ++ "x" } }
  3 │ 

  This has type: a
  But string concatenation is expecting: string

```

stdout (empty):

```text
```

### G6 — WITNESS

Match an equality whose index is a functor parameter’s abstract, private or parameterized type (OCaml ctype.ml:1874–1881; Rust ctype.rs:579–595). After the match, demand that an expression of that module type have the concrete index type, so merely accepting the constructor pattern is insufficient.

#### Fixed

Fixed by `4a248ec60`; see "P1 - an equation can refine an abstract type
reached through a module path" in "Third round: differences found while
fixing". All eight candidates agree after it.

G6-2 is a witness: OCaml adds the abstract module type equation, but Rust’s newtype-level requirement prevents it, leaving the branch expression at `X.t`. G6-1/3–8 agree. All eight reach `is_instantiable`, but parameterized indices are filtered by the nullary-constructor check before that function; there is no evidence of a parameterized declaration being incorrectly instantiated. The witness demonstrates that the extra Rust newtype-level requirement is too restrictive, rather than that a missing privacy/arity test is too permissive.

#### G6-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t
}) => {
let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 1, "occur:other": 5, "occur_shortcut:other": 5, "pair_lookup:gadt": 3, "pair_lookup:other": 35, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 37}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:5:27

  3 │   type t
  4 │ }) => {
  5 │ let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => 0 }
  6 │ }
  7 │ 

  unused variable v.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_v`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (e, v) => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G6-2 — outputs differ

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t
}) => {
let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => v }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 6, "pair_lookup:other": 60, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 64}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (e, v) => v;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:5:64

  3 │   type t
  4 │ }) => {
  5 │ let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => v }
  6 │ }
  7 │ 

  This has type: X.t
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G6-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t<'a>
}) => {
let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 1, "mcomp:gadt": 1, "occur:other": 7, "occur_shortcut:other": 7, "pair_lookup:gadt": 3, "pair_lookup:other": 39, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 41}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:5:32

  3 │   type t<'a>
  4 │ }) => {
  5 │ let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl =>
    │  0 }
  6 │ }
  7 │ 

  unused variable v.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_v`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (e, v) => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G6-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t<'a>
}) => {
let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl => v }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 2, "mcomp:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 68, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 72}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:5:74

  3 │   type t<'a>
  4 │ }) => {
  5 │ let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl =>
    │  v }
  6 │ }
  7 │ 

  This has type: X.t<int>
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G6-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t = private int
}) => {
let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 1, "occur:gadt": 1, "occur:other": 6, "occur_shortcut:gadt": 1, "occur_shortcut:other": 6, "pair_compare:other": 2, "pair_lookup:gadt": 3, "pair_lookup:other": 38, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 40}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:5:27

  3 │   type t = private int
  4 │ }) => {
  5 │ let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => 0 }
  6 │ }
  7 │ 

  unused variable v.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_v`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (e, v) => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G6-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t = private int
}) => {
let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => v }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:gadt": 2, "occur:other": 12, "occur_shortcut:gadt": 2, "occur_shortcut:other": 12, "pair_compare:other": 3, "pair_lookup:gadt": 6, "pair_lookup:other": 66, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 70}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:5:64

  3 │   type t = private int
  4 │ }) => {
  5 │ let f = (e: eq<X.t, int>, v: X.t): int => switch e { | Refl => v }
  6 │ }
  7 │ 

  This has type: X.t
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G6-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t<'a> = private array<'a>
}) => {
let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 2, "mcomp:gadt": 2, "occur:gadt": 4, "occur:other": 22, "occur_shortcut:gadt": 4, "occur_shortcut:other": 22, "pair_compare:other": 9, "pair_lookup:gadt": 6, "pair_lookup:other": 80, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 84}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:5:66-69

  3 │   type t<'a> = private array<'a>
  4 │ }) => {
  5 │ let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl =>
    │  0 }
  6 │ }
  7 │ 

  This pattern matches values of type eq<X.t<int>, X.t<int>>
  but a pattern was expected which matches values of type eq<X.t<int>, int>
  
  The incompatible parts:
    X.t<int> vs int

```

stdout (empty):

```text
```

#### G6-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
  type t<'a> = private array<'a>
}) => {
let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl => v }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 2, "mcomp:gadt": 2, "occur:gadt": 4, "occur:other": 22, "occur_shortcut:gadt": 4, "occur_shortcut:other": 22, "pair_compare:other": 9, "pair_lookup:gadt": 6, "pair_lookup:other": 80, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 6, "unify:other": 84}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:5:66-69

  3 │   type t<'a> = private array<'a>
  4 │ }) => {
  5 │ let f = (e: eq<X.t<int>, int>, v: X.t<int>): int => switch e { | Refl =>
    │  v }
  6 │ }
  7 │ 

  This pattern matches values of type eq<X.t<int>, X.t<int>>
  but a pattern was expected which matches values of type eq<X.t<int>, int>
  
  The incompatible parts:
    X.t<int> vs int

```

stdout (empty):

```text
```

#### Reduced witness: abstract-index

Removing the switch and using a constructor parameter preserves G6-2; specializing the equality witness to a single `I: t<int>` constructor removes the second type parameter. Removing the abstract module boundary (abstract-root), removing the concrete result demand (abstract-no-return), or removing the value crossing the equation (abstract-no-value) removes the discrepancy. Replacing the functor with a sealed module also preserves it, but adds a module implementation rather than reducing the program. Rust is at fault: it accepts the constructor pattern but fails to apply the abstract module-type equation that makes the body type-correct in OCaml.

#### abstract-index — outputs differ

`Main.res`:

```rescript
type rec t<_> = I: t<int>
module F = (X: {type t}) => {
let f = (I: t<X.t>, v: X.t): int => v
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 6, "occur_shortcut:other": 6, "pair_lookup:gadt": 4, "pair_lookup:other": 47, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 51}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (param, v) => v;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:37

  1 │ type rec t<_> = I: t<int>
  2 │ module F = (X: {type t}) => {
  3 │ let f = (I: t<X.t>, v: X.t): int => v
  4 │ }

  This has type: X.t
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### abstract — outputs differ

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {type t}) => {
let f = (Refl: eq<X.t, int>, v: X.t): int => v
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 10, "occur_shortcut:other": 10, "pair_lookup:gadt": 6, "pair_lookup:other": 55, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 59}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (param, v) => v;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:46

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ module F = (X: {type t}) => {
  3 │ let f = (Refl: eq<X.t, int>, v: X.t): int => v
  4 │ }

  This has type: X.t
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### abstract-no-return — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {type t}) => {
let f = (Refl: eq<X.t, int>, v: X.t) => v
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 1, "occur:other": 5, "occur_shortcut:other": 5, "pair_compare:other": 1, "pair_lookup:gadt": 3, "pair_lookup:other": 27, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 30}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (param, v) => v;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### abstract-no-functor — outputs differ

`Main.res`:

```rescript
type rec t<_> = I: t<int>
module X: {type t} = {type t = int}
let f = (I: t<X.t>, v: X.t): int => v
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 8, "occur_shortcut:other": 8, "pair_lookup:gadt": 4, "pair_lookup:other": 53, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 57}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let X = {};

function f(param, v) {
  return v;
}

exports.X = X;
exports.f = f;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:37

  1 │ type rec t<_> = I: t<int>
  2 │ module X: {type t} = {type t = int}
  3 │ let f = (I: t<X.t>, v: X.t): int => v

  This has type: X.t
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### abstract-no-value — outputs agree

`Main.res`:

```rescript
type rec t<_> = I: t<int>
module F = (X: {type t}) => {
let f = (I: t<X.t>): int => 0
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 1, "occur:other": 3, "occur_shortcut:other": 3, "pair_lookup:gadt": 2, "pair_lookup:other": 21, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 2, "unify:other": 23}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = param => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### abstract-root — outputs agree

`Main.res`:

```rescript
type rec t<_> = I: t<int>
type a
let f = (I: t<a>, v: a): int => v
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 6, "occur_shortcut:other": 6, "pair_lookup:gadt": 4, "pair_lookup:other": 28, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 28}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:10

  1 │ type rec t<_> = I: t<int>
  2 │ type a
  3 │ let f = (I: t<a>, v: a): int => v

  This pattern matches values of type t<int>
  but a pattern was expected which matches values of type t<a>
  
  The incompatible parts:
    int vs a

```

stdout (empty):

```text
```

#### abstract-let — outputs differ

`Main.res`:

```rescript
type rec t<_> = I: t<int>
module X: {type t} = {type t = int}
let f = (I: t<X.t>, v: X.t) => v + 1
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 8, "occur_shortcut:other": 8, "pair_compare:other": 2, "pair_lookup:gadt": 4, "pair_lookup:other": 51, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 55}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


let X = {};

function f(param, v) {
  return v + 1 | 0;
}

exports.X = X;
exports.f = f;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:32

  1 │ type rec t<_> = I: t<int>
  2 │ module X: {type t} = {type t = int}
  3 │ let f = (I: t<X.t>, v: X.t) => v + 1

  This has type: X.t
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### abstract-short — outputs differ

`Main.res`:

```rescript
type rec t<_> = I: t<int>
module F = (X: {type t}) => {
let f = (I: t<X.t>, v: X.t) => v + 1
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 6, "occur_shortcut:other": 6, "pair_lookup:gadt": 4, "pair_lookup:other": 45, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 49}
```

Ocaml, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = (param, v) => v + 1 | 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

Rust, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:32

  1 │ type rec t<_> = I: t<int>
  2 │ module F = (X: {type t}) => {
  3 │ let f = (I: t<X.t>, v: X.t) => v + 1
  4 │ }

  This has type: X.t
  But it's expected to have type: int

```

stdout (empty):

```text
```

### G7 — REACHED, NO DIFFERENCE SEEN

Type consecutive GADT constructor patterns in branches, nested matches, tuples and an or-pattern (OCaml ctype.ml:2739–2750; Rust typecore.rs:5516–5567). Check incompatible branches and warnings 8, 11 and 56 after the wrapper restores its flags without clearing the shared pair set.

G7-1–6/8–11 execute the wrapper, and agree; G7-7 rejects the or-pattern before entering it. G7-9 has warning 8 with example `Str`, G7-10 warning 11, and G7-11 warnings 4 and 56; all warning bytes and locations agree. Wrapper entries do not by themselves prove that a particular pair remains live across two invocations.

#### G7-1 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => 0 | Str => "" }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 3, "gadt:gadt": 3, "instantiable:gadt": 6, "occur:other": 18, "occur_shortcut:other": 18, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 50, "same_path:gadt": 3, "same_path:other": 7, "unify:gadt": 6, "unify:other": 52}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:37

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => 0 | Str =>
    │  "" }
  3 │ 

  unused variable y.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_y`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  if (x === "Int") {
    return 0;
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-2 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch x { | Str => "" | Int => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 3, "gadt:gadt": 3, "instantiable:gadt": 6, "occur:other": 18, "occur_shortcut:other": 18, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 50, "same_path:gadt": 3, "same_path:other": 7, "unify:gadt": 6, "unify:other": 52}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:37

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch x { | Str => "" | Int =
    │ > 0 }
  3 │ 

  unused variable y.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_y`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  if (x === "Int") {
    return 0;
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-3 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => "" | Str => "" }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 8, "pair_lookup:other": 74, "same_path:gadt": 4, "same_path:other": 6, "unify:gadt": 8, "unify:other": 74}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:63-64

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => "" | Str =
    │ > "" }
  3 │ 

  This has type: string
  But this switch is expected to return: a (defined as int)

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.
  
  You can convert string to int with Int.fromString.

```

stdout (empty):

```text
```

#### G7-4 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => switch x { | Int => 0 } | Str => "" }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 3, "gadt:gadt": 5, "instantiable:gadt": 8, "mcomp:gadt": 1, "occur:gadt": 3, "occur:other": 18, "occur_shortcut:gadt": 3, "occur_shortcut:other": 18, "pair_compare:gadt": 1, "pair_compare:other": 1, "pair_lookup:gadt": 11, "pair_lookup:other": 54, "same_path:gadt": 6, "same_path:other": 7, "unify:gadt": 11, "unify:other": 56}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:37

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int => switch x {
    │  | Int => 0 } | Str => "" }
  3 │ 

  unused variable y.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_y`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  if (x === "Int") {
    return 0;
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-5 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch (x, y) { | (Int, 0) => 0 | (Int, _) => 1 | (Str, _) => "" }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 5, "gadt:gadt": 5, "instantiable:gadt": 10, "occur:other": 32, "occur_shortcut:other": 32, "pair_compare:gadt": 1, "pair_compare:other": 6, "pair_lookup:gadt": 10, "pair_lookup:other": 76, "same_path:gadt": 5, "same_path:other": 10, "tuple:other": 7, "unify:gadt": 10, "unify:other": 78}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  if (x === "Int") {
    if (y !== 0) {
      return 1;
    } else {
      return 0;
    }
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-6 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch (x, x) { | (Int, Int) => 0 | (Str, Str) => "" }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 5, "gadt:gadt": 10, "instantiable:gadt": 14, "mcomp:gadt": 2, "occur:gadt": 7, "occur:other": 30, "occur_shortcut:gadt": 7, "occur_shortcut:other": 30, "pair_compare:other": 3, "pair_lookup:gadt": 22, "pair_lookup:other": 80, "same_path:gadt": 13, "same_path:other": 8, "tuple:other": 10, "unify:gadt": 22, "unify:other": 83}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:37

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch (x, x) { | (Int, Int) =
    │ > 0 | (Str, Str) => "" }
  3 │ 

  unused variable y.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_y`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  if (x === "Int") {
    return 0;
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-7 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int | Str => y }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "occur:other": 18, "occur_shortcut:other": 18, "pair_lookup:other": 70, "same_path:other": 6, "unify:other": 70}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:56-58

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => switch x { | Int | Str => y }
  3 │ 

  This pattern matches values of type t<int>
  but a pattern was expected which matches values of type t<a>
  
  The incompatible parts:
    int vs a

```

stdout (empty):

```text
```

#### G7-8 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. (t<a>, a) => a = (x, y) => {let z = switch x { | Int => 0 | Str => 1 }; switch x { | Int => z | Str => "" }}
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 6, "gadt:gadt": 6, "instantiable:gadt": 12, "occur:other": 19, "occur_shortcut:other": 19, "pair_compare:other": 5, "pair_lookup:gadt": 12, "pair_lookup:other": 58, "same_path:gadt": 6, "same_path:other": 8, "unify:gadt": 12, "unify:other": 61}
```

Both compilers, exit 0; stderr:

```text

  Warning number 27
  Main.res:2:37

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. (t<a>, a) => a = (x, y) => {let z = switch x { | Int => 0
    │  | Str => 1 }; switch x { | Int => z | Str => "" }}
  3 │ 

  unused variable y.

Fix this by:
- Deleting the variable if it's not used anymore.
- Prepending the variable name with `_` (like `_y`) to ignore that the variable is unused.
- Using the variable somewhere.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x, y) {
  let z;
  z = x === "Int" ? 0 : 1;
  if (x === "Int") {
    return z;
  } else {
    return "";
  }
}

exports.f = f;
/* No side effect */
```

#### G7-9 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. t<a> => int = x => switch x { | Int => 0 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 4, "occur:other": 13, "occur_shortcut:other": 13, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 44, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 4, "unify:other": 44}
```

Both compilers, exit 0; stderr:

```text

  Warning number 8
  Main.res:2:35-57

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. t<a> => int = x => switch x { | Int => 0 }

  You forgot to handle a possible case here, for example: 
  | Str

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  if (x === "Int") {
    return 0;
  }
  throw {
    RE_EXN_ID: "Match_failure",
    _1: [
      "Main.res",
      2,
      34
    ],
    Error: new Error()
  };
}

exports.f = f;
/* No side effect */
```

#### G7-10 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f: type a. t<a> => int = x => switch x { | Int => 0 | Str => 1 | Int => 2 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 4, "gadt:gadt": 4, "instantiable:gadt": 8, "occur:other": 15, "occur_shortcut:other": 15, "pair_compare:gadt": 1, "pair_compare:other": 2, "pair_lookup:gadt": 8, "pair_lookup:other": 52, "same_path:gadt": 4, "same_path:other": 6, "unify:gadt": 8, "unify:other": 52}
```

Both compilers, exit 0; stderr:

```text

  Warning number 11
  Main.res:2:70-72

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f: type a. t<a> => int = x => switch x { | Int => 0 | Str => 1 | Int
    │  => 2 }

  this match case is unused.

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  if (x === "Int") {
    return 0;
  } else {
    return 1;
  }
}

exports.f = f;
/* No side effect */
```

#### G7-11 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Int: t<int> | Str: t<string>
let f = (x: t<int>) => switch x { | Int => 0 | _ => 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 2, "mcomp:gadt": 1, "occur:other": 6, "occur_shortcut:other": 6, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 34, "same_path:gadt": 2, "same_path:other": 3, "unify:gadt": 4, "unify:other": 37}
```

Both compilers, exit 0; stderr:

```text

  Warning number 4
  Main.res:2:24-55

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f = (x: t<int>) => switch x { | Int => 0 | _ => 1 }

  this pattern-matching is fragile.
It will remain exhaustive when constructors are added to type t.


  Warning number 56
  Main.res:2:48

  1 │ type rec t<_> = Int: t<int> | Str: t<string>
  2 │ let f = (x: t<int>) => switch x { | Int => 0 | _ => 1 }

  this match case is unreachable.
Consider replacing it with a refutation case '<pat> -> .'

```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  if (x === "Int") {
    return 0;
  } else {
    return 1;
  }
}

exports.f = f;
/* No side effect */
```

### G8 — REACHED, NO DIFFERENCE SEEN

Match a constructor with an existential payload and, in the indexed cases, equate a locally abstract result with a structure containing that payload (OCaml ctype.ml:2084–2100 and 2390–2394; Rust ctype.rs:1700–1722). Check escape errors and forced concrete payloads for invented type names as well as acceptance.

G8-1–8 are existential-escape controls: the wrapper runs, but `add_gadt_equation` does not. G8-9–16 hit equation addition and agree, including the rejected concrete payloads. The fallback for a declaration without a newtype level is not independently reached here; G6 explains one guard preventing such an equation in Rust.

#### G8-1 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a): packed
let f = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 20, "unify:gadt": 2, "unify:other": 20}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack('a): packed
  2 │ let f = x => switch x { | Pack(v) => v }
  3 │ 

  This has type: $a
  But this switch is expected to return: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G8-2 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack(array<'a>): packed
let f = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 4, "occur_shortcut:other": 4, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 32, "same_path:other": 2, "unify:gadt": 2, "unify:other": 32}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack(array<'a>): packed
  2 │ let f = x => switch x { | Pack(v) => v }
  3 │ 

  This has type: array<$a>
  But this switch is expected to return: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G8-3 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a => 'a): packed
let f = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 20, "unify:gadt": 2, "unify:other": 20}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack('a => 'a): packed
  2 │ let f = x => switch x { | Pack(v) => v }
  3 │ 

  This has type: $a => $a
  But this switch is expected to return: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G8-4 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack(option<'a>): packed
let f = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "occur:other": 4, "occur_shortcut:other": 4, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 32, "same_path:other": 2, "unify:gadt": 2, "unify:other": 32}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack(option<'a>): packed
  2 │ let f = x => switch x { | Pack(v) => v }
  3 │ 

  This has type: option<$a>
  But this switch is expected to return: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G8-5 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a): packed
let f = x => switch x { | Pack(v) => v + 1 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 21, "unify:gadt": 2, "unify:other": 21}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack('a): packed
  2 │ let f = x => switch x { | Pack(v) => v + 1 }
  3 │ 

  This has type: $a
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### G8-6 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a): packed
let f = x => switch x { | Pack(v) => v ++ "x" }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 21, "unify:gadt": 2, "unify:other": 21}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:38

  1 │ type rec packed = Pack('a): packed
  2 │ let f = x => switch x { | Pack(v) => v ++ "x" }
  3 │ 

  This has type: $a
  But string concatenation is expecting: string

```

stdout (empty):

```text
```

#### G8-7 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a): packed
let f = x => switch x { | Pack(v) => (v, v) }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 23, "unify:gadt": 2, "unify:other": 23}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:39

  1 │ type rec packed = Pack('a): packed
  2 │ let f = x => switch x { | Pack(v) => (v, v) }
  3 │ 

  This has type: $a
  But it's expected to have type: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

```

stdout (empty):

```text
```

#### G8-8 — outputs agree

`Main.res`:

```rescript
type rec packed = Pack('a): packed
let f = x => switch x { | Pack(v) => Some(v) }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 23, "unify:gadt": 2, "unify:other": 23}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:43

  1 │ type rec packed = Pack('a): packed
  2 │ let f = x => switch x { | Pack(v) => Some(v) }
  3 │ 

  This has type: $a
  But it's expected to have type: 'a
  $a is an existential type bound by the constructor Pack.
  It is only known in the scope of the pattern that matches Pack.

```

stdout (empty):

```text
```

#### G8-9 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(option<'b>): t<option<'b>>
let f: type a. t<a> => a = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 17, "occur_shortcut:other": 17, "pair_compare:other": 3, "pair_lookup:gadt": 2, "pair_lookup:other": 47, "same_path:gadt": 1, "same_path:other": 6, "unify:gadt": 2, "unify:other": 48}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x._0;
}

exports.f = f;
/* No side effect */
```

#### G8-10 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(array<'b>): t<array<'b>>
let f: type a. t<a> => a = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 17, "occur_shortcut:other": 17, "pair_compare:other": 3, "pair_lookup:gadt": 2, "pair_lookup:other": 47, "same_path:gadt": 1, "same_path:other": 6, "unify:gadt": 2, "unify:other": 48}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x._0;
}

exports.f = f;
/* No side effect */
```

#### G8-11 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack('b => 'b): t<'b => 'b>
let f: type a. t<a> => a = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 4, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 13, "occur_shortcut:other": 13, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 35, "same_path:gadt": 1, "same_path:other": 3, "unify:gadt": 2, "unify:other": 37}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x._0;
}

exports.f = f;
/* No side effect */
```

#### G8-12 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(('b, 'b)): t<('b, 'b)>
let f: type a. t<a> => a = x => switch x { | Pack(v) => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 3, "equation:gadt": 1, "gadt:gadt": 1, "instantiable:gadt": 1, "occur:other": 13, "occur_shortcut:other": 13, "pair_compare:other": 2, "pair_lookup:gadt": 2, "pair_lookup:other": 35, "same_path:gadt": 1, "same_path:other": 3, "tuple:other": 1, "unify:gadt": 2, "unify:other": 37}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function f(x) {
  return x._0;
}

exports.f = f;
/* No side effect */
```

#### G8-13 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(option<'b>): t<option<'b>>
let f: type a. t<a> => a = x => switch x { | Pack(v) => Some(0) }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 24, "occur_shortcut:other": 24, "pair_compare:other": 1, "pair_lookup:gadt": 4, "pair_lookup:other": 77, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 4, "unify:other": 77}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:62

  1 │ type rec t<_> = Pack(option<'b>): t<option<'b>>
  2 │ let f: type a. t<a> => a = x => switch x { | Pack(v) => Some(0) }

  This has type: int
  But it's expected to have type: $0

```

stdout (empty):

```text
```

#### G8-14 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(array<'b>): t<array<'b>>
let f: type a. t<a> => a = x => switch x { | Pack(v) => [0] }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 24, "occur_shortcut:other": 24, "pair_compare:other": 3, "pair_lookup:gadt": 4, "pair_lookup:other": 76, "same_path:gadt": 2, "same_path:other": 8, "unify:gadt": 4, "unify:other": 76}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:58

  1 │ type rec t<_> = Pack(array<'b>): t<array<'b>>
  2 │ let f: type a. t<a> => a = x => switch x { | Pack(v) => [0] }

  This array item has type: int
  But this array is expected to have items of type: $0

  Arrays can only contain items of the same type.

  Possible solutions:
  - Convert all values in the array to the same type.
  - Use a tuple, if your array is of fixed length. Tuples can mix types freely, and compiles to a JavaScript array. Example of a tuple: `let myTuple = (10, "hello", 15.5, true)

```

stdout (empty):

```text
```

#### G8-15 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack('b => 'b): t<'b => 'b>
let f: type a. t<a> => a = x => switch x { | Pack(v) => x => x + 1 }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 4, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 18, "occur_shortcut:other": 18, "pair_compare:other": 2, "pair_lookup:gadt": 4, "pair_lookup:other": 57, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 4, "unify:other": 57}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:62

  1 │ type rec t<_> = Pack('b => 'b): t<'b => 'b>
  2 │ let f: type a. t<a> => a = x => switch x { | Pack(v) => x => x + 1 }

  This has type: $0
  But it's expected to have type: int

```

stdout (empty):

```text
```

#### G8-16 — outputs agree

`Main.res`:

```rescript
type rec t<_> = Pack(('b, 'b)): t<('b, 'b)>
let f: type a. t<a> => a = x => switch x { | Pack(v) => (0, 0) }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 16, "occur_shortcut:other": 16, "pair_compare:other": 2, "pair_lookup:gadt": 4, "pair_lookup:other": 55, "same_path:gadt": 2, "same_path:other": 2, "tuple:other": 2, "unify:gadt": 4, "unify:other": 55}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:58

  1 │ type rec t<_> = Pack(('b, 'b)): t<('b, 'b)>
  2 │ let f: type a. t<a> => a = x => switch x { | Pack(v) => (0, 0) }

  This has type: int
  But it's expected to have type: $0

```

stdout (empty):

```text
```

### G9 — REACHED, NO DIFFERENCE SEEN

Use `eq<a, RHS<a>>` with recursive structural and constructor right-hand sides, including an abbreviation that expands during unification (OCaml ctype.ml:1467–1490; Rust ctype.rs:2190–2337). Check whether the equation itself or a later concrete demand is rejected and compare the printed recursive abbreviation.

G9-1–7 add equations but do not call `occur_check` under the GADT wrapper. G9-8 does: four Pattern-context calls take the cheap `occur_shortcut`, confirmed by a breakpoint at the successful shortcut return; both compilers give the same mismatch. This reaches the shortcut departure but does not establish a repeated-walk/type-change counterexample.

#### G9-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, list<a>>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 26, "occur_shortcut:other": 26, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 72, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 72}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:76

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, list<a>>, a) => int = (e, v) => switch e { | Refl 
    │ => v }
  3 │ 

  This has type: a (defined as list<a>)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, a => a>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 24, "occur_shortcut:other": 24, "pair_compare:other": 1, "pair_lookup:gadt": 6, "pair_lookup:other": 67, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 67}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:75

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, a => a>, a) => int = (e, v) => switch e { | Refl =
    │ > v }
  3 │ 

  This has type: a (defined as a => a)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, option<a>>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 26, "occur_shortcut:other": 26, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 72, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 72}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:78

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, option<a>>, a) => int = (e, v) => switch e { | Ref
    │ l => v }
  3 │ 

  This has type: a (defined as option<a>)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, array<a>>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 26, "occur_shortcut:other": 26, "pair_compare:other": 2, "pair_lookup:gadt": 6, "pair_lookup:other": 72, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 72}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:77

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, array<a>>, a) => int = (e, v) => switch e { | Refl
    │  => v }
  3 │ 

  This has type: a (defined as array<a>)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, (a, a)>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:other": 1, "pair_lookup:gadt": 6, "pair_lookup:other": 66, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 66}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:75

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, (a, a)>, a) => int = (e, v) => switch e { | Refl =
    │ > v }
  3 │ 

  This has type: a (defined as (a, a))
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, [#a(a)]>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 6, "pair_lookup:other": 64, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:76

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, [#a(a)]>, a) => int = (e, v) => switch e { | Refl 
    │ => v }
  3 │ 

  This has type: a
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
let f: type a. (eq<a, {"x": a}>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_compare:other": 3, "pair_lookup:gadt": 6, "pair_lookup:other": 64, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 64}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:2:77

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ let f: type a. (eq<a, {"x": a}>, a) => int = (e, v) => switch e { | Refl
    │  => v }
  3 │ 

  This has type: a
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

#### G9-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type alias<'a> = array<'a>
let f: type a. (eq<a, alias<a>>, a) => int = (e, v) => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"arrow:other": 2, "equation:gadt": 2, "gadt:gadt": 2, "instantiable:gadt": 2, "occur:gadt": 4, "occur:other": 34, "occur_shortcut:gadt": 4, "occur_shortcut:other": 34, "pair_lookup:gadt": 8, "pair_lookup:other": 88, "same_path:gadt": 2, "same_path:other": 4, "unify:gadt": 8, "unify:other": 88}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:3:77

  1 │ type rec eq<_, _> = Refl: eq<'a, 'a>
  2 │ type alias<'a> = array<'a>
  3 │ let f: type a. (eq<a, alias<a>>, a) => int = (e, v) => switch e { | Refl
    │  => v }
  4 │ 

  This has type: a (defined as array<a>)
  But this switch is expected to return: int

  All branches in a switch must return the same type.
  To fix this, change your branch to return the expected type.

```

stdout (empty):

```text
```

### G10 — REACHED, NO DIFFERENCE SEEN

Compare GADT indices containing polymorphic record fields, first as local datatypes and then through a functor parameter so compatibility can inspect their fields (OCaml ctype.ml:1961–1964 and 2080; Rust ctype.rs:852–857 and `mcomp_enter_poly`). Check both compatible polymorphic signatures and incompatible field results, including any exhaustiveness diagnostic.

G10-1–8 stop at incompatible local datatype paths; they hit `mcomp` but not `mcomp_enter_poly`. G10-9–16 reach `mcomp_enter_poly` under the GADT wrapper and agree. This exercises the empty-pair initialization and the polymorphic compatibility body, but does not prove a nonempty outer universal-pair environment at entry; that stronger condition remains unestablished.

#### G10-1 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. 'a => 'a}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 56, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 60}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. 'a => 'a}
  3 │ type s = {f: 'a. 'a => 'a}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-2 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. 'a => 'a}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 56, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 60}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. 'a => 'a}
  3 │ type s = {f: 'a. 'a => 'a}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-3 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. array<'a> => array<'a>}
type s = {f: 'a. array<'a> => array<'a>}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 30, "occur_shortcut:other": 30, "pair_lookup:gadt": 6, "pair_lookup:other": 104, "same_path:gadt": 2, "same_path:other": 10, "unify:gadt": 6, "unify:other": 108}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. array<'a> => array<'a>}
  3 │ type s = {f: 'a. array<'a> => array<'a>}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-4 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. array<'a> => array<'a>}
type s = {f: 'a. array<'a> => array<'a>}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 30, "occur_shortcut:other": 30, "pair_lookup:gadt": 6, "pair_lookup:other": 104, "same_path:gadt": 2, "same_path:other": 10, "unify:gadt": 6, "unify:other": 108}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. array<'a> => array<'a>}
  3 │ type s = {f: 'a. array<'a> => array<'a>}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-5 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. option<'a> => option<'a>}
type s = {f: 'a. option<'a> => option<'a>}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 30, "occur_shortcut:other": 30, "pair_lookup:gadt": 6, "pair_lookup:other": 104, "same_path:gadt": 2, "same_path:other": 10, "unify:gadt": 6, "unify:other": 108}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. option<'a> => option<'a>}
  3 │ type s = {f: 'a. option<'a> => option<'a>}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-6 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. option<'a> => option<'a>}
type s = {f: 'a. option<'a> => option<'a>}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 30, "occur_shortcut:other": 30, "pair_lookup:gadt": 6, "pair_lookup:other": 104, "same_path:gadt": 2, "same_path:other": 10, "unify:gadt": 6, "unify:other": 108}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. option<'a> => option<'a>}
  3 │ type s = {f: 'a. option<'a> => option<'a>}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-7 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. ('a, 'a) => 'a}
type s = {f: 'a. ('a, 'a) => 'a}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 56, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 60}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. ('a, 'a) => 'a}
  3 │ type s = {f: 'a. ('a, 'a) => 'a}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => v }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-8 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
type r = {f: 'a. ('a, 'a) => 'a}
type s = {f: 'a. ('a, 'a) => 'a}
let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 56, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 60}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:4:48-51

  2 │ type r = {f: 'a. ('a, 'a) => 'a}
  3 │ type s = {f: 'a. ('a, 'a) => 'a}
  4 │ let f = (e: eq<r, s>, v: r): s => switch e { | Refl => 0 }
  5 │ 

  This pattern matches values of type eq<r, r>
  but a pattern was expected which matches values of type eq<r, s>
  
  The incompatible parts:
    r vs s

```

stdout (empty):

```text
```

#### G10-9 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. 'a => 'a}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 5, "mcomp_poly:gadt": 1, "occur:other": 7, "occur_shortcut:other": 7, "pair_compare:other": 1, "pair_lookup:gadt": 3, "pair_lookup:other": 26, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 28}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = e => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G10-10 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. array<'a> => array<'a>}
type s = {f: 'a. array<'a> => array<'a>}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 7, "mcomp_poly:gadt": 1, "occur:other": 15, "occur_shortcut:other": 15, "pair_lookup:gadt": 3, "pair_lookup:other": 50, "same_path:gadt": 1, "same_path:other": 5, "unify:gadt": 3, "unify:other": 52}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = e => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G10-11 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. option<'a> => option<'a>}
type s = {f: 'a. option<'a> => option<'a>}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 7, "mcomp_poly:gadt": 1, "occur:other": 15, "occur_shortcut:other": 15, "pair_lookup:gadt": 3, "pair_lookup:other": 50, "same_path:gadt": 1, "same_path:other": 5, "unify:gadt": 3, "unify:other": 52}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = e => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G10-12 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. ('a, 'a) => 'a}
type s = {f: 'a. ('a, 'a) => 'a}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 1, "instantiable:gadt": 2, "mcomp:gadt": 6, "mcomp_poly:gadt": 1, "occur:other": 7, "occur_shortcut:other": 7, "pair_compare:other": 1, "pair_lookup:gadt": 3, "pair_lookup:other": 26, "same_path:gadt": 1, "same_path:other": 1, "unify:gadt": 3, "unify:other": 28}
```

Both compilers, exit 0; stderr (empty):

```text
```

stdout (generated JavaScript):

```javascript
// Generated by ReScript, PLEASE EDIT WITH CARE
'use strict';


function F(X) {
  let f = e => 0;
  return {
    f: f
  };
}

exports.F = F;
/* No side effect */
```

#### G10-13 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. 'a => int}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 10, "mcomp_poly:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 50, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 52}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:6:43-46

  4 │ type s = {f: 'a. 'a => int}
  5 │ }) => {
  6 │ let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
  7 │ }

  This pattern matches values of type eq<X.r, X.r>
  but a pattern was expected which matches values of type eq<X.r, X.s>
  
  The incompatible parts:
    X.r vs X.s

```

stdout (empty):

```text
```

#### G10-14 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. array<'a> => array<int>}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 8, "mcomp_poly:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 6, "pair_lookup:other": 74, "same_path:gadt": 2, "same_path:other": 6, "unify:gadt": 6, "unify:other": 76}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:6:43-46

  4 │ type s = {f: 'a. array<'a> => array<int>}
  5 │ }) => {
  6 │ let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
  7 │ }

  This pattern matches values of type eq<X.r, X.r>
  but a pattern was expected which matches values of type eq<X.r, X.s>
  
  The incompatible parts:
    X.r vs X.s

```

stdout (empty):

```text
```

#### G10-15 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. option<'a> => option<int>}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 8, "mcomp_poly:gadt": 2, "occur:other": 22, "occur_shortcut:other": 22, "pair_lookup:gadt": 6, "pair_lookup:other": 74, "same_path:gadt": 2, "same_path:other": 6, "unify:gadt": 6, "unify:other": 76}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:6:43-46

  4 │ type s = {f: 'a. option<'a> => option<int>}
  5 │ }) => {
  6 │ let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
  7 │ }

  This pattern matches values of type eq<X.r, X.r>
  but a pattern was expected which matches values of type eq<X.r, X.s>
  
  The incompatible parts:
    X.r vs X.s

```

stdout (empty):

```text
```

#### G10-16 — outputs agree

`Main.res`:

```rescript
type rec eq<_, _> = Refl: eq<'a, 'a>
module F = (X: {
type r = {f: 'a. 'a => 'a}
type s = {f: 'a. ('a, 'a) => int}
}) => {
let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
}
```

Debugger counts (separate invocation):

```json
{"gadt:gadt": 2, "instantiable:gadt": 4, "mcomp:gadt": 6, "mcomp_poly:gadt": 2, "occur:other": 14, "occur_shortcut:other": 14, "pair_lookup:gadt": 6, "pair_lookup:other": 50, "same_path:gadt": 2, "same_path:other": 2, "unify:gadt": 6, "unify:other": 52}
```

Both compilers, exit 2; stderr:

```text

  We've found a bug for you!
  Main.res:6:43-46

  4 │ type s = {f: 'a. ('a, 'a) => int}
  5 │ }) => {
  6 │ let f = (e: eq<X.r, X.s>) => switch e { | Refl => 0 }
  7 │ }

  This pattern matches values of type eq<X.r, X.r>
  but a pattern was expected which matches values of type eq<X.r, X.s>
  
  The incompatible parts:
    X.r vs X.s

```

stdout (empty):

```text
```

### Found on the way

No departure outside G1–G10 was observed in these runs. The stricter Rust
newtype-level requirement is recorded as G6, even though its direction is
the reverse of the missing privacy/arity checks proposed in the inventory.

### Limits and verification

The source and manifests are unchanged. No whole compiler test suite was
run. This search does not certify all internal-state combinations: notably,
G2/G7 do not prove cross-mode pair reuse, G5 does not separately trace the
OCaml level-choice branch, G8 does not exercise the missing-level fallback,
and G10 does not establish inherited nonempty universal pairs. The concrete
reachability and output evidence above is the extent of each verdict.

Application self-comparison with two byte-identical copies of the unchanged
release executable also matched: 3,735 signatures, 32 diagnostics in 18 files,
and 3,980 generated files. This verifies repeatability, not a Rust-versus-OCaml
comparison or a performance improvement; the pattern evidence above comes
from separate Rust and OCaml invocations.
