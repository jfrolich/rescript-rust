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
