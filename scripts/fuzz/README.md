# Differential compiler fuzzing

OCaml `bsc` is the oracle; Rust `bsc` must reach the same verdict
(accept / reject / same diagnostic) on every input.

```bash
# prerequisites: OCaml bsc + stdlib (make lib), Rust release bsc
cargo build --release --manifest-path compiler-rust/Cargo.toml

python3 scripts/fuzz/fuzz.py seeds            # build seed corpus, check every seed
python3 scripts/fuzz/fuzz.py run -m 10        # mutate seeds for 10 minutes
python3 scripts/fuzz/fuzz.py reduce           # delta-debug new findings
python3 scripts/fuzz/fuzz.py regress          # re-check buckets, mark fixed ones
python3 scripts/fuzz/fuzz.py report --open    # list open buckets by priority
python3 scripts/fuzz/fuzz.py check A.res      # compare one case by hand
```

Finding kinds, most important first:

| kind | meaning |
|---|---|
| `rust_accepts` | OCaml rejects, Rust accepts (missing check) |
| `crash` | Rust panics, overflows its stack, or times out |
| `rust_rejects` | OCaml accepts, Rust rejects |
| `msg_diff` | both reject, diagnostics differ |
| `warn_diff` | both accept, warnings differ |
| `ocaml_crash` | the oracle itself crashed (not a Rust bug) |

State lives in the git-ignored `.fuzz/` directory. A fixed bucket should get
a fixture under `tests/error_output_parity/` or `tests/build_tests/super_errors/`
so the regular parity gates keep it fixed.
