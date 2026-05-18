# OCaml Alignment Setup

## Build

Run from the repository root.

```bash
cargo build --release --manifest-path compiler-rust/Cargo.toml
cargo build --release --manifest-path rewatch/Cargo.toml
```

## Typedtree Parity

Authoritative run:

```bash
find .parity-cache/tests/diffs -type f -delete
find .parity-cache/tests/ocaml -type f -delete
find .parity-cache/tests/rust -type f -delete
./scripts/test_typedtree_parity.sh --release
```

Focused run:

```bash
./scripts/test_typedtree_parity.sh --release <pattern>
```

Analyzer examples:

```bash
python3 scripts/parity_analyzer.py summary
python3 scripts/parity_analyzer.py divergence-summary
python3 scripts/parity_analyzer.py divergence <file-key>
python3 scripts/parity_analyzer.py sharing <file-key>
python3 scripts/parity_analyzer.py trace <file-key> <type-id>
```

## Lambda Parity Guard

```bash
./scripts/test_lambda_parity.sh --release
```

Raw lambda parity may have separate project debt. Do not treat raw lambda
failures as OCaml alignment failures unless the current task touches raw lambda
or typedtree-to-lambda boundaries.

## Direct bsc Repro

Use direct compiler runs only when the parity script is not enough.

```bash
cd tests/tests
../../packages/@rescript/darwin-arm64/bin/rescript.exe compiler-args src/<file>.res
cd lib/bs
timeout 10 /absolute/path/to/compiler-rust/target/release/bsc -dtyped-sexp <args...> 2> /tmp/rust.sexp 1>/dev/null
timeout 10 /absolute/path/to/_build/install/default/bin/bsc -dtyped-sexp <args...> 2> /tmp/ocaml.sexp 1>/dev/null
diff -u /tmp/ocaml.sexp /tmp/rust.sexp | sed -n '1,220p'
```

## Source Map

OCaml Env/lazy module components:

- `compiler/ml/env.ml:67-120` for `EnvLazy`
- `compiler/ml/env.ml:781-882` for `find_module_descr` and `find_module`
- `compiler/ml/env.ml:1435-1598` for `scrape_alias`,
  `prefix_idents`, and `components_of_module_maker`
- `compiler/ml/env.ml:1841-1878` for `add_components` and `open_signature`

OCaml substitution and freshening:

- `compiler/ml/subst.ml:69-95` for path substitution
- `compiler/ml/subst.ml:327-364` for bound-id freshening and
  `Subst.signature`
- `compiler/ext/ident.ml:26-58` for stamp creation and side effects

Rust equivalents:

- `compiler-rust/src/types/env_lazy.rs`
- `compiler-rust/src/types/env.rs`
- `compiler-rust/src/types/typecore.rs`
- `compiler-rust/src/types/ctype.rs`
- `compiler-rust/src/types/typemod.rs`
- `compiler-rust/src/types/includemod.rs`
- `compiler-rust/src/cmi/persistent_env.rs`
- `compiler-rust/src/types/context.rs`

## Dirty Worktree Note

This repository often has unrelated generated-file churn. Stage only files
owned by the current task. Never revert unrelated changes.

