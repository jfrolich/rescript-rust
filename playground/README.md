# Rust compiler playground

Install the repository's pinned Rust toolchain, `wasm-pack`, Node.js, and the
`wasm32-unknown-unknown` target (`rustup target add wasm32-unknown-unknown`).
From this directory:

```sh
npm run build:wasm
npm run test:wasm
```

The build script selects getrandom's `wasm_js` backend and produces the web-target
bundle in `crate/pkg`. The smoke test runs that exact bundle in Node, loads the
runtime sources into the virtual filesystem, compiles two dependent modules,
changes an exported type, checks rejection of the old consumer and acceptance
of the updated consumer, and checks that clearing the registry removes modules.

The crate targets wasm, not native platforms. A quick API compatibility check is:

```sh
RUSTFLAGS='--cfg getrandom_backend="wasm_js"' cargo check --locked --manifest-path crate/Cargo.toml --target wasm32-unknown-unknown
```

Known runtime blocker: repeated compilation with the standard library can panic
in `TypeContext::resolve_table_loc` with `declaration location of another
compilation`. The smoke test intentionally fails until that compiler lifetime
problem is fixed; a successful wasm build alone does not establish runtime health.
