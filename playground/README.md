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

Each compile request starts a new compiler build generation, like a rewatch
rebuild: portable registry signatures survive, but worker component views from
the previous type context do not. User modules are registered as a virtual
CommonJS package, so dependency imports resolve without generated files on disk.
The smoke test also executes the generated JavaScript and checks the dependent
module's exported value before and after the edit.
