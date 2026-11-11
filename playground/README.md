# Macros site and playground

A static site for the Rust compiler's compile-time macros. The compiler runs
in WebAssembly in a worker; macros run in the browser's JavaScript engine. A
project is a few files: they are compiled in dependency order, and the
compiled program is run.

| Page | What |
| --- | --- |
| `index.html` | The RFC, rendered from [docs/comptime/README.md](../docs/comptime/README.md). Each `<!-- example: id -->` block in it becomes a live example: the project on the left, and on the right the source after expansion with the generated lines marked, the JavaScript, the compiler's trees, and the program's output. |
| `implementation.html` | [docs/comptime/IMPLEMENTATION.md](../docs/comptime/IMPLEMENTATION.md). |
| `playground.html` | The full playground: any number of files, share links. |

The examples on the RFC page show a result that was built with the site, so
the page reads without loading the compiler; it is loaded when an example is
edited or its trees are opened.

## Build

```bash
cd playground
npm ci
npm run build:wasm   # compiler-rust -> crate/pkg (needs wasm-pack and the wasm32-unknown-unknown target)
npm run smoke        # builds and runs every example with the wasm compiler, in Node
npm run build        # builds the examples for the RFC page, then the static site in dist/
```

`npm run dev` serves it with hot reload.

`dist/` is a static site with relative URLs: it works from any path of any
static host. The `Macros playground` workflow builds it and deploys it to
GitHub Pages when it is started by hand.

The standard library comes from `packages/@rescript/runtime`: its sources are
type checked on demand, and its compiled modules in `lib/es6` are what macros
and the compiled program import. `npm run build` bundles both into
`public/stdlib.json`.

## Layout

| Path | What |
| --- | --- |
| `crate/` | The wasm-bindgen entry points: `compile_file`, the virtual file system, and the macro host that calls into the page. |
| `src/engine.js` | The build: file order, compiling, running macros and the program. No dependency on the page; `scripts/smoke.mjs` runs it in Node. |
| `src/rfc/` | The RFC pages: the Markdown renderer, the live example, the diagrams. `scripts/prebuild-examples.mjs` writes the results they start from. |
| `src/compiler-worker.js`, `src/compiler-client.js` | The worker the compiler runs in, and the page's side: a build that takes more than 20 seconds is stopped by replacing the worker. |
| `src/App.jsx` | The page. |
| `examples/` | The example projects, listed in `examples/index.json`. `compiler-rust/tests/macros.rs` compiles all of them; the RFC page and the playground both show them. |

## Adding an example

Add a directory under `examples/` with the files, and an entry in
`examples/index.json`. List a file after the files it uses. A file that is
not `.res` is not compiled: macros read it with `Macro.readFile`.
