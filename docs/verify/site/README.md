# The pages of docs/verify

Renders the documents of `docs/verify` with their examples live: each
`<!-- example: id -->` block of a document is replaced by the example
`examples/<id>.res`, compiled in the browser.

The compiler is `crate/`: the Rust compiler built for `wasm32-wasip1`.
`src/engine.js` supplies the few WASI calls it needs; it has no file system,
the file of an example comes in with each request, and the standard library
is type checked from its sources (`public/stdlib.json`).

```sh
npm ci
npm run build:wasm   # public/compiler.wasm, about 10 MB
npm run build        # dist/, with relative URLs: serve it from any path
npm run dev
```

`npm run build` first compiles every example with the WebAssembly module
(`scripts/prebuild-examples.mjs`), so that a page shows results before the
compiler has loaded, and fails when an example does not behave as
`examples/index.json` says: `"fails": true` for one the compiler is meant to
reject, `"report"` for a sentence its report must contain, and `"expected"`
for the sentence shown above the report. Set `VITE_PULL_REQUEST` to link the
pages to a pull request.

There is one page per document: `index.html` is `README.md`, `pure.html` is
`pure.md`, `law.html` is `law.md`, `spec.html` is `spec.md` and `proof.html` is
`proof.md`. A host that serves `pure.html` as
`/pure` works as well: every URL in the pages is relative.

An example marked `"checks": true` is also verified: the compiler module
compiles it once more with its laws and specs kept, and the page runs them with the
runner of `rescript verify` (`rewatch/src/verify/runner.mjs`) against the
runtime's compiled modules, which `public/stdlib.json` carries. `"failing"`
names the checks that are meant to fail.
