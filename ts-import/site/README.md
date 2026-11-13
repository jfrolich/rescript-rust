# The page of docs/ts-import

Renders `docs/ts-import/README.md` with its examples live: each
`<!-- example: id -->` block is replaced by the example `examples/<id>`,
compiled in the browser.

The compiler is `crate/`: the Rust compiler with `%ts` imports and the
TypeScript checker, built for `wasm32-wasip1`. `src/engine.js` supplies the
few WASI calls it needs; it has no file system, the files of an example come
in with each request.

```sh
npm ci
npm run build:wasm   # public/compiler.wasm, about 18 MB
npm run build        # dist/, with relative URLs: serve it from any path
npm run dev
```

`npm run build` first compiles every example with the WebAssembly module
(`scripts/prebuild-examples.mjs`), so that the page shows results before the
compiler has loaded, and fails if an example does not compile. Set
`VITE_PULL_REQUEST` to link the page to a pull request.

`classes.html` is a second page from the same parts: it renders
`docs/class-identity/README.md`. Its examples have no TypeScript files and are
marked `"plain": true`, which leaves only the JavaScript (or the error) on the
right. To publish it on its own, serve `dist/classes.html` as the index of a
directory beside `dist/assets`, `compiler.wasm` and `stdlib.json`.

An example is listed in `examples/index.json`: its files (the last one is the
ReScript file), `"fails": true` when it is meant not to compile, `"compare":
true` to also run a full TypeScript check for comparison, and `"view"` for the
tab that is open at first.
