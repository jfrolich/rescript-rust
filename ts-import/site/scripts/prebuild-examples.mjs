#!/usr/bin/env node
/**
 * Builds every example with the WebAssembly compiler and writes what the page
 * shows before the compiler has loaded in the browser. An example that does
 * not compile fails the build, unless it is marked `"fails": true`.
 */
import { readFile, writeFile } from "fs/promises";
import { join } from "path";
import { createEngine } from "../src/engine.js";

const root = join(import.meta.dirname, "..");
const module = await WebAssembly.compile(await readFile(join(root, "public/compiler.wasm")));
const stdlib = JSON.parse(await readFile(join(root, "public/stdlib.json"), "utf-8"));
const engine = createEngine(module, stdlib);

const prebuilt = {};
for (const example of JSON.parse(await readFile(join(root, "examples/index.json"), "utf-8"))) {
  const files = [];
  for (const name of example.files) {
    files.push({ name, source: await readFile(join(root, "examples", example.id, name), "utf-8") });
  }
  const started = performance.now();
  const result = engine.build(files, { full: Boolean(example.compare) });
  const ms = Math.round(performance.now() - started);
  if (result.crashed || (result.type !== "success") !== Boolean(example.fails)) {
    console.error(`${example.id}: ${result.crashed ?? result.message ?? "compiled, but is marked as failing"}`);
    process.exit(1);
  }
  console.log(`${example.id}: ${result.type} in ${ms} ms, ${result.imports.length} imports, ${result.stats?.types} types`);
  prebuilt[example.id] = result;
}
await writeFile(join(root, "src/prebuilt.json"), JSON.stringify(prebuilt));
console.log(`Prebuilt ${Object.keys(prebuilt).length} examples -> src/prebuilt.json`);
