#!/usr/bin/env node
// Exercise the same web-target wasm bundle used by the playground, in Node.
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import init, * as compiler from "../crate/pkg/rescript_playground_wasm.js";

await init({
  module_or_path: await readFile(
    new URL("../crate/pkg/rescript_playground_wasm_bg.wasm", import.meta.url)
  ),
});
compiler.vfs_clear();
const runtime = new URL("../../packages/@rescript/runtime/", import.meta.url);
const runtimeFiles = await readdir(runtime);
for (const name of runtimeFiles) {
  if (!/\.resi?$/.test(name)) continue;
  const path = `/stdlib/${name}`;
  compiler.vfs_write_file(path, await readFile(new URL(name, runtime), "utf8"));
  // Prefer an interface when both source forms exist.
  if (name.endsWith(".resi") || !runtimeFiles.includes(`${name}i`)) {
    compiler.register_source_module(name.replace(/\.resi?$/, ""), path);
  }
}

function compile(source, filename, expected = "success") {
  console.log(`Compiling ${filename}: ${source}`);
  compiler.vfs_write_file(filename, source);
  const result = JSON.parse(compiler.compile_all(source, filename));
  assert.equal(result.type, expected, JSON.stringify(result));
  if (expected === "success") assert.ok(result.js.length > 0);
  return result;
}

compile("let value = 1", "/src/First.res");
compile("let value: int = First.value", "/src/Second.res");
compile('let value = "updated"', "/src/First.res");
compile("let value: int = First.value", "/src/Second.res", "error");
compile("let value: string = First.value", "/src/Second.res");
compiler.vfs_clear();
compile("let value = First.value", "/src/Second.res", "error");
console.log("Wasm smoke passed: dependencies, changed export types, and registry reset");
