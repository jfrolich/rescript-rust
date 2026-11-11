#!/usr/bin/env node
/**
 * Builds every example with the wasm compiler and writes what the RFC page
 * shows before the compiler has loaded in the browser: per file the expanded
 * source and the JavaScript, and the program's output.
 */
import { readFile, writeFile } from "fs/promises";
import { join } from "path";
import * as wasm from "../crate/pkg/rescript_playground_wasm.js";
import { createEngine } from "../src/engine.js";

const root = join(import.meta.dirname, "..");
wasm.initSync({ module: await readFile(join(root, "crate/pkg/rescript_playground_wasm_bg.wasm")) });
const stdlib = JSON.parse(await readFile(join(root, "public/stdlib.json"), "utf-8"));
const engine = createEngine(wasm, stdlib);

const prebuilt = {};
for (const example of JSON.parse(await readFile(join(root, "examples/index.json"), "utf-8"))) {
  const files = [];
  for (const name of example.files) {
    files.push({ name, source: await readFile(join(root, "examples", example.id, name), "utf-8") });
  }
  const { order, results, logs } = engine.build(files);
  const failed = order.find((name) => results[name]?.type !== "success");
  if (failed || logs === null) {
    console.error(`${example.id}: ${failed} does not compile\n${results[failed]?.message}`);
    process.exit(1);
  }
  prebuilt[example.id] = {
    order,
    logs,
    results: Object.fromEntries(
      order.map((name) => [
        name,
        {
          type: "success",
          js: results[name].js,
          expanded: results[name].expanded ?? null,
          formatted: results[name].formatted ?? null,
          warnings: "",
        },
      ]),
    ),
  };
}
await writeFile(join(root, "src/rfc/prebuilt.json"), JSON.stringify(prebuilt));
console.log(`Prebuilt ${Object.keys(prebuilt).length} examples -> src/rfc/prebuilt.json`);
