#!/usr/bin/env node
/**
 * Builds every example of the playground with the wasm compiler, in Node,
 * and prints what the page would show. Fails when an example does not
 * compile or its program raises.
 *
 *   node scripts/smoke.mjs [example-id] [--show]
 */
import { readFile } from "fs/promises";
import { join } from "path";
import * as wasm from "../crate/pkg/rescript_playground_wasm.js";
import { createEngine } from "../src/engine.js";

const root = join(import.meta.dirname, "..");
wasm.initSync({ module: await readFile(join(root, "crate/pkg/rescript_playground_wasm_bg.wasm")) });
const stdlib = JSON.parse(await readFile(join(root, "public/stdlib.json"), "utf-8"));
const engine = createEngine(wasm, stdlib);

const examples = [];
for (const example of JSON.parse(await readFile(join(root, "examples/index.json"), "utf-8"))) {
  const files = [];
  for (const name of example.files) {
    files.push({ name, source: await readFile(join(root, "examples", example.id, name), "utf-8") });
  }
  examples.push({ ...example, files });
}

const only = process.argv.slice(2).find((argument) => !argument.startsWith("--"));
const showAll = process.argv.includes("--show");
let failed = false;

for (const example of examples) {
  if (only && example.id !== only) continue;
  const started = performance.now();
  const { order, results, logs, crashed } = engine.build(example.files);
  const ms = Math.round(performance.now() - started);
  const errors = order.filter((name) => results[name]?.type !== "success");
  const raised = logs?.some((log) => log.text.startsWith("Uncaught"));
  const ok = !crashed && errors.length === 0 && !raised;
  console.log(`${ok ? "ok  " : "FAIL"} ${example.id} (${ms} ms)`);
  if (crashed) console.log(crashed);
  for (const name of order) {
    const result = results[name];
    if (!result) continue;
    if (result.type !== "success") console.log(`--- ${name}\n${result.message}`);
    else if (showAll || !ok) {
      if (result.expanded) console.log(`--- ${name} expanded\n${result.expanded}`);
      console.log(`--- ${name} js\n${result.js}`);
    }
    if (result.warnings) console.log(`--- ${name} warnings\n${result.warnings}`);
  }
  if (logs) console.log(logs.map((log) => `  | ${log.text}`).join("\n"));
  failed ||= !ok;
}
process.exit(failed ? 1 : 0);
