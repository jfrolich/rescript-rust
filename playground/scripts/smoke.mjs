#!/usr/bin/env node
/**
 * Builds every example of the playground with the wasm compiler, in Node,
 * and prints what the page would show. Fails when an example does not
 * compile or its program raises.
 *
 * It also runs the session the read-eval-print loop of the RFC page opens
 * with, and the inputs it offers after that: none may fail, and the opening
 * session has to be the transcript docs/comptime/README.md shows
 * (`--write-transcript` puts it there). After that session it asks for the
 * completions of examples/repl.json, and for some in a file of a project.
 *
 *   node scripts/smoke.mjs [example-id] [--show] [--write-transcript]
 */
import { readFile, writeFile } from "fs/promises";
import { join } from "path";
import * as wasm from "../crate/pkg/rescript_playground_wasm.js";
import { createEngine } from "../src/engine.js";
import { runSession, sessionLibraries, transcriptOf } from "../src/repl-transcript.js";

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

if (!only) {
  const session = JSON.parse(await readFile(join(root, "examples/repl.json"), "utf-8"));
  const inputs = [...session.intro, ...session.tries.map((entry) => entry.source)];
  const started = performance.now();
  const entries = await runSession(engine, sessionLibraries(examples), inputs);
  const broken = entries.filter((entry) => entry.output.some((line) => line.kind === "problem" || line.kind === "warn"));
  console.log(`${broken.length === 0 ? "ok  " : "FAIL"} repl (${Math.round(performance.now() - started)} ms)`);
  if (showAll || broken.length > 0) console.log(transcriptOf(showAll ? entries : broken));
  failed ||= broken.length > 0;

  // A function prints where it is called, not where it was defined.
  const printed = await runSession(engine, [], ['let shout = text => Console.log(text ++ "!")', 'shout("hi")']);
  const wanted = '> let shout = text => Console.log(text ++ "!")\nlet shout: string => unit = <fun>\n\n> shout("hi")\nhi!\n- : unit = ()';
  const same = transcriptOf(printed) === wanted;
  console.log(`${same ? "ok  " : "FAIL"} repl output of a function of an earlier input${same ? "" : `\n${transcriptOf(printed)}`}`);
  failed ||= !same;
  engine.replStart(sessionLibraries(examples));
  for (const input of inputs) await engine.replEval(input);

  // What the editors offer after those inputs, and in a file of a project.
  const missing = [];
  const offered = (request, label) => {
    const result = engine.complete(request);
    if (result?.crashed || !result?.options.some((option) => option.label === label)) {
      missing.push(`${JSON.stringify(request.source ?? request.name)}: ${label} is not offered`);
    }
  };
  for (const [source, label] of session.completions) offered({ mode: "repl", source, offset: source.length }, label);
  const project = examples.find((example) => example.id === "json");
  const written = (name, text) => {
    const files = project.files.map((file) => (file.name === name ? { ...file, source: file.source + text } : file));
    return { mode: "project", files, name, offset: files.find((file) => file.name === name).source.length };
  };
  offered(written("Main.res", "\nlet n = alice."), "avatar");
  offered(written("Main.res", "\nlet n = team->"), "Array.map");
  offered(written("Json.res", "\nlet f = (field: Type.field) => field."), "jsName");
  console.log(`${missing.length === 0 ? "ok  " : "FAIL"} completions${missing.map((line) => `\n  ${line}`).join("")}`);
  failed ||= missing.length > 0;

  // The opening session is in the RFC as text.
  const readmePath = join(root, "../docs/comptime/README.md");
  const readme = await readFile(readmePath, "utf-8");
  const block = /(<!-- repl -->\n\n```text\n)([\s\S]*?)(\n```\n\n<!-- \/repl -->)/;
  const transcript = transcriptOf(entries.slice(0, session.intro.length));
  const found = readme.match(block);
  if (process.argv.includes("--write-transcript") && found) {
    await writeFile(readmePath, readme.replace(block, (_, before, _old, after) => before + transcript + after));
    console.log("ok   repl transcript written to docs/comptime/README.md");
  } else if (!found || found[2] !== transcript) {
    console.log(`FAIL repl transcript: docs/comptime/README.md does not show this session\n${transcript}`);
    failed = true;
  } else {
    console.log("ok   repl transcript");
  }
}
process.exit(failed ? 1 : 0);
