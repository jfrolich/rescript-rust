#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
bold "Test: Location-free compilation matches a location-enabled build"
node --input-type=module <<'JS'
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {spawnSync} from "node:child_process";

const root = fs.mkdtempSync(path.join(os.tmpdir(), "rescript-location-retry-"));
const src = path.join(root, "src");
fs.mkdirSync(src);
const executable = process.env.REWATCH_EXECUTABLE;
const config = {
  name: "location-retry", sources: "src",
  "package-specs": {module: "esmodule", "in-source": true}, suffix: ".res.js",
  warnings: {number: "+26", error: "-a"},
};
// Unit names only: compiled without a located retry.
const nameOnly = "let file = __FILE__\nlet unit = __MODULE__\n" +
  "let qualified = Pervasives.__FILE__ ++ Pervasives.__MODULE__\n" +
  "let shadowed = {\n  let __LINE__ = 7\n  let __LOC__ = \"mine\"\n  (__LINE__, __LOC__)\n}\n" +
  "module P = {\n  let __POS__ = 1\n}\nlet viaModule = P.__POS__\n";
const cases = [
  ["clean", {"A.res": "let f = x => x + 1\n", "B.res": "let answer = A.f(41)\n"}, 0],
  ["location constants and assertions", {
    "A.res": "let file = __FILE__\nlet line = __LINE__\nlet loc = __LOC__\nlet pos = __POS__\nlet check = x => assert(x > 0)\n",
    "B.res": "let value = A.line\n",
  }, 0],
  ["unit names, shadowed and qualified location names", {
    "A.res": nameOnly, "B.res": "let value = A.file ++ A.qualified\n",
  }, 0],
  ["shadowed unused binding", {
    "A.res": "let f = () => {\n let x = 1\n let x = 2\n x\n}\n", "B.res": "let answer = A.f()\n",
  }, 0],
  ["cross-module error", {
    "A.res": "type t = {a: int}\nlet f = (x: t) => x.a\n", "B.res": 'let x = A.f({a: "wrong"})\n',
  }, 1],
  ["interface error", {"A.res": 'let a = "wrong"\n', "A.resi": "let a: int\n", "B.res": "let a = A.a\n"}, 1],
  ["syntax error", {"A.res": "let f = (x => x\n", "B.res": "let answer = A.f(41)\n"}, 1],
];
function run(args) {
  const result = spawnSync(executable, args, {cwd: root, encoding: "utf8", timeout: 30000});
  assert.ifError(result.error);
  return result;
}
function outputs() {
  return Object.fromEntries(fs.readdirSync(src).filter(f => f.endsWith(".res.js")).sort()
    .map(f => [f, fs.readFileSync(path.join(src, f), "utf8")]));
}
try {
  for (const [name, sources, status] of cases) {
    for (const file of fs.readdirSync(src)) fs.unlinkSync(path.join(src, file));
    for (const [file, content] of Object.entries(sources)) fs.writeFileSync(path.join(src, file), content);
    fs.writeFileSync(path.join(root, "rescript.json"), JSON.stringify(config));
    assert.equal(run(["clean"]).status, 0);
    const fast = run(["build"]);
    const fastOutputs = outputs();
    assert.equal(fast.status, status, `${name}: ${fast.stderr}`);
    assert.equal(run(["clean"]).status, 0);
    // Dumps explicitly require locations, and force a fresh complete build.
    const located = run(["build", "--dump", "rawlambda", "--dump-dir", path.join(root, "dumps")]);
    assert.equal(located.status, fast.status, name);
    assert.equal(fast.stderr, located.stderr, `${name}: diagnostic mismatch`);
    assert.deepEqual(fastOutputs, outputs(), `${name}: JavaScript mismatch`);
    assert.ok(!fast.stderr.includes("requires source locations"), name);
    if (name === "shadowed unused binding") assert.match(fast.stderr, /unused/i);
  }
  // `-vv` logs each located retry; unit names alone must not cause one,
  // while a line number still does.
  for (const [sources, retries] of [[nameOnly, false], ["let line = __LINE__\n", true]]) {
    for (const file of fs.readdirSync(src)) fs.unlinkSync(path.join(src, file));
    fs.writeFileSync(path.join(src, "A.res"), sources);
    assert.equal(run(["clean"]).status, 0);
    const verbose = run(["-vv", "build"]);
    assert.equal(verbose.status, 0, verbose.stderr);
    const log = verbose.stdout + verbose.stderr;
    assert.equal(/Retrying .* with source locations/.test(log), retries, log);
  }
} finally {
  fs.rmSync(root, {recursive: true});
}
JS
success "Location-free output and diagnostic retries match located compilation"
