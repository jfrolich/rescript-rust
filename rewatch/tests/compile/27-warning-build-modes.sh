#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
bold "Test: Parse warnings occur once in every build mode"
node --input-type=module <<'JS'
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {spawnSync} from "node:child_process";

const root = fs.mkdtempSync(path.join(os.tmpdir(), "rescript-warning-modes-"));
function run(args, env = {}) {
  const result = spawnSync(process.env.REWATCH_EXECUTABLE, args, {
    cwd: root, encoding: "utf8", timeout: 10000, env: {...process.env, ...env},
  });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stdout + result.stderr);
}
function log() {
  return fs.readFileSync(path.join(root, "lib/rescript/.compiler.log"), "utf8")
    .split("\n").filter(line => !line.startsWith("#")).join("\n");
}
try {
  fs.mkdirSync(path.join(root, "src"));
  fs.writeFileSync(path.join(root, "rescript.json"), JSON.stringify({
    name: "warning-modes", sources: "src", warnings: {error: "-a"},
  }));
  const source = path.join(root, "src/A.res");
  fs.writeFileSync(source, 'let f = () => %todo("later")\n\n\n\n\n');
  run(["build"], {RESCRIPT_FULL_BUILD: "1"});
  const expected = log();
  assert.equal((expected.match(/Todo found: later/g) ?? []).length, 1);
  // Change content rather than mtime: incremental planning hashes sources.
  fs.appendFileSync(source, "\n");
  run(["build"]);
  assert.equal(log(), expected, "incremental parse rounds");
  run(["build"]);
  assert.equal(log(), expected, "replayed warnings");
  run(["clean"]);
  assert.ok(!fs.existsSync(path.join(root, "lib/rescript/rescript.sqlite")));
  run(["build"]);
  assert.equal(log(), expected, "clean build");
  run(["build", "--dump", "lambda", "--dump-dir", path.join(root, "dumps")]);
  assert.equal(log(), expected, "located build");
} finally {
  fs.rmSync(root, {recursive: true});
}
JS
success "Warning logs match across build modes"
