#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
bold "Test: OTLP export leaves the console at the CLI verbosity"
node --input-type=module <<'JS'
import assert from "node:assert/strict";
import fs from "node:fs";
import http from "node:http";
import os from "node:os";
import path from "node:path";
import {spawn} from "node:child_process";

// A collector that keeps every OTLP request body.
const bodies = [];
const collector = http.createServer((req, res) => {
  const chunks = [];
  req.on("data", chunk => chunks.push(chunk));
  req.on("end", () => {
    bodies.push(Buffer.concat(chunks));
    res.writeHead(200, {"Content-Type": "application/x-protobuf"});
    res.end();
  });
});
await new Promise(resolve => collector.listen(0, "127.0.0.1", resolve));
const endpoint = `http://127.0.0.1:${collector.address().port}`;

const env = {...process.env, OTEL_EXPORTER_OTLP_ENDPOINT: endpoint};
// The exported level defaults to debug; the console's follows -v/-vv only.
delete env.RUST_LOG;
const root = fs.mkdtempSync(path.join(os.tmpdir(), "rescript-otel-console-"));
function build(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.env.REWATCH_EXECUTABLE, [...args, "build"], {
      cwd: root,
      env,
      timeout: 10000,
    });
    let output = "";
    child.stdout.on("data", data => (output += data));
    child.stderr.on("data", data => (output += data));
    child.on("error", reject);
    child.on("close", status => {
      assert.equal(status, 0, output);
      resolve(output);
    });
  });
}
try {
  fs.mkdirSync(path.join(root, "src"));
  fs.writeFileSync(path.join(root, "rescript.json"), JSON.stringify({
    name: "otel-console", sources: "src",
  }));
  fs.writeFileSync(path.join(root, "src/A.res"), "let x = 1\n");

  const quiet = await build([]);
  assert.match(quiet, /Finished compilation/);
  assert.doesNotMatch(quiet, /debug/i, "default verbosity prints no debug logs");
  const exported = Buffer.concat(bodies).toString("latin1");
  assert.match(exported, /Parsing package: otel-console/, "debug logs are still exported");

  const verbose = await build(["-vv"]);
  assert.match(verbose, /^debug: Parsing package: otel-console$/m, "-vv prints debug logs");
} finally {
  collector.close();
  fs.rmSync(root, {recursive: true});
}
JS
success "OTLP export does not change the console verbosity"
