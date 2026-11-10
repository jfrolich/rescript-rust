#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
bold "Test: Clean builds write the same build record whatever the worker count"
node --no-warnings --input-type=module <<'JS'
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {spawnSync} from "node:child_process";
import {DatabaseSync} from "node:sqlite";

const root = fs.mkdtempSync(path.join(os.tmpdir(), "rescript-deterministic-records-"));
const src = path.join(root, "src");
fs.mkdirSync(src);
const executable = process.env.REWATCH_EXECUTABLE;
fs.writeFileSync(path.join(root, "rescript.json"), JSON.stringify({
  name: "deterministic-records", sources: "src",
  "package-specs": {module: "esmodule", "in-source": true}, suffix: ".res.js",
}));

const sources = {
  // Independent modules aliasing the same unit: what a module that reads
  // only `Shared` records must not depend on which of them compiled first.
  "Shared.res": "type t = {a: int}\nlet make = a => {a: a}\n",
  // A functor applied in other modules: the result signatures they publish
  // mention identifiers of the functor's signature.
  "Event.res": "module type Intf = {\n  type detail\n  let name: string\n}\n" +
    "module Make = (E: Intf) => {\n  let name = E.name\n  type payload = {detail: E.detail}\n" +
    "  let make = detail => {detail: detail}\n  module Target = {\n" +
    "    let get = (p: payload) => p.detail\n  }\n}\n",
};
for (let i = 0; i < 6; i++) {
  sources[`Alias${i}.res`] = `module S = Shared\nlet x: S.t = S.make(${i})\n`;
  sources[`Reader${i}.res`] = `let read = (x: Shared.t) => x.a + ${i}\n`;
  sources[`Applied${i}.res`] =
    `module E = Event.Make({\n  type detail = int\n  let name = "e${i}"\n})\n` +
    `include Event.Make({\n  type detail = string\n  let name = "i${i}"\n})\n` +
    `let p = E.make(${i})\n`;
}
for (const [file, content] of Object.entries(sources)) fs.writeFileSync(path.join(src, file), content);

function run(args, threads) {
  const result = spawnSync(executable, args, {
    cwd: root, encoding: "utf8", timeout: 60000,
    env: {...process.env, RAYON_NUM_THREADS: String(threads)},
  });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
  return result;
}

// Every table of the record, leaving out times (when the build started, when
// each module's JavaScript was confirmed, source modification times).
function dump() {
  const db = new DatabaseSync(path.join(root, "lib", "bs", "rescript.sqlite"), {readOnly: true});
  try {
    const rows = {};
    const tables = db.prepare("SELECT name FROM sqlite_master WHERE type = 'table' ORDER BY name").all();
    for (const {name} of tables) {
      const select = db.prepare(`SELECT * FROM ${name} ORDER BY 1`);
      select.setReadBigInts(true);
      rows[name] = select.all().map(row => {
        const copy = {};
        for (const [column, value] of Object.entries(row)) {
          if (column === "js_confirmed_at" || column === "mtime") continue;
          if (name === "meta" && column === "value" && /_at$|started/.test(row.key)) continue;
          copy[column] = value instanceof Uint8Array ? Buffer.from(value).toString("hex") : value;
        }
        return copy;
      });
    }
    return rows;
  } finally {
    db.close();
  }
}

try {
  let first;
  for (const threads of [1, 8, 3, 8, 1]) {
    run(["clean"], threads);
    run(["build"], threads);
    const record = dump();
    if (first === undefined) {
      first = record;
      assert.ok(first.interfaces.length > 0, "the record stores interfaces");
    } else {
      for (const table of Object.keys(first)) {
        assert.deepEqual(record[table], first[table], `table ${table} differs with ${threads} threads`);
      }
    }
  }
} finally {
  fs.rmSync(root, {recursive: true});
}
JS
success "Clean builds write the same build record"
