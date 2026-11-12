// Compare the Rust editor analysis (`rescript analysis test <file>`, served by
// a running `rescript watch`) with the OCaml analysis snapshots in
// src/expected and not_compiled/expected.
//
// The snapshots are `rescript-editor-analysis test <file>` output: one block
// per `//^xxx` directive. This script splits both outputs into those blocks
// and compares them directive by directive. Directives the Rust analysis does
// not implement are counted as unsupported, never as passing; so are hovers
// OCaml answers through its completion engine (`hov(completion)`), which the
// Rust analysis does not have.
//
// Usage:
//   node rust-analysis.mjs run <results.jsonl>   (in a project, under with-watcher.sh)
//   node rust-analysis.mjs summary <results.jsonl>
//
// With RUST_ANALYSIS_DUMP=<dir>, `run` also writes each file's Rust output
// to <dir>/<project>/<file>.txt.
//
// `run` appends one JSON line per directive to the results file and prints
// the differences; `summary` prints the per-directive table and exits 1 when
// a supported directive differs or a file fails.

// @ts-check

import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";
import { rescript_exe } from "../../cli/common/bins.js";

/** Directives that only set a flag: OCaml prints nothing but a newline. */
const CONTROL = new Set(["db+", "db-", "dv+", "dv-", "in+", "in-"]);

/**
 * What a hover prints when nothing is at the position: OCaml then hovers
 * through its completion engine (Hover.get_hover_via_completions), which the
 * Rust analysis does not have, so Rust answers null.
 */
const HOVER_VIA_COMPLETION =
  "Nothing at that position. Now trying to use completion.";

/**
 * The header line `rescript-editor-analysis test` prints before a directive's
 * output (analysis/src/cli.ml), or a predicate for it; `null` when the
 * directive prints no header.
 * @param {string} cmd
 * @param {string} rest
 * @param {string} file
 * @param {number} line
 * @param {number} col
 * @returns {null | ((l: string) => boolean)}
 */
function header(cmd, rest, file, line, col) {
  const at = `${file} ${line}:${col}`;
  const exact = (/** @type {string} */ s) => (/** @type {string} */ l) =>
    l === s;
  switch (cmd) {
    case "def":
      return exact(`Definition ${at}`);
    case "com":
      return exact(`Complete ${at}`);
    case "cre":
      return exact(`Completion resolve: ${rest.slice(3).trim()}`);
    case "dce":
      return exact(`DCE ${file}`);
    case "doc":
      return exact(`DocumentSymbol ${file}`);
    case "hig":
      return exact(`Highlight ${file}`);
    case "hov":
      return exact(`Hover ${at}`);
    case "she":
      return exact(`Signature help ${at}`);
    case "int":
      return exact(`Create Interface ${file}`);
    case "ref":
      return exact(`References ${at}`);
    case "pre":
      return exact(`PrepareRename ${at}`);
    case "ren":
      return exact(`Rename ${at} ${rest.slice(4)}`);
    case "typ":
      return exact(`TypeDefinition ${at}`);
    case "xfm":
      return l => l.startsWith(`Xform ${file} `);
    case "c-a":
      return exact(`Codemod AddMissingCases${at}`);
    case "hin":
      return exact(`Inlay Hint ${file} 1:34`);
    case "cle":
      return exact(`Code Lens ${file}`);
    case "ast":
      return exact(`Dump AST ${at}`);
    default:
      // dia, sem, the control directives and unknown ones.
      return null;
  }
}

/**
 * The directives of a test file, as `Cli.test` finds them.
 * @param {string} file
 */
function directives(file) {
  const text = fs.readFileSync(file, "latin1");
  /** @type {{cmd: string, line: number, col: number, header: null | ((l: string) => boolean)}[]} */
  const found = [];
  text.split("\n").forEach((l, i) => {
    const m = /^ *\/\/[ ]*\^/.exec(l);
    if (!m || m[0].length < 3) return;
    const mlen = m[0].length;
    const rest = l.slice(mlen);
    const cmd = rest.slice(0, 3);
    const line = i - 1;
    const col = mlen - 1;
    found.push({ cmd, line, col, header: header(cmd, rest, file, line, col) });
  });
  return found;
}

/**
 * The marker line Rust prints for a directive it does not implement.
 * @param {string} cmd
 */
const unsupportedLine = cmd =>
  `\`${cmd}\` is not available inside the watcher yet`;

/**
 * Split `lines` into one block per directive. A block starts after the
 * directive's marker line (its header, or for the Rust output the
 * unsupported line) and ends at the next directive's marker. Directives
 * without a header get no block of their own.
 * @param {string[]} lines
 * @param {ReturnType<typeof directives>} ds
 * @param {boolean} rust
 */
function blocks(lines, ds, rust) {
  /** @type {{start: number, unsupported: boolean} | null}[]} */
  const starts = [];
  let cursor = 0;
  for (const d of ds) {
    const unsupported = unsupportedLine(d.cmd);
    if (CONTROL.has(d.cmd)) {
      starts.push(null);
      continue;
    }
    const isMarker = (/** @type {string} */ l) =>
      d.header?.(l) || (rust && l === unsupported);
    if (d.header === null && !rust) {
      starts.push(null);
      continue;
    }
    let i = cursor;
    while (i < lines.length && !isMarker(lines[i])) i++;
    if (i === lines.length) {
      starts.push(null);
      continue;
    }
    starts.push({ start: i, unsupported: rust && lines[i] === unsupported });
    cursor = i + 1;
  }
  const markers = starts.flatMap(s => (s ? [s.start] : []));
  return starts.map(s => {
    if (!s) return null;
    const next = markers.find(m => m > s.start) ?? lines.length;
    const body = lines.slice(s.start + 1, next);
    while (body.length > 0 && body[body.length - 1] === "") body.pop();
    return { unsupported: s.unsupported, text: body.join("\n") };
  });
}

/**
 * @param {string} resultsFile
 */
function run(resultsFile) {
  const project = path.basename(process.cwd());
  const files = ["src", "not_compiled"].flatMap(dir =>
    fs.existsSync(dir)
      ? fs
          .readdirSync(dir)
          .filter(f => f.endsWith(".res") || f.endsWith(".resi"))
          .sort()
          .map(f => `${dir}/${f}`)
      : [],
  );
  let differences = 0;
  /** @type {string[]} */
  const out = [];
  for (const file of files) {
    const ds = directives(file);
    if (ds.length === 0) continue;
    const snapshot = path.join(
      path.dirname(file),
      "expected",
      `${path.basename(file)}.txt`,
    );
    const expectedText = fs.existsSync(snapshot)
      ? fs.readFileSync(snapshot, "latin1")
      : null;
    const result = spawnSync(rescript_exe, ["analysis", "test", file], {
      encoding: "latin1",
      timeout: 60_000,
    });
    const dump = process.env.RUST_ANALYSIS_DUMP;
    if (dump) {
      const target = path.join(dump, project, `${file}.txt`);
      fs.mkdirSync(path.dirname(target), { recursive: true });
      fs.writeFileSync(target, result.stdout + result.stderr, "latin1");
    }
    const failed =
      result.status !== 0 ? `exit ${result.status}: ${result.stderr}` : null;
    const expected =
      expectedText === null
        ? null
        : blocks(expectedText.split("\n"), ds, false);
    const actual = failed ? null : blocks(result.stdout.split("\n"), ds, true);
    ds.forEach((d, i) => {
      /** @type {string} */
      let status;
      let cmd = d.cmd;
      const viaCompletion =
        d.cmd === "hov" &&
        expected?.[i]?.text.startsWith(`${HOVER_VIA_COMPLETION}\n`) &&
        actual?.[i]?.text === `${HOVER_VIA_COMPLETION}\nnull` &&
        expected[i]?.text !== actual[i]?.text;
      if (viaCompletion) cmd = "hov(completion)";
      if (CONTROL.has(d.cmd)) status = "control";
      else if (failed) status = "error";
      else if (!actual?.[i]) status = "missing";
      else if (actual[i]?.unsupported || viaCompletion) status = "unsupported";
      else if (!expected?.[i]) status = "no-snapshot";
      else if (expected[i]?.text === actual[i]?.text) status = "match";
      else status = "differ";
      const record = { project, file, cmd, line: d.line, col: d.col, status };
      fs.appendFileSync(resultsFile, `${JSON.stringify(record)}\n`);
      if (
        status === "differ" ||
        status === "missing" ||
        status === "no-snapshot"
      ) {
        differences++;
        out.push(
          `--- ${project}/${file} ${d.cmd} ${d.line}:${d.col}: ${status}`,
        );
        if (status === "differ") {
          out.push("expected (OCaml snapshot):", expected?.[i]?.text ?? "");
          out.push("actual (Rust):", actual?.[i]?.text ?? "");
        }
      }
    });
    if (failed) {
      differences++;
      out.push(`--- ${project}/${file}: ${failed.trim()}`);
    }
  }
  if (out.length > 0) console.log(out.join("\n"));
  console.log(`${project}: ${differences} problem(s)`);
}

/**
 * @param {string} resultsFile
 */
function summary(resultsFile) {
  const records = fs
    .readFileSync(resultsFile, "utf8")
    .split("\n")
    .filter(Boolean)
    .map(l => JSON.parse(l));
  const columns = [
    "run",
    "match",
    "differ",
    "unsupported",
    "error",
    "missing",
    "no-snapshot",
    "control",
  ];
  /** @type {Map<string, Record<string, number>>} */
  const rows = new Map();
  const total = Object.fromEntries(columns.map(c => [c, 0]));
  for (const r of records) {
    let row = rows.get(r.cmd);
    if (!row) {
      row = Object.fromEntries(columns.map(c => [c, 0]));
      rows.set(r.cmd, row);
    }
    for (const target of [row, total]) {
      target[r.status]++;
      if (r.status !== "unsupported" && r.status !== "control") target.run++;
    }
  }
  const sorted = [...rows.entries()].sort(([a], [b]) => a.localeCompare(b));
  const width = 12;
  const pad = (/** @type {string | number} */ s) => String(s).padStart(width);
  console.log(["directive".padEnd(16), ...columns.map(pad)].join(""));
  for (const [cmd, row] of [...sorted, ["total", total]]) {
    console.log(
      [String(cmd).padEnd(16), ...columns.map(c => pad(row[c]))].join(""),
    );
  }
  const failures =
    total.differ + total.error + total.missing + total["no-snapshot"];
  if (failures > 0) {
    console.log(
      `\n${failures} supported directive(s) differ from the OCaml snapshots.`,
    );
    process.exit(1);
  }
  console.log(
    "\nEvery directive the Rust analysis supports matches the OCaml snapshots.",
  );
}

const [mode, resultsFile] = process.argv.slice(2);
if (mode === "run" && resultsFile) run(path.resolve(resultsFile));
else if (mode === "summary" && resultsFile) summary(resultsFile);
else {
  console.error("usage: node rust-analysis.mjs run|summary <results.jsonl>");
  process.exit(2);
}
