// @ts-check

// Diagnostics and warnings of code the built-in derive generates. Each
// fixture directory is built as a project that enables the derive
// (`ppx-flags`) together with support/Spice.res, the library the generated code
// calls, and the diagnostics the build writes to
// `lib/rescript/.compiler.log` are compared with the snapshot. A fixture that
// compiles has an empty snapshot unless it warns.
//
//   node input.js            check
//   node input.js update     regenerate the snapshots
//
// The OCaml compiler has no built-in derive, so there is no reference build:
// the snapshots record this compiler's output.

import { readdirSync, statSync } from "node:fs";
import * as fs from "node:fs/promises";
import * as os from "node:os";
import * as path from "node:path";
import { setup } from "#dev/process";
import { normalizeNewlines } from "#dev/utils";

const fixturesDir = path.join(import.meta.dirname, "fixtures");
const expectedDir = path.join(import.meta.dirname, "expected");
const supportDir = path.join(import.meta.dirname, "support");
const repoRoot = path.resolve(import.meta.dirname, "../../..");

const fixtures = readdirSync(fixturesDir)
  .filter(name => statSync(path.join(fixturesDir, name)).isDirectory())
  .sort();

const updateTests = process.argv.includes("update");

/** @type {NodeJS.ProcessEnv} */
const buildEnv = {
  // The projects live in a temporary directory, outside any node_modules.
  RESCRIPT_RUNTIME: path.join(repoRoot, "packages", "@rescript", "runtime"),
  ...process.env,
};

const projectConfig = {
  name: "super-errors-derived-fixture",
  sources: "src",
  "package-specs": { module: "esmodule", "in-source": true },
  suffix: ".res.js",
  // Every warning except 4: each generated match on `JSON.t` ends in a
  // catch-all, which that warning reports.
  warnings: { number: "+A-4" },
  "ppx-flags": ["ppx-spice"],
};

/**
 * @param {string} fixtureName
 * @param {string[]} projectDirs spellings of the project directory
 * @param {string} log
 * @return {string}
 */
function postProcessErrorOutput(fixtureName, projectDirs, log) {
  let result = log
    .split("\n")
    .filter(line => !/^#(Start|Done)\(\d+\)$/.test(line))
    .join("\n");
  for (const dir of projectDirs) {
    result = result
      .split(path.join(dir, "src") + path.sep)
      .join(`/.../fixtures/${fixtureName}/`);
  }
  return normalizeNewlines(result.trim());
}

/**
 * @param {string} fixtureName
 * @returns {Promise<{ fixtureName: string, failure: string | null }>}
 */
async function runFixture(fixtureName) {
  const fixtureDir = path.join(fixturesDir, fixtureName);
  const projectDir = await fs.mkdtemp(
    path.join(os.tmpdir(), `super-errors-derived-${fixtureName}-`),
  );
  try {
    await fs.mkdir(path.join(projectDir, "src"));
    for (const dir of [supportDir, fixtureDir]) {
      for (const name of await fs.readdir(dir)) {
        if (name.endsWith(".res") || name.endsWith(".resi")) {
          await fs.copyFile(
            path.join(dir, name),
            path.join(projectDir, "src", name),
          );
        }
      }
    }
    await fs.writeFile(
      path.join(projectDir, "rescript.json"),
      `${JSON.stringify(projectConfig, null, 2)}\n`,
    );

    const { execBuild } = setup(projectDir);
    const { stdout, stderr } = await execBuild([], { env: buildEnv });
    let log;
    try {
      log = await fs.readFile(
        path.join(projectDir, "lib", "rescript", ".compiler.log"),
        "utf-8",
      );
    } catch {
      return {
        fixtureName,
        failure: `The build of ${fixtureName} wrote no .compiler.log:\n${stdout}${stderr}`,
      };
    }
    const actualErrorOutput = postProcessErrorOutput(
      fixtureName,
      [projectDir, await fs.realpath(projectDir)],
      log,
    );
    const expectedFilePath = path.join(expectedDir, `${fixtureName}.expected`);

    if (updateTests) {
      await fs.writeFile(expectedFilePath, `${actualErrorOutput}\n`);
      return { fixtureName, failure: null };
    }

    let expectedErrorOutput;
    try {
      expectedErrorOutput = normalizeNewlines(
        (await fs.readFile(expectedFilePath, "utf-8")).trim(),
      );
    } catch {
      return {
        fixtureName,
        failure: `Missing expected snapshot for ${fixtureName} (run with 'update' to create)`,
      };
    }

    if (expectedErrorOutput === actualErrorOutput) {
      return { fixtureName, failure: null };
    }
    return {
      fixtureName,
      failure: [
        `The old and new error output for fixture ${fixtureName} aren't the same`,
        "\n=== Old:",
        expectedErrorOutput,
        "\n=== New:",
        actualErrorOutput,
      ].join("\n"),
    };
  } finally {
    await fs.rm(projectDir, { recursive: true, force: true });
  }
}

const concurrency = Math.max(1, os.availableParallelism());
let cursor = 0;
const results = new Array(fixtures.length);

await Promise.all(
  Array.from({ length: Math.min(concurrency, fixtures.length) }, async () => {
    while (true) {
      const i = cursor++;
      if (i >= fixtures.length) return;
      results[i] = await runFixture(fixtures[i]);
    }
  }),
);

let atLeastOneTaskFailed = false;
for (const { failure } of results) {
  if (failure !== null) {
    console.error(failure);
    atLeastOneTaskFailed = true;
  }
}
if (atLeastOneTaskFailed) {
  process.exit(1);
}
