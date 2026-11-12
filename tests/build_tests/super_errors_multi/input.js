// @ts-check

// Multi-file error fixtures. Each fixture directory is built as a small
// project with `rescript build`, the way users compile, and the diagnostics the
// build writes to `lib/rescript/.compiler.log` are compared with the snapshot. The
// compiler resolves interfaces, namespaces and dependency order itself, so the
// harness passes no per-file flags.
//
//   node input.js            check with the default (in-process) build
//   node input.js --ocaml    check with the OCaml reference compiler
//   node input.js update     regenerate snapshots with the OCaml reference
//
// The OCaml reference build is the hidden `rescript build-reference`, which
// runs $RESCRIPT_BSC_EXE (default: the dune build of the compiler) per file
// and writes the same `.compiler.log`.

import { existsSync, readdirSync, statSync } from "node:fs";
import * as fs from "node:fs/promises";
import * as os from "node:os";
import * as path from "node:path";
import { rescript_exe } from "#cli/bins";
import { setup } from "#dev/process";
import { normalizeNewlines } from "#dev/utils";

const fixturesDir = path.join(import.meta.dirname, "fixtures");
const expectedDir = path.join(import.meta.dirname, "expected");
const repoRoot = path.resolve(import.meta.dirname, "../../..");

const fixtures = readdirSync(fixturesDir)
  .filter(name => statSync(path.join(fixturesDir, name)).isDirectory())
  .sort();

const updateTests = process.argv.includes("update");
const useOcaml = updateTests || process.argv.includes("--ocaml");

/** @type {NodeJS.ProcessEnv} */
const buildEnv = {
  // The projects live in a temporary directory, outside any node_modules.
  RESCRIPT_RUNTIME: path.join(repoRoot, "packages", "@rescript", "runtime"),
  ...process.env,
};
/** @type {string | undefined} */
let ocamlBsc;
if (useOcaml) {
  ocamlBsc =
    process.env.RESCRIPT_BSC_EXE ??
    path.join(repoRoot, "_build", "install", "default", "bin", "bsc");
  if (!existsSync(ocamlBsc)) {
    console.error(
      `OCaml reference bsc not found at ${ocamlBsc}; build it with dune or set RESCRIPT_BSC_EXE.`,
    );
    process.exit(1);
  }
  // The OCaml compiles read the runtime's .cmi files: build it with the
  // OCaml bsc.
  const runtime = setup(repoRoot);
  const reference = await runtime.execBin(
    rescript_exe,
    ["build-reference", "--bsc", ocamlBsc, buildEnv.RESCRIPT_RUNTIME ?? ""],
    { env: buildEnv },
  );
  if (reference.status !== 0) {
    console.error(`OCaml reference build of the runtime failed:\n${reference.stderr}`);
    process.exit(1);
  }
}

const projectConfig = {
  name: "super-errors-multi-fixture",
  sources: "src",
  "package-specs": { module: "esmodule", "in-source": true },
  suffix: ".res.js",
  warnings: { number: "+A" },
  jsx: { version: 4 },
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
    result = result.split(path.join(dir, "src") + path.sep).join(
      `/.../fixtures/${fixtureName}/`,
    );
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
    path.join(os.tmpdir(), `super-errors-multi-${fixtureName}-`),
  );
  try {
    await fs.mkdir(path.join(projectDir, "src"));
    for (const name of await fs.readdir(fixtureDir)) {
      if (name.endsWith(".res") || name.endsWith(".resi")) {
        await fs.copyFile(
          path.join(fixtureDir, name),
          path.join(projectDir, "src", name),
        );
      }
    }
    await fs.writeFile(
      path.join(projectDir, "rescript.json"),
      `${JSON.stringify(projectConfig, null, 2)}\n`,
    );

    const { execBuild, execBin } = setup(projectDir);
    const { stdout, stderr } = ocamlBsc
      ? await execBin(rescript_exe, ["build-reference", "--bsc", ocamlBsc, projectDir], {
          env: buildEnv,
        })
      : await execBuild([], { env: buildEnv });
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
