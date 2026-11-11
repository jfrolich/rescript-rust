// @ts-check

import * as fs from "node:fs/promises";
import * as path from "node:path";
import { bsc_exe, rescript_exe } from "#cli/bins";
import { runtimeDir } from "#dev/paths";
import { execBin } from "#dev/process";

/**
 * Builds a copy of the runtime package with the `bsc` executable under
 * `parentDir`, and returns the copy's path for `bsc -runtime-path`.
 *
 * A test that runs `bsc` on its own files needs the runtime's `.cmi` files
 * (`Pervasives`, `Stdlib`). The in-process build of the runtime package
 * writes none, so the test builds the copy it compiles against itself
 * instead of depending on which build of the runtime package ran before it.
 *
 * @param {string} parentDir
 * @return {Promise<string>}
 */
export async function buildRuntimeCopy(parentDir) {
  const copy = path.join(parentDir, "runtime");
  await fs.mkdir(copy, { recursive: true });
  for (const name of await fs.readdir(runtimeDir)) {
    if (
      /\.resi?$/.test(name) ||
      name === "rescript.json" ||
      name === "package.json"
    ) {
      await fs.copyFile(path.join(runtimeDir, name), path.join(copy, name));
    }
  }
  const result = await execBin(
    rescript_exe,
    ["build-reference", "--bsc", bsc_exe, copy],
    { env: { ...process.env, RESCRIPT_RUNTIME: copy } },
  );
  if (result.status !== 0) {
    throw new Error(
      `Building the runtime copy failed:\n${result.stdout}${result.stderr}`,
    );
  }
  return copy;
}
