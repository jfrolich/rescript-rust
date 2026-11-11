#!/usr/bin/env node
/**
 * Bundles the ReScript standard library for the playground: the .res/.resi
 * sources, which the compiler type checks on demand, and the compiled ES
 * modules, which the page loads to run macros and the compiled program.
 */
import { readdir, readFile, writeFile, mkdir } from "fs/promises";
import { join } from "path";

const RUNTIME_DIR = join(import.meta.dirname, "../../packages/@rescript/runtime");
const OUTPUT = join(import.meta.dirname, "../public/stdlib.json");

async function main() {
  const sources = {};
  for (const filename of await readdir(RUNTIME_DIR)) {
    if (filename.endsWith(".res") || filename.endsWith(".resi")) {
      sources[`/stdlib/${filename}`] = await readFile(join(RUNTIME_DIR, filename), "utf-8");
    }
  }

  const javascript = {};
  const jsDir = join(RUNTIME_DIR, "lib/es6");
  for (const filename of await readdir(jsDir)) {
    if (filename.endsWith(".mjs")) {
      javascript[filename.slice(0, -".mjs".length)] = await readFile(join(jsDir, filename), "utf-8");
    }
  }
  if (!javascript.Macro) {
    throw new Error("lib/es6/Macro.mjs is missing: build packages/@rescript/runtime first");
  }

  await mkdir(join(import.meta.dirname, "../public"), { recursive: true });
  const json = JSON.stringify({ sources, javascript });
  await writeFile(OUTPUT, json);

  console.log(
    `Bundled ${Object.keys(sources).length} source files and ${Object.keys(javascript).length} modules ` +
      `(${(json.length / 1024).toFixed(0)}KB) -> public/stdlib.json`
  );
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});
