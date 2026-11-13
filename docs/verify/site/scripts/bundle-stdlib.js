#!/usr/bin/env node
/**
 * Bundles the runtime into `public/stdlib.json`: its `.res` and `.resi`
 * files, which the compiler in the page type checks from source when a
 * program uses them, and its compiled CommonJS modules, which the page
 * loads to run the checks of a program.
 */
import { mkdir, readdir, readFile, writeFile } from "fs/promises";
import { join } from "path";

const runtime = join(import.meta.dirname, "../../../../packages/@rescript/runtime");
const output = join(import.meta.dirname, "../public/stdlib.json");

const sources = {};
for (const name of (await readdir(runtime)).sort()) {
  if (name.endsWith(".res") || name.endsWith(".resi")) {
    sources[`/stdlib/${name}`] = await readFile(join(runtime, name), "utf-8");
  }
}
const javascript = {};
for (const name of (await readdir(join(runtime, "lib/js"))).sort()) {
  if (name.endsWith(".cjs")) {
    javascript[name.slice(0, -".cjs".length)] = await readFile(join(runtime, "lib/js", name), "utf-8");
  }
}
await mkdir(join(import.meta.dirname, "../public"), { recursive: true });
const json = JSON.stringify({ sources, javascript });
await writeFile(output, json);
console.log(
  `Bundled ${Object.keys(sources).length} sources and ${Object.keys(javascript).length} modules ` +
    `(${Math.round(json.length / 1024)} KB) -> public/stdlib.json`,
);
