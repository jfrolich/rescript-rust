#!/usr/bin/env node
/**
 * Bundles the runtime's `.res` and `.resi` files into `public/stdlib.json`.
 * The compiler in the page type checks them from source when a program uses
 * them.
 */
import { mkdir, readdir, readFile, writeFile } from "fs/promises";
import { join } from "path";

const runtime = join(import.meta.dirname, "../../../../packages/@rescript/runtime");
const output = join(import.meta.dirname, "../public/stdlib.json");

const files = {};
for (const name of (await readdir(runtime)).sort()) {
  if (name.endsWith(".res") || name.endsWith(".resi")) {
    files[`/stdlib/${name}`] = await readFile(join(runtime, name), "utf-8");
  }
}
await mkdir(join(import.meta.dirname, "../public"), { recursive: true });
await writeFile(output, JSON.stringify(files));
const size = Object.values(files).reduce((sum, text) => sum + text.length, 0);
console.log(`Bundled ${Object.keys(files).length} files (${Math.round(size / 1024)} KB) -> public/stdlib.json`);
