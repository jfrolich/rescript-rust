#!/usr/bin/env node
/**
 * Bundles all ReScript stdlib .res/.resi files into a JSON file
 * for loading into the playground's virtual filesystem.
 */
import { readdir, readFile, writeFile, mkdir } from "fs/promises";
import { join, basename } from "path";

const RUNTIME_DIR = join(import.meta.dirname, "../../packages/@rescript/runtime");
const OUTPUT = join(import.meta.dirname, "../public/stdlib.json");

async function main() {
  const entries = await readdir(RUNTIME_DIR);
  const sourceFiles = entries.filter(
    (f) => f.endsWith(".res") || f.endsWith(".resi")
  );

  const files = {};
  for (const filename of sourceFiles) {
    const content = await readFile(join(RUNTIME_DIR, filename), "utf-8");
    files[`/stdlib/${filename}`] = content;
  }

  await mkdir(join(import.meta.dirname, "../public"), { recursive: true });
  await writeFile(OUTPUT, JSON.stringify(files));

  const totalSize = Object.values(files).reduce((s, c) => s + c.length, 0);
  console.log(
    `Bundled ${Object.keys(files).length} files (${(totalSize / 1024).toFixed(0)}KB) -> public/stdlib.json`
  );
}

main().catch(console.error);
