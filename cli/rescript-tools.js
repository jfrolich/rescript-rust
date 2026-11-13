#!/usr/bin/env node

// @ts-check

import * as child_process from "node:child_process";

import { rescript_exe, rescript_tools_exe } from "./common/bins.js";
import { runBuildSystem } from "./common/runBuildSystem.js";

const args = process.argv.slice(2);

// Builds write no `.cmt` files, which `rescript-tools doc` reads, so the
// build system documents a module instead: `rescript doc <file>` type-checks
// the module's project in memory and prints the same JSON. Several files
// are type-checked once and printed as a JSON list.
const files = args.slice(1);
if (
  args[0] === "doc" &&
  files.length > 0 &&
  files.every(file => !file.startsWith("-"))
) {
  runBuildSystem(rescript_exe);
} else {
  child_process.spawnSync(rescript_tools_exe, args, { stdio: "inherit" });
}
