#!/usr/bin/env node

// @ts-check

import * as child_process from "node:child_process";

import { rescript_exe, rescript_tools_exe } from "./common/bins.js";
import { runBuildSystem } from "./common/runBuildSystem.js";

const args = process.argv.slice(2);

// Builds write no `.cmt` files, which `rescript-tools doc` reads, so the
// build system documents a module instead: `rescript doc <file>` type-checks
// the module's project in memory and prints the same JSON.
if (args.length === 2 && args[0] === "doc" && !args[1].startsWith("-")) {
  runBuildSystem(rescript_exe);
} else {
  child_process.spawnSync(rescript_tools_exe, args, { stdio: "inherit" });
}
