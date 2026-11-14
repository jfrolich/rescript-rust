#!/usr/bin/env node

// @ts-check

import * as child_process from "node:child_process";

import { rescript_exe, rescript_tools_exe } from "./common/bins.js";
import { runBuildSystem } from "./common/runBuildSystem.js";

const args = process.argv.slice(2);

// The options of `reanalyze` that read the `.cmt` files under a directory:
// the build system has none to offer for a directory that is no project.
const reanalyzeCmtOptions = [
  "-all-cmt",
  "-dce-cmt",
  "-exception-cmt",
  "-termination-cmt",
];

// Builds write no `.cmt` files, which `rescript-tools doc` and
// `rescript-tools reanalyze` read, so the build system runs them instead:
// `rescript doc <file>` and `rescript reanalyze <options>` type-check the
// project in memory and print the same output.
if (args.length === 2 && args[0] === "doc" && !args[1].startsWith("-")) {
  runBuildSystem(rescript_exe);
} else if (
  args[0] === "reanalyze" &&
  !args.some(arg => reanalyzeCmtOptions.includes(arg))
) {
  runBuildSystem(rescript_exe);
} else {
  child_process.spawnSync(rescript_tools_exe, args, { stdio: "inherit" });
}
