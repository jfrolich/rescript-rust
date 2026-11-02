#!/usr/bin/env node

// @ts-check

import { rescript_ocaml_exe } from "./common/bins.js";
import { runBuildSystem } from "./common/runBuildSystem.js";

runBuildSystem(rescript_ocaml_exe);
