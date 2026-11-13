// @ts-check

import * as assert from "node:assert";
import * as fs from "node:fs";
import * as path from "node:path";
import { setup } from "#dev/process";

const { rescript, execClean } = setup(import.meta.dirname);

/** @param {string} text */
const plain = text => text.replace(/\u001b\[[0-9;]*m/g, "");

await execClean();
const out = await rescript("verify", ["--seed", "1", "--states", "500"]);
const report = plain(out.stdout);

assert.equal(out.status, 1, out.stdout + out.stderr);

// Every property holds: all the states were gone through.
assert.match(
  report,
  /✓ request\s+always, sometimes, reachable, eventually hold over all 10 states/,
);
// The actions a spec gives are the ones tried.
assert.match(report, /✓ neverOverdrawn\s+always holds over all 15 states/);
// A machine with more states than the bound is not looked at to the end.
assert.match(
  report,
  /✓ counts\s+always held over the first 500 states \(there are more\)/,
);

// `always`: the fewest steps to a state where it is false.
assert.ok(
  report.includes(
    [
      "`always` is false after 4 steps:",
      "        init        {pending: 0, charges: 0}",
      "        Pay      →  {pending: 1, charges: 0}",
      "        Pay      →  {pending: 2, charges: 0}",
      "        Charged  →  {pending: 1, charges: 1}",
      "        Charged  →  {pending: 0, charges: 2}",
      "      src/Checkout.res:14",
    ].join("\n"),
  ),
  report,
);

// `reachable`: a state with no way to one where it is true, in a module.
assert.match(report, /✗ Dialog\.canBeClosed\s+fails: reachable/);
assert.ok(
  report.includes(
    [
      "`reachable` is out of reach after 3 steps: no actions lead from the last state to one where it is true",
      "        init           Closed",
      "        Open        →  Editing",
      "        Save        →  Saving",
      "        SaveFailed  →  Broken",
    ].join("\n"),
  ),
  report,
);

// `eventually`: a run that goes round.
assert.match(report, /✗ retriesForever\s+fails: eventually/);
assert.ok(
  report.includes(
    [
      "`eventually` is never true in this run, which can go on forever:",
      "        init      {status: Idle, attempts: 0}",
      "        Send   →  {status: Loading, attempts: 1}",
      "        and then, again and again:",
      "        Fail   →  {status: Failed, attempts: 1}",
      "        Retry  →  {status: Loading, attempts: 1}",
    ].join("\n"),
  ),
  report,
);

// `sometimes`: no state where it is true.
assert.match(
  report,
  /`sometimes` is true in none of the 4 states the machine can get into/,
);

// A step that raises.
assert.ok(
  report.includes(
    [
      "`step` raised Division_by_zero in the first state:",
      "        init      0",
      "        false  →  raises Division_by_zero",
    ].join("\n"),
  ),
  report,
);

assert.match(report, /5 of 8 checks failed/);

// The build's JavaScript has no spec, and the files the run compiled are gone.
const js = fs.readFileSync(
  path.join(import.meta.dirname, "lib/es6/src/Checkout.mjs"),
  "utf8",
);
assert.ok(js.includes("function update("), js);
assert.ok(!js.includes("chargedOnce"), js);
assert.ok(!js.includes("canBeClosed"), js);
assert.ok(
  !fs.existsSync(
    path.join(import.meta.dirname, "lib/es6/src/Checkout.verify.mjs"),
  ),
);
