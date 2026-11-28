// @ts-check

import * as assert from "node:assert";
import * as fs from "node:fs";
import * as path from "node:path";
import { setup } from "#dev/process";

const { rescript, execClean } = setup(import.meta.dirname);

/** @param {string} text */
const plain = text => text.replace(/\u001b\[[0-9;]*m/g, "");

await execClean();
const out = await rescript("verify", ["--seed", "1"]);
const report = plain(out.stdout);

// One law of the project does not hold.
assert.equal(out.status, 1, out.stdout + out.stderr);

// A law over an unbounded type is run on random values.
assert.match(report, /✓ totalIgnoresOrder\s+held for 1000 random cases/);
// A law over a finite type is run on every value.
assert.match(report, /✓ deMorgan\s+holds for all 4 values/);
assert.match(report, /✓ colours\s+holds for all 3 values/);
assert.match(report, /✓ options\s+holds for all 4 values/);
// A failing law is reported with the smallest values found.
assert.match(
  report,
  /✗ couponNeverRaisesThePrice\s+fails \(case \d+(, made smaller \d+ times?)?\)\n\s+amount = 0\n\s+coupon = Fixed\(-1\)\n\s+the law returned false\n\s+src\/Cart\.res:18/,
);
// Values of every representation are made the way compiled code reads them.
for (const law of [
  "points",
  "shapes",
  "mirrorKeepsSize",
  "mirrorTwice",
  "events",
  "ids",
  "containers",
  "Nested.reverseTwice",
]) {
  assert.match(report, new RegExp(`✓ ${law.replace(".", "\\.")}\\s`), report);
}
assert.match(report, /1 of 13 checks failed \(seed 1\)/);

// The build's JavaScript has no law, and the files the run compiled are gone.
const js = fs.readFileSync(
  path.join(import.meta.dirname, "lib/es6/src/Cart.mjs"),
  "utf8",
);
assert.ok(js.includes("function total("), js);
assert.ok(!js.includes("deMorgan"), js);
assert.ok(
  !fs.existsSync(path.join(import.meta.dirname, "lib/es6/src/Cart.verify.mjs")),
);

// The same seed gives the same report.
const again = await rescript("verify", ["--seed", "1"]);
assert.equal(plain(again.stdout).slice(plain(again.stdout).indexOf("src/Cart.res")), report.slice(report.indexOf("src/Cart.res")));

await execClean();
