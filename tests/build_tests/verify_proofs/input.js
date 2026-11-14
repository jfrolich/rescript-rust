// @ts-check

import * as assert from "node:assert";
import { setup } from "#dev/process";

const { rescript, execClean } = setup(import.meta.dirname);

/** @param {string} text */
const plain = text => text.replace(/\u001b\[[0-9;]*m/g, "");

await execClean();
const out = await rescript("verify", ["--seed", "1"]);
const report = plain(out.stdout);

assert.equal(out.status, 1, out.stdout + out.stderr);

// Induction on a list, and laws proved earlier used as lemmas.
assert.match(report, /✓ appendNil\s+proved for every value \(induction on xs\)/);
assert.match(report, /✓ lengthAppend\s+proved for every value \(induction on xs\)/);
assert.match(
  report,
  /✓ reverseAppend\s+proved for every value \(induction on xs, using appendNil, appendAssoc\)/,
);
assert.match(
  report,
  /✓ reverseTwice\s+proved for every value \(induction on xs, using reverseAppend\)/,
);

// Cases over a variant and a record, arithmetic and order on `int`.
assert.match(report, /✓ freeShippingCostsTheAmount\s+proved for every value \(by computation\)/);
assert.match(report, /✓ totalAddsUp\s+proved for every value \(3 cases\)/);
assert.match(report, /✓ clampStaysInRange\s+proved for every value \(\d+ cases\)/);

// A law the prover cannot read is run, and the report says why.
assert.match(
  report,
  /✓ reverseKeepsLength\s+held for 1000 random cases \(no proof: it uses `List\.length`, which is defined in another file\)/,
);

// `@law(proved)` is not satisfied by a run.
assert.ok(
  report.includes(
    [
      "libraryReverseTwice  is not proved",
      "      held for 1000 random cases, which is not a proof",
      "      no proof was found: it uses `List.reverse`, which is defined in another file",
      "      src/Lists.res:42",
    ].join("\n"),
  ),
  report,
);

// What is false is not proved, and the run finds the value.
assert.match(
  report,
  /✗ successorIsLarger\s+fails \(case \d+(, made smaller \d+ times?)?\)\n\s+n = 2147483647\n\s+the law returned false/,
);

assert.match(report, /2 of 11 checks failed \(seed 1\)/);
