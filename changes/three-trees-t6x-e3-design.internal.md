- The export fold of the new backend was converted once in a throw-away copy, slice by slice, and
  `THREE_TREES.md` records what that settled: a removed declaration is released at once and given up by
  whoever holds it, the final list stages the statements of a dissolved block, a substitution promises no
  order, and the id count is held under a ceiling. It gains the build prompts of T6x-e3, T6x-e4 and
  T6x-f and a probe prompt for T6r. Added: `StatementStack::take_placed` (for tests until its caller
  exists) and tests of the fold and of `JsStmt::substitute` that run on trunk. The review made the script check of the last slice cover the eighth function, marked two replaced decisions where they stand, and made each prompt say what wins against the common rules.
