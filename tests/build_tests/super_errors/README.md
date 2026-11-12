Special tests for super errors (the pretty error display).

Follow CONTRIBUTING.md and build the project, then run `node ./tests/build_tests/super_errors/input.js` at the root of the project to check the tests against previous snapshots.

Run `node ./tests/build_tests/super_errors/input.js update` to update the snapshots (assuming you've made some changes to super errors' display and/or messages).

The `checker_identity_*` fixtures follow the numbering in
`compiler-rust/docs/CHECKER_REDESIGN.md` I.2.3. Fixture 1 is
`alias_name_follows_unification.res`; fixture 8 lives in `super_errors_multi`
and the genType project's `CheckerIdentity08A`/`CheckerIdentity08B` modules.
Fixture 9b has both an accepted program and a forced clash that prints the
weak phantom type. `checker_identity_comparison.res` checks I.2.4's warnings;
`tests/tests/src/checker_identity_comparison_{a,b,c}.res` checks its JavaScript
within a module and through two stored interfaces. Tuple observations are
bound before forcing a clash so the diagnostic prints their inferred types.
