# Derived diagnostic fixtures

From the repository root, install dependencies with `yarn install --immutable`,
then build the platform executable with `make rewatch` (or `make`). Run:

```sh
node tests/build_tests/super_errors_derived/input.js
RESCRIPT_DERIVED_PATH=general node tests/build_tests/super_errors_derived/input.js
RESCRIPT_DERIVED_PATH=check node tests/build_tests/super_errors_derived/input.js
```

These commands compare the 14 diagnostic snapshots without updating them.
The harness normalizes newlines, trims surrounding whitespace and replaces
project paths before comparing; it does not compare raw log bytes or assert
build exit statuses.

`support/Spice.res` is copied from
`node_modules/@jfrolich/ppx-spice/src/rescript/Spice.res`, version 0.10.1 (MIT).
The original is identical to `tests/ppx_spice/src/Spice.res`; that test package
now vendors the library rather than depending on the npm package. Two
adaptations keep the existing snapshots unchanged:

- Read `error.path` rather than destructuring `{path}` in the array and dict
  decoders (original lines 81 and 206). With `+A-4`, partial record patterns
  otherwise emit warning 9 for the unbound `message` and `value` fields.
- Remove `include Spice_Codecs` (original line 236). The fixtures do not need
  that separate package module; including it reports a missing module before
  the fixture diagnostics can be produced.
