# Rewatch integration-test fixture

This workspace models package layouts that Rewatch must handle. Its `rescript`
dependencies intentionally use distinct published versions: the workspace root
uses 12.0.0, while `packages/nohoist` uses 12.3.0. Keeping those versions
different makes Yarn install separate root and nested copies, which exercises
dependency discovery in hoisted and non-hoisted layouts. Do not update both
dependencies to the same version without replacing that coverage.

These published packages are not the compiler and runtime under test. When the
suite runs a native Rewatch executable, `tests/suite.sh` sets
`RESCRIPT_RUNTIME` to the runtime built from the current repository; the
compiler is linked into the Rewatch executable. The `rescript` packages installed here primarily provide a
realistic package-manager dependency tree; the version printed from
`node_modules/.bin/rescript` during setup is informational.

When changing either fixture version, regenerate this directory's `yarn.lock`
and verify that `yarn why rescript` still reports separate root and nested
installations.

`packages/with-ppx` is a negative configuration fixture: its external `sury-ppx/bin`
flag must fail with a package-specific error. It is not a root build dependency;
`tests/compile/26-external-ppx-rejected.sh` builds it separately.
