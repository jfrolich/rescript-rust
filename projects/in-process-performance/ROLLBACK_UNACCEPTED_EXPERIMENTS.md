# Rollback of unaccepted performance experiments

Rollback PR: [jfrolich/rescript-rust#20](https://github.com/jfrolich/rescript-rust/pull/20), targeting `ocaml-to-rust-rewrite`.

This branch removes three experimental compiler changes through new revert commits. It does not rewrite `ocaml-to-rust-rewrite`, merge a PR, or roll back the verified identifier-freshness fix.

## Scope

- Env ownership: reverse compiler changes from `b5a4f7cdc`, `227e6e698`, `482761cbc`, `b54d194c1`, `0e448cb49` and `9d6a4a0b7`. Restore owned resolution snapshots and declaration results. The fixed timing cohort stopped on an output mismatch at 39/56 builds and established no accepted speedup.
- TypeArg storage: reverse `c6278e795` and `5dc38ba21`. Restore inline labels and the prior copy paths. The isolated C/D comparison measured a small gain, but acceptance remained incomplete.
- Hybrid-map restoration: reverse the compiler portion of `8311daed8`. Restore the previous dense identity map. The isolated B/C comparison measured a small gain, but acceptance remained incomplete.

Experimental reports, failed attempts, scripts and measurement evidence remain in history and on disk. Representation-specific tests introduced with the reverted implementations are removed with those implementations. The let-pattern stamp synchronization fix `a59f271c7` and its regression test remain. The inactive indexed-Lambda work and its existing generator ownership contracts are unchanged.

After these reversions, `compiler-rust` and `rewatch` match the pre-experiment source at `730dcbf30d93584bb9626d0267881d5d92e11728` except for the later identifier fix and its test instrumentation in `driver.rs`, `raw_lambda/convert.rs` and `raw_lambda/lower.rs`.

## Correction to the baseline explanation

Historical A, `fb4497659`, is on the separate `perf-type-copy-memory` branch associated with jfrolich/rescript-rust#17. It is not an ancestor of the current main branch. Their merge base is `8fcf92dc9`. Therefore D's 4.857s versus A's 4.601s does not prove that these commits regressed main by 5.6%. The earlier explanation was too broad.

This is a rollback of unaccepted experiments at the user's request. It is not a measured performance improvement, and it does not restore A's entire implementation. The positive isolated B/C and C/D results remain recorded honestly. Main retains the experimental changes until this PR is merged.

## Validation

- `cargo check --locked --offline` passed after each experiment's removal.
- Compiler library test executable built; the retained identifier regression passed once, including both existing TLS-start cases.
- Release compiler and rewatch builds passed with the normal profiles.
- Release typedtree, raw Lambda and optimized Lambda parity: 610/610 each.
- Release JavaScript parity: 344/344 focused fixtures and 610/610 snapshots.
- Release diagnostic parity: 1431/1431.

Native toolchain and runtime CMI prerequisites were reused; no fresh native build is claimed. Tella, performance timing, full release library tests and prior parser benchmark failures were not rerun. Earlier red gates are not waived. Full commands, logs, process exits and preserved release binaries are under the organization-controlled local artifact directory `rollback-unaccepted`.

A local build-target symlink was accidentally staged in the TypeArg revert, then removed from the index in a separate correction commit. The final PR contains no build-target link or generated artifacts. Setup failures, including the initial credential fetch and an incorrectly nested runtime copy, remain in the session log; the owned nested copy was moved into local artifacts without deleting any source or cache directories.
