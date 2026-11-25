# S3.7b: loop and recursive-value lowering results

The lowering remains opt-in/check-only. These are local release-build results,
not a claim that the new backend is the default.

## Coverage

The initial in-repository baseline is `e5ada1df9`. The application baseline
was 3,709/3,848 units, with 136 `loop` and three `let rec` fallbacks.

| Corpus | Before: complete / total | After: complete / total | Before reasons | After reasons |
| --- | --- | --- | --- | --- |
| Fixtures | 519 / 593 | 609 / 609 | `loop`: 74 | none |
| Runtime | 103 / 113 | 113 / 113 | `loop`: 10 | none |
| Tests | 668 / 732 | 731 / 732 | `loop`: 50; `let rec`: 13; shared binder: 1 | shared binder: 1 |
| 3,735-module application, including runtime | 3,709 / 3,848 | 3,848 / 3,848 | `loop`: 136; `let rec`: 3 | none |

The two new reference fixtures add 16 fixture/mode units. The remaining test
fallback is `shared Lambda subtree with binder`, catch-only, at the import
boundary. No literal Unsupported reasons remain in `bir/lower`; specifically,
none contain `loop`, `let rec`, or `re-lowered conditional`. Legacy compiler
references in that directory are confined to tests and explanatory comments.

`python3 scripts/test_backend_coverage.py --record` regenerated the committed
ratchet with the release executable. A separate clean application check-mode
build produced exactly 3,848 successful lowering reports and no fallbacks.

## Correctness and bounded work

- 681 BIR tests pass, including 512 generated label shapes compared with the
  legacy printer in five continuations, direct/probed lowering and both
  parenthesis modes (10,240 text comparisons).
- Separate oracles cover recursive self-tail calls, top-level counter resets,
  captured iteration variables, every loop form, nested jumps and recursive
  groups with value members.
- 10,000 nested loops with an innermost labelled break: 20,005 source visits,
  30,007 schedule visits, one allocated label. Construction and independent
  validation each perform exactly 10,000 loop-fact folds.
- 10,000 recursive values: 10,002 source visits and 50,000 member steps.
- Event edges/source frames are 12 bytes; scheduling tasks and recursive-group
  handles are 16 bytes; recursive-member rows are 32 bytes. Statement lists
  and scheduling events are pooled.
- Check-mode JS gates pass 472 focused fixture/mode comparisons and all 732
  snapshots, with no hidden build errors; stdlib parity passes 113/113.
- Both in-repository genType suites pass. Application genType comparison with
  OCaml remains unavailable because its reference PPX setup is incomplete;
  the base/candidate application comparison below includes generated TypeScript.

The OCaml reference exposed two legacy numbering discrepancies, each fixed
separately: a discarded self-tail-call conditional probe, and general string
switches lowering cases before the default. Each has an eight-mode source
fixture. See [BACKEND_LOWERING.md §4.5](BACKEND_LOWERING.md#45-loop-labels)
for the symbolic schedule and the six continuation classes it actually needs.

## Application measurements

The candidate is the release build at `8737e4d0a`; subsequent changes are tests,
ratchet data, documentation and an equivalent iterator spelling of the fixed-size
summary loop. The base executable is the `rescript-base`
artifact from instruction-count run `43359451509`, SHA-256
`928201e697eef850351f1bd6a56423bca10e7365451d7c3f8a9e01dede21d8bc`.
It was downloaded, not rebuilt in this measurement run.

`bench_project.sh` measured 656,677 source lines. All 3,980 generated files
were identical. `compare_checker_builds.py` additionally found identical
3,735 signatures and 32 diagnostics across 18 files, with both builds exiting 0.

| Measurement | Base | Candidate |
| --- | ---: | ---: |
| Instructions | 68,318,328,208 | 67,701,647,348 |
| Instructions/source line | 104,036.426 | 103,097.333 |
| Hyperfine mean ± standard deviation | 1.850 ± 0.148 s | 1.731 ± 0.078 s |
| Hyperfine minimum–maximum | 1.665–2.070 s | 1.642–1.845 s |

Hyperfine used one warm-up and five clean builds per executable. The measured
instruction difference is −0.9027%; timing ranges overlap. These default-path
measurements are regression evidence, not a speedup attributed to the opt-in
lowerer. CI and publication status must be checked separately on the PR.
