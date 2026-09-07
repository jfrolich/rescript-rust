# Position-index removal: validation and stopped comparison

## Disposition

The candidate remains on draft [jfrolich/rescript-rust#20](https://github.com/jfrolich/rescript-rust/pull/20). Main remains `d98b8b9430045d40d08ed89dd75174b5669fa829`. No measured speedup or one-second result is established.

`f1d11bfa71de2fb408de14b16bb8f188b130f317` removes the unused parser position-content index and adds the fresh-identity regression test. `eba0277be2065fa85df2816fcb3fb07032cfbc18` corrects three stale rustdoc lines. Independent source review passed. Removing two public experimental Rust methods is an explicit API change; absence of repository callers does not rule out external clients.

## Exact-head release validation

| Gate | Result |
|---|---|
| Compiler library | 1,347 passed; 108 ignored |
| Rewatch | 150 passed |
| Typedtree / raw Lambda / optimized Lambda | 610/610 each |
| JavaScript | 344/344 focused fixtures; 610/610 corpus |
| Errors | 1,431/1,431 |
| Current parser AST | 1,231 full-parity cases; 1,196 binary checks and 35 reference skips |
| Syntax/formatter | **504/570; 66 failures** |
| Legacy AST0 | **4,467 binary differences** |
| External JavaScript | **Blocked in native OCaml at missing Belt in bs-css, after 208 modules, before Rust** |

The normal release binaries rebuilt at exact `eba0277be` match the preserved pre-rustdoc binaries. The parent verified 506 tracked validation files and 1,285 expected/baseline files unchanged, plus candidate binary hashes and protected generated files. Passing core gates do not waive the red or blocked gates.

### Control limitations

For the 66 failed syntax fixtures, the surviving main/candidate controls have 65 byte/exit-identical results. `FunctionsAndArrows` crashes both with the same stack overflow; only runtime thread numbers differ. One representative legacy AST0 fixture matched main in all four checked modes, which does not establish parity across the entire failed corpus.

The syntax control violated its one-invocation rule. Its first attempt invoked fixtures 1–48 and failed in diff generation. Resume reused fixture 1, repeated fixtures 2–48, overwrote their original outputs, then first invoked fixtures 49–66. The 47 original M/C output pairs and first runner source version are unrecoverable; the first traceback log and fixture 1 outputs survive. These controls are not one-shot evidence. The parent's initial inference that no fixtures had rerun was incorrect and has been withdrawn.

## Fixed comparison: stopped before qualification

The registered experiment specified M-w12 then C-w12 qualification and 32 timed builds: eight pairs per mode, alternating mode and variant order. Inner process time was authoritative; Hyperfine was secondary. The plan allowed only the exact 12 known compiler metadata paths to change across clean/build transitions. No retries, replacements, exclusions or extensions were permitted.

Before execution, harness review caught replay, completion-order and process-cleanup defects. Worker versions and parent revisions remain preserved. The final parent harness passed 16 fake tests and an actual Hyperfine/fake-child timeout check proving both owned groups disappeared and child reaping was recorded. Runtime freshness is supported by the fresh-process in-memory registry/bootstrap source and 107 runtime source inputs, not disk CMJ timestamps: the in-process path does not publish those runtime CMJs.

The **one initial clean ran once and exited zero**. Its input check then failed: 510 `.res`/`.resi` copies under dependency `lib/bs` and `lib/ocaml` directories disappeared. This exceeded the registered 12-path allowance. The experiment stopped with **zero qualification builds and zero timed builds**. It was not rerun or reopened.

Read-only attribution afterward established that all 510 removed files were byte-identical to surviving sources in the same packages. Post-clean inputs exactly match the prior clean baseline. Compiler source, heads, status, symlinks and binary hashes were unchanged; the 18 protected `.gen.ts` files and four protected untracked files retained their hashes and mtimes. The clean process group was reaped. This explains the failed gate but does not retroactively broaden its allowance.

A future comparison needs a new preregistration that distinguishes generated source copies from authored inputs before execution. There are no candidate timing samples to analyze or pool with historical results.

## Organization-controlled evidence

Under `/Users/jake/.opensession/artifacts/rescript-performance-20260907/simplify-and-speed/`:

- `position-index-validation/exact-head-validation-4/`: gate logs, preserved binaries, validation report and parent audit.
- `position-index-comparison-protocol/`: versioned runners, tests, seals, fake-process failures and verified cleanup evidence.
- `position-index-comparison/`: preregistration, one clean's raw process evidence, before/after inventories, `EXPERIMENT_FAILED.json`, `parent-failed-freeze-audit.json` and `parent-closeout.json`.

Original plan SHA256: `e0dae752705b6c1a45244ef8fb355f482d2e1091db4ce0d6e345214cf7dd398f`.
Final parent seal SHA256: `7859b6fabb9ed6cd4f2e553de87caeff752d4645de35ae9a716446acea26ccef`.
