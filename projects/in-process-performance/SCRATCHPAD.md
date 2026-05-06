# In-Process Performance Scratchpad

This file is for transient measurements, hypotheses, rejected experiments, and slow-file notes. Keep committed facts concise; use temp files under `/tmp` for bulky logs/profiles.

## Current Retained Baseline

- Commit: `140fca525 Add registry snapshot counters`
- Tella `hyperfine`: `3.048s +/- 0.051s` over 20 runs, after a same-session retained baseline sample of `3.056s +/- 0.014s` over 10 runs
- Later retained recheck: phase-timed clean build completed in `2896ms`; a noisy `hyperfine` recheck reported `3.118s +/- 0.074s` over 10 runs with a best run of `3.052s`
- Goal: subsecond clean compile of the Tella repo with 100% codegen parity
- JS output parity: 660/660
- Canonical typedtree parity: 660/660

## Counter Baseline

`RESCRIPT_COMPILER_COUNTERS=1` prints aggregate compiler counters at the end of an in-process build. The counters are disabled by default.

Tella clean build counter report after adding lazy signature/component counters:

- value lazy lookup: `hits=0 misses=39129 scanned_items=1565341 result_items=39129`
- type lazy lookup: `hits=152600 misses=41990 scanned_items=1522394 result_items=40159`
- module lazy lookup: `hits=767151 misses=29981 scanned_items=1348646 result_items=15655`
- constructor lazy lookup: `hits=12600 misses=4697 scanned_items=72046 result_items=4973`
- label lazy lookup: `hits=538 misses=353 scanned_items=7066 result_items=396`
- child component lazy lookup: `hits=62908 misses=17491 scanned_items=1002353 result_items=16719`
- qualified component views: `hits=1249987 misses=138619 registered=47876`

Disabled-counter Tella `hyperfine`: `2.952s +/- 0.015s` over 20 runs, compared with the retained pre-counter baseline of about `2.918s +/- 0.070s`.

## Scheduler Counter Baseline

`RESCRIPT_SCHEDULER_COUNTERS=1` prints the in-process scheduler queue shape at the end of a build. It is disabled by default.

Tella clean build scheduler counter report:

- capacity: `24`
- scheduled typecheck / JS: `2128 / 2127`
- signature ready / pre-JS ready / completed: `2127 / 2127 / 2128`
- JS scheduled while typecheck work was ready: `2104`
- max ready typecheck / ready JS / pending JS / in-flight: `545 / 18 / 2 / 24`
- blocked events with idle slots: `56`
- max idle slots: `23`
- dispatcher wait: `2453.038ms`
- idle-slot wait: `202.217ms`

Disabled-counter Tella `hyperfine` after adding scheduler counters: `2.959s +/- 0.019s` over 10 runs. A previous local `3.31s` no-diff run appears to have been transient machine noise, not retained code drift.

## Registry Snapshot Counter Baseline

`RESCRIPT_COMPILER_COUNTERS=1` now includes `module_registry_snapshots`. It reports how many per-worker snapshots are created and whether those snapshots copy local overlay maps.

Tella clean build registry snapshot report:

- snapshots: `4436`
- shared entries total / max: `12437996 / 4975`
- local entries total / max: `0 / 0`
- local module/info/alias/fallback totals: `0 / 0 / 0 / 0`

Conclusion: Tella clean builds are already using shared registry chunks for snapshots; local overlay cloning is not currently a cold-build target.

## Slow Non-Icon Files To Watch

- `node_modules/bs-css/src/Css_Js_Core.res`
- `node_modules/bs-css/src/Css_Legacy_Core.res`
- `packages/core/webapp/src/frontend/LayoutDetail.res`
- `packages/core/webapp/src/shared/Layout.res`
- `packages/core/webapp/src/frontend/UI__LayoutPickerStructured.res`
- `packages/core/webapp/src/frontend/TrimTranscriptEditor.res`
- `packages/core/webapp/src/frontend/Recording__Layers.res`
- `packages/core/webapp/src/frontend/UI__BackgroundPicker.res`
- `packages/core/webapp/src/frontend/Page__Stories.res`

## Retained Ideas

- CSS files contain many polymorphic-variant spreads and row traversals. The retained row-field traversal change avoided cloning full variant-row maps while forcing qualified value type paths.
- JSX/Layout-heavy files likely stress record labels, component signatures, and Lambda lowering more than Icon-specific sparse prop records.
- Signature/env sharing should remain the top architectural target because it removes cross-module repeated semantic work.
- Raw lambda field-position recovery now tries the shared qualified module-components view before falling back to owned module-type reconstruction, avoiding a whole-signature clone when the component cache already has the selected module signature.

## Rejected Experiments

- Naively prioritizing ready JS work behind all typecheck work regressed Tella badly in one trial. Scheduler changes need a more careful cap or mixed policy and must be kept only with `hyperfine` evidence.
- Replacing one small `Vec<TypeExprRef>` visited list with `TypeExprRefSet` in a path-root search passed parity but regressed Tella `hyperfine`, so it was reverted.
- Adaptive full per-kind signature indexes reduced value/type/module scanned items by roughly 16-18%, but disabled-counter Tella `hyperfine` regressed to `3.009s +/- 0.067s` over 20 runs, so it was reverted.
- Converting current `lookup_module_in_resolved_path` callers to shared `Arc<ModuleDeclaration>` avoided owned declaration clones but regressed Tella `hyperfine` to `3.380s +/- 0.077s` over 20 runs. The extra shared-pointer path did not remove enough downstream work, so it was reverted.
- Capping JS finishing to `capacity / 4` workers while typecheck work was ready reduced aggressive JS scheduling but increased idle-slot wait in the counter run (`444.377ms` vs the retained `202.217ms`) and regressed Tella `hyperfine` to `3.078s +/- 0.044s` over 20 runs, compared with an immediately measured retained baseline of `3.056s +/- 0.014s` over 10 runs. The scheduler needs a smarter policy than a fixed JS cap.
- Storing cached qualified module-component views behind one outer `Arc` reduced the number of handle clones on cache hits, but Tella `hyperfine` did not improve (`3.314s +/- 0.856s` over 20 runs, best `3.090s`, with one large outlier). It was reverted because it only reduced cache-hit bookkeeping, not the underlying semantic work.
- Skipping row-field sorting for already-sorted large polymorphic-variant rows produced a plausible Tella timing (`3.033s +/- 0.032s` over 20 runs, best `2.992s`) but regressed JS output parity to `659/660` by changing `src/js_re_test.res` output. It was reverted; the rebuilt retained binary returned to `660/660`.
