# In-Process Performance Scratchpad

This file is for transient measurements, hypotheses, rejected experiments, and slow-file notes. Keep committed facts concise; use temp files under `/tmp` for bulky logs/profiles.

## Current Retained Baseline

- The updated Tella corpus has grown to 3,248 compiled modules. Before the current candidate, release in-process builds measured `15.686s +/- 0.118s` over 5 runs, range `15.581s..15.887s`.
- Module timing identified one dominant regression: the 12,875-line `Layout__Types` module took `13.228s` wall / `12.549s` typecheck because every `TypeContext::variant_layout` lookup cloned its hundreds-entry constructor layout.
- A first candidate stored layouts behind `Arc` and reduced `Layout__Types` to `509.8ms` wall / `310.1ms` typecheck, but it was replaced to avoid reference counting in the per-compilation arena. The retained design reads layouts through a scoped callback. After converting typecheck and raw-Lambda hot callers, three module-timing runs averaged `642.6ms` wall / `371.2ms` typecheck / `200.7ms` Lambda, a 20.6x module-wall and 33.8x typecheck improvement over the profiled baseline. Full-corpus timing is temporarily blocked by the updated Tella source expecting newer Spice-generated aliases than the current source-built compiler provides (`Schema__EditorEvents` references missing `Story.event_encode`).
- Latest retained change: share stored persistent alias component views in normal in-process mode.
- Tella `hyperfine`: `2.488s +/- 0.014s` over 12 runs, range `2.457s..2.510s` after rebuilding both release artifacts from current HEAD (`2ffafbcd0`)
- Previous same-change retained measurement: `2.494s +/- 0.027s` over 12 runs, range `2.471s..2.556s`
- Previous retained baseline at `fea2c7566` (`Shallow-copy cold signature values`): `2.537s +/- 0.037s` over 10 runs, range `2.500s..2.631s`
- A follow-up persistent-root shallow-value experiment compiled Tella but measured `2.588s +/- 0.024s`, range `2.552s..2.637s`, so it was dropped as no improvement.
- Treat 2.9s readings in the notes below as historical/noisy baselines from before the retained signature-sharing and shallow-value freshening work, or as contaminated runs called out explicitly.
- Goal: subsecond clean compile of the Tella repo with 100% codegen parity
- JS output parity: 660/660
- Canonical typedtree parity: 660/660
- Latest measurement-infra no-regression check: module-attributed signature counters keep normal Tella `hyperfine` in-band at `2.478s +/- 0.024s` over 10 runs, range `2.452s..2.528s`; JS output parity `660/660`; canonical typedtree parity `660/660`.

## Historical Baseline Notes

- Earlier retained baseline at `Reuse cached persistent type declarations`: Tella `hyperfine` `2.848s +/- 0.021s` over 20 runs, range `2.817s..2.886s`
- A later same-commit benchmark during heavy system load reported `3.031s +/- 0.048s`, range `2.853s..3.080s`, while `uptime` showed load averages above 30 from macOS background services. Treat that run as contaminated; the minimum still matched the retained baseline band.
- Candidate persistent-root type-declaration cache reuse benchmarked at `2.907s +/- 0.043s` over 20 runs, range `2.782s..2.971s`, under continuing Spotlight load. It passed Tella clean compile, JS output parity `660/660`, and canonical typedtree parity `660/660`.
- Previous retained baseline: `2.941s +/- 0.017s` over 20 runs at `127969d9d`
- Fresh current-source check after rebuilding release artifacts at `ab4d71481`: Tella clean in-process `hyperfine` `2.755s +/- 0.060s`, range `2.673s..2.877s`; this did not reproduce a real regression back to 2.9s.
- ASCII source-read helper candidate/no-regression run: Tella clean in-process `hyperfine` `2.750s +/- 0.056s`, range `2.673s..2.847s`; JS output parity `660/660`; canonical typedtree parity `660/660`.
- Post-rebuild check after rejecting the shared-resolution helper: Tella clean in-process `hyperfine` `2.830s +/- 0.029s`, range `2.794s..2.896s`. The observed 2.9s is currently the upper edge of the retained distribution, not a retained regression.
- Persistent child alias component overlays: Tella clean in-process `hyperfine` `2.600s +/- 0.021s`, range `2.566s..2.633s`; JS output parity `660/660`; canonical typedtree parity `660/660`.
- Fresh same-branch rebaseline after the user noticed drift: Tella clean in-process `hyperfine` `2.854s +/- 0.053s`, range `2.740s..2.944s`.
- After rebuilding both release artifacts again and running with counters disabled: Tella clean in-process `hyperfine` `2.722s +/- 0.026s`, range `2.678s..2.765s`. Treat the current retained baseline as roughly the `2.7-2.8s` band; isolated 2.9s runs need system-load/context checks before calling them regressions.
- Normal-mode shallow top-level values during type-context lazy signature freshening: Tella clean in-process `hyperfine` `2.537s +/- 0.037s`, range `2.500s..2.631s`; JS output parity `660/660`; canonical typedtree parity `660/660`.
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

## Qualified Record Label Counter Baseline

`RESCRIPT_COMPILER_COUNTERS=1` now includes `qualified_record_labels`, which tracks the cache inside `qualify_label_description_paths`.

Tella clean build report after adding the counters, before local-root caching:

- hits: `78549`
- misses / registered: `46594 / 46594`
- uncached local-root labels: `50742`
- uncached other labels: `2693`

After enabling normal-compile local-root caching:

- hits: `103809`
- misses / registered: `72076 / 72076`
- uncached local-root labels: `0`
- uncached other labels: `2693`

Conclusion: normal-compile local-root caching removes about 25k repeated label-qualification copies from Tella and improved clean-build `hyperfine` from `2.941s +/- 0.017s` to `2.848s +/- 0.021s`. Canonical typedtree mode keeps local-root caching disabled and still passes `660/660`.

## Signature Qualification Counter Baseline

`RESCRIPT_COMPILER_COUNTERS=1` now includes `signature_qualification`, which classifies the full-signature copy path inside access-path qualification before it materializes a rewritten signature.
It also includes `signature_freshen` and `signature_freshen_name`, which classify `Subst.signature`-style freshening by entry point and module name.

Latest Tella clean build report after persistent child alias component overlays:

- signature_copies: `calls=25353 items=725667 max_items=559`
- resolved_name_pdot qualification: `calls=1502 items=157930 max_items=449`
- persistent_root qualification: `calls=8028 items=77353 max_items=117`
- alias qualification: `calls=502 items=4705 max_items=38`
- signature freshening: `type_context_lazy_rename calls=9730 items=327893 max_items=559`
- largest type-context lazy rename modules: `Dom 69948`, `Icon 46056`, `React 19352`, `Pervasives 17199`, `Css_Legacy_Core 17167`, `Stdlib_JSON 17052` copied items

Conclusion: persistent child aliases can share the backing `Arc<Signature>` when normal compile mode is active, as long as forced values carry a lazy source-prefix overlay. This removes most dotted reexport full-signature rewrites while preserving JS output parity.

Latest named qualification counter run after `fea2c7566`:

- Tella clean in-process compile: `Compiled 2127 modules`
- top `resolved_name_pdot` names by copied signature items: `Webapi.Dom.Element 40660`, `Webapi.Dom 19344`, `Webapi.Dom.HtmlElement 17917`, `Webapi.Dom.Document 17493`, `Webapi.Dom.Window 13756`, `Webapi.Dom.EventTarget 5016`
- top `persistent_root` names by copied signature items: `ReactEvent.Mouse 7524`, `JsxEvent.Mouse 4917`, `Jotai.Atom 4350`, `BaseUI.Tooltip 3240`, `Next.SSR 2771`, `JsxEvent.Pointer 2752`

Conclusion: the largest remaining access-path full-signature rewrites are concentrated in DOM component views, not Icon. The next shared-signature work should make `resolved_name_pdot` component views contextual/lazy so selecting `Webapi.Dom.Element` does not clone and rewrite the whole element signature each time.

After sharing stored persistent alias component views in normal in-process mode:

- Tella clean in-process compile: `Compiled 2127 modules`
- signature copies: `calls=23684 items=564930 max_items=559`, down from `25367 / 725754`
- `resolved_name_pdot`: `calls=3 items=94 max_items=42`, down from `1502 / 157930`
- JS output parity: `660/660`
- canonical typedtree parity: `660/660`
- Tella `hyperfine`: `2.494s +/- 0.027s` over 12 runs, range `2.471s..2.556s`; an earlier 10-run measurement had one contaminated `5.934s` outlier but a best run of `2.463s`

Conclusion: stored child-component thunks were still resolving persistent aliases by cloning and qualifying the whole target signature. Reusing the immutable target `Arc<Signature>` with a lazy value source-prefix overlay removes nearly all DOM `resolved_name_pdot` full-signature copies.

After adding module-attributed signature counters:

- Tella clean in-process compile: `Compiled 2127 modules`
- signature copies: `calls=23688 items=564764 max_items=559`
- signature freshening: `type_context_lazy_rename calls=9730 items=327885 max_items=559`
- top modules by signature-copy items: `Page__Story__View__New__Tabs 2918`, `Editor__Timeline__Zoom 2878`, `Http-NodeJs 2770`, `Overview__Search 2756`, `Editor__Timeline__Trimming 2676`, `UI__BackgroundPicker 2595`, `TrimTranscriptEditor 2495`, `Recording__Layers 2204`, `LayoutDetail 2011`
- top modules by signature-freshen items: `Editor__Timeline__Zoom 1606`, `Recording__Layers 1552`, `TrimTranscriptEditor 1551`, `Timeline__Scenes 1506`, `Page__Story__View__New__Tabs 1473`, `Overview__Search 1447`, `UI__BackgroundPicker 1408`, `CssJs 1371`, `Css 1369`, `Page__Stories 1161`

Conclusion: the remaining signature work is spread across JSX/layout-like modules, not concentrated in a single source file. The dependency names being freshened are still dominated by `Dom`, `Icon`, `React`, `Pervasives`, `Css_Legacy_Core`, and `Stdlib_JSON`.

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

## Module JS-Finish Timing

`RESCRIPT_MODULE_TIMINGS=1` now also prints `[module-js-timing]` for the JS-finish boundary. This complements the existing `[module-timing]`, which stops at the pre-JS boundary.

Latest clean Tella non-Icon slow modules after current retained signature sharing:

- `Css_Js_Core`: wall `510.207ms`, typecheck `253.710ms`, lambda `59.608ms`
- `Css_Legacy_Core`: wall `506.869ms`, typecheck `290.056ms`, lambda `25.534ms`
- `LayoutDetail`: wall `442.772ms`, typecheck `397.033ms`, lambda `11.550ms`
- `TrimTranscriptEditor`: wall `284.956ms`, typecheck `189.266ms`, lambda `70.423ms`
- `Page__Stories`: wall `270.960ms`, typecheck `194.155ms`, lambda `50.291ms`
- `Recording__Layers`: wall `270.661ms`, typecheck `221.983ms`, lambda `40.744ms`
- `Layout__Types`: wall `223.655ms`, typecheck `198.647ms`, lambda `13.356ms`
- `Page__Story__View__New__Tabs`: wall `220.939ms`, typecheck `177.623ms`, lambda `8.436ms`
- `UI__BackgroundPicker`: wall `220.636ms`, typecheck `158.574ms`, lambda `50.069ms`
- `Layout`: wall `172.578ms`, typecheck `16.178ms`, lambda `153.388ms`

Latest Tella aggregate phase timing under the timing env:

- parse: `2323.108ms`
- typecheck: `23834.272ms`
- lambda: `6046.517ms`
- lambda optimization: `2798.666ms`
- codegen: `2868.199ms`

Top non-Icon JS-finish/codegen files from that run:

- `Css`: codegen `64.058ms`, JS-finish wall `86.389ms`
- `Editor__Timeline__Layout2`: codegen `59.005ms`, JS-finish wall `61.812ms`
- `UI__LayoutPickerStructured`: codegen `54.501ms`, JS-finish wall `60.694ms`
- `CssJs`: codegen `51.715ms`, JS-finish wall `81.670ms`
- `Css_Legacy_Core`: codegen `44.558ms`, JS-finish wall `110.626ms`

Conclusion: for the current Tella shape, JS finish is visible but not the main bottleneck. Typecheck/signature/env work still dominates aggregate CPU time, with Lambda/lowering second.

## Retained Ideas

- CSS files contain many polymorphic-variant spreads and row traversals. The retained row-field traversal change avoided cloning full variant-row maps while forcing qualified value type paths.
- Row unification now skips the sort/allocation step for large strictly-sorted polymorphic-variant rows. The strictness keeps duplicate-label rows on the old unstable-sort path, preserving codegen parity while removing work from CSS-like row-heavy modules.
- Qualified record-label caching now includes local-root record paths in normal compile mode. Canonical typedtree mode still bypasses this local-root cache to preserve debug/parity physical sharing.
- Persistent-root `resolve_type_through_modules` now checks the full-path type declaration cache before resolving/scanning the dependency module signature again. This skips repeated signature walks for already-forced persistent type paths while leaving local stamped module paths on the old resolution path.
- Persistent-root `resolve_type_item_through_modules` now checks a full-path `(Ident, TypeDeclaration)` cache before resolving/scanning the dependency module signature again. This covers callers that need the declaration ident as well as the declaration body. Validation: Tella clean in-process compile `Compiled 2127 modules`; JS output parity `660/660`; canonical typedtree parity `660/660`. Hyperfine under heavy Spotlight load was noisy (`3.274s +/- 1.150s`, range `2.752s..6.209s`), so the minimum/range are the usable no-regression signal for this run.
- Persistent-root `resolve_type_item_through_modules` now also caches missing full paths. Counter baseline before the missing cache was `cache_hits=4`, `scans=16796`, `scanned_items=303959`, `type_items=37106`, `found=14`. After the missing cache it reported `positive_cache_hits=4`, `missing_cache_hits=15013`, `scans=1787`, `scanned_items=30488`, `type_items=4074`, `found=18`. Validation: Tella clean in-process compile `Compiled 2127 modules`; JS output parity `660/660`; canonical typedtree parity `660/660`; `hyperfine` `2.841s +/- 0.060s`, range `2.784s..2.954s`.
- Qualified value lookup now builds a value-name index only for signatures with at least 32 items after two distinct value names have already been cached. This keeps one-off lazy lookups cheap but skips repeated full-signature scans for large dependency modules. Counter shape changed from `value hits=0 misses=39128 scans=39128 scanned_items=1565337 result_items=39128` to `hits=5356 misses=33772 scans=33772 scanned_items=1172597 result_items=176483`. Validation: Tella clean in-process compile via `hyperfine` `2.802s +/- 0.018s`, range `2.766s..2.828s`; JS output parity `660/660`; canonical typedtree parity `660/660`.
- Normal in-process persistent-root component views now share the already-internalized `Arc<Signature>` when canonical typedtree mode is disabled and no flattened alias prefix rewrite is required. Signature-copy counters showed Tella dropping from `53916` full signature copies / `1612664` copied signature items to `31822` copies / `967700` items; the former top persistent-root copy site disappeared. Validation: Tella clean in-process compile `Compiled 2127 modules`; JS output parity `660/660`; canonical typedtree parity `660/660`; `hyperfine` `2.677s +/- 0.014s`, range `2.659s..2.700s`.
- Normal in-process persistent child aliases now build component views directly over the backing persistent module's shared `Arc<Signature>`. A source-prefix overlay rewrites only forced value descriptions, avoiding a whole-signature copy for dotted reexports such as runtime child modules. Validation: Tella signature-copy counters dropped from `31810 / 967596` to `25353 / 725667`; JS output parity `660/660`; canonical typedtree parity `660/660`; `hyperfine` `2.600s +/- 0.021s`, range `2.566s..2.633s`.
- Stored child-component thunks for normal in-process persistent aliases now also reuse the backing persistent module's shared `Arc<Signature>` with the same lazy value source-prefix overlay. This covers component descent through modules such as `Webapi.Dom.Element`, where the direct path already had a shared view but the stored thunk still cloned and qualified the target signature.
- JSX/Layout-heavy files likely stress record labels, component signatures, and Lambda lowering more than Icon-specific sparse prop records.
- Signature/env sharing should remain the top architectural target because it removes cross-module repeated semantic work.
- Raw lambda field-position recovery now tries the shared qualified module-components view before falling back to owned module-type reconstruction, avoiding a whole-signature clone when the component cache already has the selected module signature.
- Compiler source-read paths now share one Latin-1 decoding helper: ASCII sources reuse the read buffer as a `String`, while non-ASCII keeps the byte-to-char fallback. The in-process rewatch source path already had this fast path; this keeps `bsc`, `res_parser`, disk fallback, and parser benchmarks aligned without changing JS or typedtree output.
- Signature qualification counters classify the remaining whole-signature copy path by cause. Current Tella data shows `resolved_name` qualification dominates, so future shared-signature work should remove contextual whole-signature rewrites rather than add more eager shared-resolution paths.
- Signature freshening counters show `type_context_lazy_rename` is the largest remaining freshen bucket. A broad normal-compile skip cut copied signature items sharply but broke Tella typechecking in `API__DeleteAccount`, so the next version needs lazy/shared views that preserve type identity instead of removing the rename.
- Normal compile mode now keeps type-context lazy renamed signatures but shallow-copies top-level `SigValue` types first, deep-copying only values whose type graph references binders rewritten by the freshening maps. This preserves the semantic renamed-signature cache that Tella needs while skipping cold value type-node copies in large dependency signatures.

## Rejected Experiments

- Naively prioritizing ready JS work behind all typecheck work regressed Tella badly in one trial. Scheduler changes need a more careful cap or mixed policy and must be kept only with `hyperfine` evidence.
- Replacing one small `Vec<TypeExprRef>` visited list with `TypeExprRefSet` in a path-root search passed parity but regressed Tella `hyperfine`, so it was reverted.
- Adaptive full per-kind signature indexes reduced value/type/module scanned items by roughly 16-18%, but disabled-counter Tella `hyperfine` regressed to `3.009s +/- 0.067s` over 20 runs, so it was reverted.
- Converting current `lookup_module_in_resolved_path` callers to shared `Arc<ModuleDeclaration>` avoided owned declaration clones but regressed Tella `hyperfine` to `3.380s +/- 0.077s` over 20 runs. The extra shared-pointer path did not remove enough downstream work, so it was reverted.
- Capping JS finishing to `capacity / 4` workers while typecheck work was ready reduced aggressive JS scheduling but increased idle-slot wait in the counter run (`444.377ms` vs the retained `202.217ms`) and regressed Tella `hyperfine` to `3.078s +/- 0.044s` over 20 runs, compared with an immediately measured retained baseline of `3.056s +/- 0.014s` over 10 runs. The scheduler needs a smarter policy than a fixed JS cap.
- Storing cached qualified module-component views behind one outer `Arc` reduced the number of handle clones on cache hits, but Tella `hyperfine` did not improve (`3.314s +/- 0.856s` over 20 runs, best `3.090s`, with one large outlier). It was reverted because it only reduced cache-hit bookkeeping, not the underlying semantic work.
- Skipping row-field sorting for already-sorted large polymorphic-variant rows produced a plausible Tella timing (`3.033s +/- 0.032s` over 20 runs, best `2.992s`) but regressed JS output parity to `659/660` by changing `src/js_re_test.res` output. It was reverted; the rebuilt retained binary returned to `660/660`.
- Borrowed iterators for record-label environment lookup removed temporary `Vec<&LabelDescription>` allocations in hot disambiguation paths and passed JS output parity plus a clean Tella compile, but did not improve Tella `hyperfine` (`2.958s +/- 0.074s` over 20 runs, with outliers) versus the retained same-session baseline (`2.954s +/- 0.019s` over 10 runs). It was reverted because the allocation skip was not on the wall-clock path.
- Sharing persistent-root qualified record-label cache entries across envs improved the counter shape (`hits=126002`, `misses=49883`, `uncached_local_root=0`) but regressed Tella `hyperfine` to `2.986s +/- 0.062s` over 20 runs, range `2.912s..3.088s`, while the retained local-root-only cache had previously measured `2.848s +/- 0.021s`. It was reverted; the extra shared lookup/branching did not skip enough work to pay for itself.
- Eagerly caching all sibling persistent-root type paths during `resolve_type_item_through_modules` passed Tella compile, JS output parity, and canonical typedtree parity, but did not show a clear Tella win (`timeout`-bounded hyperfine `4.095s +/- 1.270s`, range `2.770s..6.095s`) and an earlier unbounded hyperfine run got stuck under load. It was reverted; the extra first-miss cloning/cache insertion was not justified.
- Adding the same adaptive index pattern to qualified module-name lookup reduced module scanned items (`1348978` to `1040488`) but regressed Tella `hyperfine` to `2.931s +/- 0.030s`, range `2.894s..2.993s`, compared with the retained value-index run at `2.802s +/- 0.018s`. It was reverted; materializing many module positions did not pay for itself.
- Adding the same adaptive index pattern to qualified type-name lookup reduced type scanned items (`~1522k` to `1204k`) but regressed same-session Tella `hyperfine` to `2.950s +/- 0.012s`, range `2.930s..2.976s`. After reverting the candidate and rebuilding, the retained branch measured `2.792s +/- 0.019s`, range `2.767s..2.830s`. It was reverted because materializing full type-name indexes costs more than the skipped scans.
- Lazy normal-mode component modtype freshening only moved Tella signature-copy counters from `31822` copies / `967700` items to `31802` copies / `967580` items. It was reverted because the extra `RefCell`/lazy lookup path skipped too little work to justify the added component-view complexity.
- Shallow-cloning exact persistent-root signatures in `build_module_signature_for_path` for normal in-process/no-alias cases barely changed Tella signature-copy counters (`typecore.rs:23169` moved from `2532` copies / `65599` items to `2522` copies / `65325` items). It was reverted; the retained shared component-view path already bypasses the important root case.
- Resolving module types through a shared `Arc<Signature>` before access-path qualification did not reduce the measured copy bucket (`31967` copies / `974195` copied items vs retained `31810` / `967596`) and regressed Tella `hyperfine` to `3.452s +/- 0.335s`, range `2.873s..3.714s`. It was reverted; sharing the raw signature is insufficient while qualification still materializes a rewritten full signature.
- Skipping all normal-compile `TypeContext::trigger_module_sig_rename` work cut Tella signature-copy counters from roughly `725k` copied items to `391k`, but failed typechecking in `API__DeleteAccount`. The rename work is partly semantic, not only canonical typedtree stamp preservation.
- Seeding raw signatures while skipping normal-compile `TypeContext::trigger_module_sig_rename` freshening failed the same `API__DeleteAccount` typecheck. This confirms the current typechecker depends on renamed-signature type identity somewhere, not just raw-signature availability.
- Sharing raw signatures for value-only type-context lazy renames did not fire on Tella's hot modules and did not change the copy counters, so it was removed rather than retaining an unmeasured correctness risk.
- Replacing tagged switch action comparison's `make_key` plus `Debug` formatting with the direct structural-key writer compiled Tella but did not improve clean-build `hyperfine` (`2.592s +/- 0.026s`, range `2.557s..2.634s`) versus the retained `2.537s` baseline, so it was reverted.
- Replacing `compute_variance_decl`'s small `HashMap<TypeExprRef, Variance>` with `TypeExprRefMap<Variance>` compiled Tella but regressed clean-build `hyperfine` to `2.832s +/- 0.195s`, range `2.685s..3.176s`, versus the retained 2.48s band. It was reverted; the extra dense-vector resizing does not pay off for this scratch map.
