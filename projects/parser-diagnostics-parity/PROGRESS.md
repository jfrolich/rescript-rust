# Parser Diagnostics Parity Progress

## Snapshot

Date: **February 10, 2026**

Status: **Project initialized, OCaml diagnostics inventory completed**

## Baseline Metrics

From latest local diagnostics scan:

- In-repo syntax corpus (`tests/syntax_tests/data`): **507/507 match**
- TELLA corpus (`~/dev/tella-fusion`): **2310/2320 match**
- TELLA mismatches: **10**

Mismatch classes:

1. **Message text mismatch**
   - Example: JSX tag-name wording differs.
2. **Recovery-count mismatch**
   - Example: extra Rust diagnostic emitted in same failure region.
3. **Renderer panic**
   - Rust panic in diagnostic code-frame path on binary-like malformed input.

## Representative Known Cases

1. `/Users/jaapf/dev/tella-fusion/packages/core/gstreamer/gstreamer/subprojects/gst-devtools/validate/gst/validate/validate.res`
   - OCaml and Rust both error; message text differs.
2. `/Users/jaapf/dev/tella-fusion/node_modules/@greenlabs/ppx-spice/src/rescript/Spice.res`
   - Rust emits an extra syntax diagnostic compared to OCaml.
3. `/Users/jaapf/dev/tella-fusion/packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/tzres/metaZones.res`
   - Rust parser aborts with char-boundary panic while rendering diagnostics.

## Completed

- Created diagnostics-parity project docs:
  - `projects/parser-diagnostics-parity/PLAN.md`
  - `projects/parser-diagnostics-parity/INVENTORY.md`
  - `projects/parser-diagnostics-parity/PROGRESS.md`
- Added numbered parser diagnostics matrix:
  - `tests/syntax_tests/data/parsing/diagnostics_numbers.csv`
  - `84` numbered parser error fixtures (`error,1..84,...`)
  - `1` numbered parser warning fixture (`warning,22,...`)
- Added matrix iteration checker:
  - `scripts/check_parser_diagnostics_numbers.sh`
- Completed static source inventory of OCaml parser diagnostic emitters.
- Captured representative runtime failures to anchor the plan.

## Next Actions

1. Implement Rust diagnostics code-frame panic hardening.
2. Add reduced regression fixtures for panic-inducing malformed inputs.
3. Expand the numbered matrix from fixture-level coverage to emitter-level coverage (map each source emitter to numbered fixture entries).
4. Align JSX parser message wording where Rust diverges from OCaml.
5. Align recovery behavior for known multi-error mismatch files.
6. Add diagnostics-only parity summary mode in script/CI reporting.

## Open Risks

- Large binary-like `.res` files can bypass normal assumptions about UTF-8 slicing.
- Recovery-path differences can cascade and inflate mismatch counts.
- Script-level blacklists can hide regressions if not tracked explicitly by class.
