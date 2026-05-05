# Shared Interfaces — Progress Log

## Goal

Reduce repeated type-interface materialization during in-process builds while
preserving strict typedtree and JavaScript output parity.

## Current Status

The useful shared-interface changes are in the compiler proper:

- Persistent module cache hits still run the per-env preparation that the miss
  path performs, so cached modules do not skip alias-rewrite and raw-signature
  side effects.
- Stale negative persistent-module cache entries are invalidated when the
  in-process registry later publishes the module.
- Component views for selected module paths and opens are reused when the OCaml
  reference would force the same lazy component table.
- Selected record labels and qualified type lookups keep the selected access
  path while reading declarations from resolved component views.

The active in-process build still creates a fresh `TypeContext` per module. The
worker-local `TypeContext` reuse experiment was removed: it failed on Tella
typechecking in some reset configurations, and when made to compile it was
slower than the fresh-context baseline. Earlier attempts also produced semantic
JavaScript output drift, so this path is not safe to keep as inactive scaffold.

## Validated Baseline

- Non-Tella typedtree parity: 660/660.
- Non-Tella JavaScript output parity: 660/660.
- Tella clean in-process build: completes.
- Tella clean in-process timing before rejecting worker-context reuse:
  ~5.1s parallel wall, ~20.4s single-thread wall.

## Next Useful Work

Do not re-enable worker-local `TypeContext` reuse until type-representation
freshness is understood. The next optimization should be driven by the existing
per-module phase timings: typecheck dominates single-thread time, while very
large generated JSX/SVG modules still show expensive lambda/codegen behavior in
parallel builds.
