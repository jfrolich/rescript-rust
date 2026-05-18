# Projects

This directory organizes all planning, progress, and design documents by project.

## Active Projects

### [compiler-rewrite](./compiler-rewrite/)

OCaml-to-Rust rewrite of the full ReScript compiler (~135K lines across 653 files). Phased migration with FFI boundaries, covering parser, type checker, Lambda/JS IR, and frontend integration. Currently in Phase 2 (Parser) and Phase 3 (Lambda IR).

| Document | Description |
|----------|-------------|
| [PLAN.md](./compiler-rewrite/PLAN.md) | Comprehensive 5-phase migration plan, technical approach, success criteria |
| [PROGRESS.md](./compiler-rewrite/PROGRESS.md) | Current progress across all phases, test results, blockers |
| [GLOBAL_STATE_AUDIT.md](./compiler-rewrite/GLOBAL_STATE_AUDIT.md) | Catalog of ~80+ OCaml global mutable state refs to eliminate |
| [BINARY_AST.md](./compiler-rewrite/BINARY_AST.md) | Binary AST format spec, OCaml Marshal encoding, sharing model |
| [UPSTREAM_BACKPORTS.md](./compiler-rewrite/UPSTREAM_BACKPORTS.md) | Status of upstream rescript-lang PRs in the Rust port (ported / deferred / N/A) |

### [parser-parity](./parser-parity/)

Achieve byte-for-byte identical AST and binary AST output between the Rust and OCaml parsers. Covers parse tree structure, location tracking, identity-based position sharing, and error recovery. 100% binary parity achieved for all 1,312 test files.

| Document | Description |
|----------|-------------|
| [PLAN.md](./parser-parity/PLAN.md) | Parser parity master plan |
| [TASK_FEATURES.md](./parser-parity/TASK_FEATURES.md) | Missing syntax support task list |
| [TASK_ERRORS.md](./parser-parity/TASK_ERRORS.md) | Error reporting and recovery parity |
| [TASK_ERRORS_PROGRESS.md](./parser-parity/TASK_ERRORS_PROGRESS.md) | Error reporting progress tracker |
| [POSITION_SHARING_PLAN.md](./parser-parity/POSITION_SHARING_PLAN.md) | Identity-based position sharing design |
| [RALPH_PROMPT.md](./parser-parity/RALPH_PROMPT.md) | Agent loop instructions for binary AST parity |
| [RALPH_TODO.md](./parser-parity/RALPH_TODO.md) | Agent task tracking for binary AST parity |
| [RALPH_SETUP.md](./parser-parity/RALPH_SETUP.md) | Agent setup instructions |

### [parser-diagnostics-parity](./parser-diagnostics-parity/)

Achieve full parser diagnostics parity between OCaml and Rust parsers, including syntax errors, warning output, code-frame rendering, and recovery behavior across in-repo and external corpora. Focuses on warning/error coverage, message parity, and crash-hardening for pathological inputs.

| Document | Description |
|----------|-------------|
| [PLAN.md](./parser-diagnostics-parity/PLAN.md) | Diagnostics parity roadmap, phases, acceptance criteria |
| [PROGRESS.md](./parser-diagnostics-parity/PROGRESS.md) | Current mismatch baseline and execution tracker |
| [INVENTORY.md](./parser-diagnostics-parity/INVENTORY.md) | OCaml parser warning/error emission inventory from code scan |

### [parser-performance-engineering](./parser-performance-engineering/)

Performance engineering of the Rust parser to achieve best-in-class speed. 4-tier strategy covering byte-level scanning, zero-copy tokens, SIMD, arena allocation, and PGO. Currently 2-5x faster than OCaml on small files, parity on large files.

| Document | Description |
|----------|-------------|
| [PLAN.md](./parser-performance-engineering/PLAN.md) | Optimization roadmap with 14 items across 4 tiers |
| [PROGRESS.md](./parser-performance-engineering/PROGRESS.md) | Optimization progress and benchmark log |
| [RALPH_PROMPT.md](./parser-performance-engineering/RALPH_PROMPT.md) | Agent loop instructions for performance optimization |
| [RALPH_TODO.md](./parser-performance-engineering/RALPH_TODO.md) | Agent task tracking for performance optimization |

### [typechecker-performance](./typechecker-performance/)

Performance engineering of the Rust typechecker, focused first on the
module-signature-heavy `Import.res` cliff where Rust currently spends seconds
and multi-GB while OCaml finishes in milliseconds. The main target is to make
module signature resolution, path qualification, and type expansion behave much
more like OCaml's lazy cached module-components model.

| Document | Description |
|----------|-------------|
| [PLAN.md](./typechecker-performance/PLAN.md) | Project goals, phases, and success criteria |
| [RALPH_PROMPT.md](./typechecker-performance/RALPH_PROMPT.md) | Agent loop instructions for typechecker performance work |
| [RALPH_TODO.md](./typechecker-performance/RALPH_TODO.md) | Baseline, task list, and acceptance gates |
| [RALPH_SETUP.md](./typechecker-performance/RALPH_SETUP.md) | Exact repro, timing, and profiling workflow |
| [CORPUS_BASELINE.md](./typechecker-performance/CORPUS_BASELINE.md) | Canonical 657-file benchmark baseline, slower-file clusters, and fix directions |
| [IMPORT_RES_PERFORMANCE_HANDOFF.md](./typechecker-performance/IMPORT_RES_PERFORMANCE_HANDOFF.md) | Link to the detailed investigation and fix guidance |

### [ocaml-alignment](./ocaml-alignment/)

Correctness project for bringing Rust typechecker and module-environment
behavior closer to the OCaml reference implementation, excluding intentional
in-process and performance differences. Focus areas include lazy Env component
sharing, Env lookup API boundaries, alias identity, abbreviation caches,
copy/instantiation sharing, pattern/GADT restoration, definition levels,
type-declaration groups, and module type algorithms.

| Document | Description |
|----------|-------------|
| [PLAN.md](./ocaml-alignment/PLAN.md) | Project goal, scope, guardrails, workstreams, and acceptance criteria |
| [PROGRESS.md](./ocaml-alignment/PROGRESS.md) | Current baseline, open questions, and next recommended session |
| [RALPH_PROMPT.md](./ocaml-alignment/RALPH_PROMPT.md) | Agent loop instructions for OCaml-alignment sessions |
| [RALPH_TODO.md](./ocaml-alignment/RALPH_TODO.md) | Top-ten checklist with files, OCaml references, and acceptance gates |
| [RALPH_SETUP.md](./ocaml-alignment/RALPH_SETUP.md) | Build, parity, analyzer, direct repro, and source-reference workflow |

### [in-process-performance](./in-process-performance/)

Performance engineering for clean in-process builds through `rewatch` and the Rust compiler. Tella is the current benchmark target, with priority on shared immutable signatures, lazy env/component views, critical-path scheduler work, module-registry snapshots, Lambda/JS IR allocation, and non-Icon slow files.

| Document | Description |
|----------|-------------|
| [PLAN.md](./in-process-performance/PLAN.md) | Scope, success criteria, priority order, and benchmark command |
| [RALPH_TODO.md](./in-process-performance/RALPH_TODO.md) | Active performance checklist and validation gates |
| [SCRATCHPAD.md](./in-process-performance/SCRATCHPAD.md) | Current measurements, slow-file notes, retained ideas, and rejected experiments |

### [raw-lambda-parity](./raw-lambda-parity/)

Achieve full unoptimized lambda parity between the Rust and OCaml compilers. Focuses on building a real OCaml-aligned raw lambda stage, grouped match compilation from `matching.ml`, and module/coercion lowering from `translmod.ml`. Current baseline: 657/657 files, 0 hunks.

| Document | Description |
|----------|-------------|
| [RALPH_PROMPT.md](./raw-lambda-parity/RALPH_PROMPT.md) | Agent loop instructions for raw lambda parity |
| [RALPH_TODO.md](./raw-lambda-parity/RALPH_TODO.md) | Agent task tracking for raw lambda parity |
| [RALPH_SETUP.md](./raw-lambda-parity/RALPH_SETUP.md) | Build, baseline, and cache inspection instructions |

### [optimized-lambda-parity](./optimized-lambda-parity/)

Achieve full optimized lambda parity between the Rust and OCaml compilers. Focuses on replacing the legacy typedtree-to-lambda shortcut with the real OCaml lambda conversion and pass pipeline from `lam_compile_main.ml` and the `lam_*` pass modules. Current baseline: 657/657 files, 0 hunks.

| Document | Description |
|----------|-------------|
| [PLAN.md](./optimized-lambda-parity/PLAN.md) | Optimized lambda parity phase plan and execution order |
| [RALPH_PROMPT.md](./optimized-lambda-parity/RALPH_PROMPT.md) | Agent loop instructions for optimized lambda parity |
| [RALPH_TODO.md](./optimized-lambda-parity/RALPH_TODO.md) | Agent task tracking for optimized lambda parity |
| [RALPH_SETUP.md](./optimized-lambda-parity/RALPH_SETUP.md) | Build, baseline, and cache inspection instructions |

### [js-output-parity](./js-output-parity/)

Achieve byte-for-byte emitted JavaScript parity between the Rust and OCaml compilers. Typedtree parity, raw lambda parity, and optimized lambda parity are already at 100%; this project focuses only on the real downstream backend after optimized lambda: lambda passes, grouping/coercion, JS IR lowering, JS passes, and final JS dumping. Baseline is tracked via the dedicated wrapper over the existing snapshot harness.

| Document | Description |
|----------|-------------|
| [PLAN.md](./js-output-parity/PLAN.md) | JS-output parity phase plan and backend execution order |
| [RALPH_PROMPT.md](./js-output-parity/RALPH_PROMPT.md) | Agent loop instructions for emitted JS parity |
| [RALPH_TODO.md](./js-output-parity/RALPH_TODO.md) | Agent task tracking and current baseline |
| [RALPH_SETUP.md](./js-output-parity/RALPH_SETUP.md) | Build, baseline, direct repro, and artifact inspection instructions |

### [gentype-rust](./gentype-rust/)

Implement GenType inside the Rust compiler so `bsc -bs-gentype` emits the same `.gen.tsx` and `.gen.ts` files as the OCaml compiler. Parity is measured by the in-repo GenType suites and Tella generated output, with TypeScript typecheck as a secondary gate. The plan ports the existing `compiler/gentype` implementation directly instead of shelling out, normalizing output, or adding Rust-only compatibility wrappers.

| Document | Description |
|----------|-------------|
| [PLAN.md](./gentype-rust/PLAN.md) | Full Rust GenType implementation plan, phases, architecture, and acceptance gates |
| [PROGRESS.md](./gentype-rust/PROGRESS.md) | Current Rust baseline, source inventory, test counts, and next session |
| [RALPH_TODO.md](./gentype-rust/RALPH_TODO.md) | Phase-by-phase task list for implementation sessions |
| [RALPH_SETUP.md](./gentype-rust/RALPH_SETUP.md) | Build, in-repo, Tella, and regression parity commands |

### [printer-parity](./printer-parity/)

Achieve byte-for-byte identical printer/formatter output between Rust and OCaml. Covers the AST printer, OCaml Format module compatibility, and roundtrip idempotence. Currently at 423/506 syntax tests passing (83%).

| Document | Description |
|----------|-------------|
| [PLAN.md](./printer-parity/PLAN.md) | Printer rewrite plan (1:1 OCaml port) |
| [FORMATTER_PLAN.md](./printer-parity/FORMATTER_PLAN.md) | OCaml Format module compatibility plan |
| [TASK_ROUNDTRIP.md](./printer-parity/TASK_ROUNDTRIP.md) | Roundtrip idempotence task list |
| [RALPH_PROMPT.md](./printer-parity/RALPH_PROMPT.md) | Agent loop instructions for syntax parity |
| [RALPH_TODO.md](./printer-parity/RALPH_TODO.md) | Agent task tracking for syntax parity |
| [RALPH_SETUP.md](./printer-parity/RALPH_SETUP.md) | Agent setup instructions |

### [comptime](./comptime/)

Design proposal for compile-time metaprogramming in ReScript, inspired by Zig's comptime. Intended to replace PPX use cases with a simpler, more powerful system.

| Document | Description |
|----------|-------------|
| [DESIGN.md](./comptime/DESIGN.md) | Full design document |
