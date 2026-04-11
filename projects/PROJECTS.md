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

### [raw-lambda-parity](./raw-lambda-parity/)

Achieve full unoptimized lambda parity between the Rust and OCaml compilers. Focuses on building a real OCaml-aligned raw lambda stage, grouped match compilation from `matching.ml`, and module/coercion lowering from `translmod.ml`. Current baseline: 657/657 files, 0 hunks.

| Document | Description |
|----------|-------------|
| [RALPH_PROMPT.md](./raw-lambda-parity/RALPH_PROMPT.md) | Agent loop instructions for raw lambda parity |
| [RALPH_TODO.md](./raw-lambda-parity/RALPH_TODO.md) | Agent task tracking for raw lambda parity |
| [RALPH_SETUP.md](./raw-lambda-parity/RALPH_SETUP.md) | Build, baseline, and cache inspection instructions |

### [optimized-lambda-parity](./optimized-lambda-parity/)

Achieve full optimized lambda parity between the Rust and OCaml compilers. Focuses on replacing the legacy typedtree-to-lambda shortcut with the real OCaml lambda conversion and pass pipeline from `lam_compile_main.ml` and the `lam_*` pass modules. Current baseline: 0/657 files, 1631 hunks.

| Document | Description |
|----------|-------------|
| [PLAN.md](./optimized-lambda-parity/PLAN.md) | Optimized lambda parity phase plan and execution order |
| [RALPH_PROMPT.md](./optimized-lambda-parity/RALPH_PROMPT.md) | Agent loop instructions for optimized lambda parity |
| [RALPH_TODO.md](./optimized-lambda-parity/RALPH_TODO.md) | Agent task tracking for optimized lambda parity |
| [RALPH_SETUP.md](./optimized-lambda-parity/RALPH_SETUP.md) | Build, baseline, and cache inspection instructions |

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
