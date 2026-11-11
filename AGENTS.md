# AGENTS.md

This file provides guidance to AI coding assistants when working with code in this repository.

## ⚠️ CRITICAL: NEVER use `rm -rf` on directories

**An agent previously deleted the entire repository with `rm -rf`.** This is catastrophic and unrecoverable.

Rules:
- **NEVER run `rm -rf` on any directory** unless the user explicitly asks you to delete that specific directory
- **NEVER run `rm -rf` with variables** (e.g., `rm -rf $DIR`) — variable expansion bugs can delete wrong paths
- To clean caches or temp files, remove specific files by name (e.g., `rm /path/to/specific/file`)
- If you need to clear a cache directory, use `rm /path/to/cache/*.ext` with a specific extension, NOT `rm -rf /path/to/cache/`
- When in doubt, use `ls` first to see what you'd be deleting, and ask the user before proceeding

## ⚠️ Repository Setup - READ FIRST

- `jfrolich/rescript-rust` is the development repository. Its default branch is
  `ocaml-to-rust-rewrite`. Push only to this repository.
- `rescript-lang/rescript` is the read-only upstream. **Never push to it.**

Depending on the checkout, the development repository is the `origin` or the
`private` remote; check `git remote -v` before pushing.

## Quick Start: Essential Commands

```bash
# Build the platform toolchain (default target)
make

# Build the platform toolchain + stdlib
make lib

# Build the platform toolchain + stdlib and run tests
make test

# Format code
make format

# Check formatting
make checkformat
```

The Makefile’s targets build on each other in this order:

1. `yarn-install` runs automatically for targets that need JavaScript tooling (lib, playground, tests, formatting, etc.).
2. `build` (default target) builds the toolchain binaries (all copied into `packages/@rescript/<platform>/bin`):
   - `compiler` builds the dune executables (`bsc`, `rescript-*`, `ounit_tests`, etc.).
   - `rewatch` builds the Rust-based ReScript build system and CLI.
3. `lib` uses those toolchain outputs to build the runtime sources.
4. Test targets (`make test`, `make test-syntax`, etc.) reuse everything above.

## ⚠️ Critical Guidelines & Common Pitfalls

- **COMMIT YOUR CHANGES** - After completing ANY meaningful work (bug fix, feature, refactor, parity improvement), you MUST commit immediately. Do not leave work uncommitted. Do not move on to the next task without committing first. This is the most important rule.

- **Match OCaml's behaviour, not its implementation** - Read
  "The Correctness Contract" below. Identical JavaScript and a consistent type
  system are required; mirroring OCaml's algorithms, laziness or data sharing is
  not. Do large refactors when the current Rust design is in the way.

- **We are NOT bound by OCaml compatibility** - The ReScript compiler originated as a fork of the OCaml compiler, but we maintain our own AST and can make breaking changes. Focus on what's best for ReScript's JavaScript compilation target.

- **PPX is not supported going forward; `parsetree0.ml` is not frozen** - Nothing compares the v0 parsetree or `.ast` bytes with OCaml. The v0 form and its mappers (`ast_mapper_to0`/`ast_mapper_from0`) remain only because external `-ppx` flags and the builtin Spice mapper still round-trip through them, so a new construct must not be dropped there; change `parsetree0` when that is simpler than encoding around it.

- **Missing test coverage** - Always add tests for syntax, lambda, and end-to-end behavior

- **Test early and often** - Add tests immediately after modifying each compiler layer to catch problems early, rather than waiting until all changes are complete

- **Use underscore patterns carefully** - Don't use `_` patterns as lazy placeholders for new language features that then get forgotten. Only use them when you're certain the value should be ignored for that specific case. Ensure all new language features are handled correctly and completely across all compiler layers
- **Avoid `let _ = …` for side effects** - If you need to call a function only for its side effects, use `ignore expr` (or bind the result and thread state explicitly). Do not write `let _ = expr in ()`, and do not discard stateful results—plumb them through instead.

- **Don't use unit `()` with mandatory labeled arguments** - When a function has a mandatory labeled argument (like `~config`), don't add a trailing `()` parameter. The labeled argument already prevents accidental partial application. Only use `()` when all parameters are optional and you need to force evaluation. Example: `let forceDelayedItems ~config = ...` not `let forceDelayedItems ~config () = ...`

- **Avoid warning suppressions** - Never use `[@@warning "..."]` to silence warnings. Instead, fix the underlying issue properly
- **Skip trailing `; _` in record patterns** - The warning it targets is disabled in this codebase, so prefer `{field = x}` over `{field = x; _}`.
- **Do not introduce new `unsafe` Rust in compiler code** - Prefer safe ownership/lifetime patterns (owned `String`, arena indices, side tables). If `unsafe` is truly unavoidable (for example, FFI boundaries), keep it narrowly scoped, document invariants, and justify it in the PR/commit message.

- **Do not introduce new keywords unless absolutely necessary** - Try to find ways to implement features without reserving keywords, as seen with the "catch" implementation that avoids making it a keyword.

- **Use tight timeouts when testing compiler/parser** - When running the compiler or parser in tests, always use a short timeout (e.g., 5-10 seconds). Compilation should be fast, and logic errors can cause infinite loops or hangs. A tight timeout ensures these issues are caught quickly rather than blocking indefinitely.

- **Handle concurrent agent work gracefully** - If compilation fails due to errors in code you didn't touch, another agent may be actively working on that part of the codebase. Do NOT modify their files and NEVER use `git stash`. Simply wait 30 seconds and retry the build. Repeat this until compilation succeeds—the other agent will fix their changes shortly.

- **There is NO linter that reverts your changes** - If you're having trouble editing files, the issue is with your edit commands (e.g., wrong `old_string`, file not found, etc.), NOT a linter reverting changes. There are no pre-commit hooks, no auto-formatters, and no tools that automatically modify or revert your edits. Debug your actual edit failures instead of assuming external interference.

- **Finish the task you started** - Do not revert a large change or switch to an
  easier task because the current one got hard. Complete it, then move on.

- **ALWAYS commit before moving on** - Before starting a new task, before investigating a problem, before taking a break: COMMIT. Use `git add <files> && git commit -m "description"`. No exceptions.

- **One task per session** - Only take on ONE task at a time. When you complete a task, STOP. Do not pick up another task from the TODO list. Each new task should start with a fresh context window. This ensures you have full context capacity for each task and prevents context exhaustion from accumulating state across multiple tasks.

## ⚠️ CRITICAL: The Correctness Contract

The Rust compiler is a drop-in replacement for the OCaml compiler. Two things
define whether it is correct:

1. **The generated JavaScript is byte-for-byte identical** to what the OCaml
   compiler emits for the same sources and flags. That includes gentype output
   and source maps. Check it with `scripts/test_js_output_parity.sh`,
   `scripts/test_stdlib_output_parity.sh` and
   `scripts/test_gentype_output_parity.sh`.
2. **The type system is consistent with OCaml's.** The same programs are
   accepted and rejected, inferred and printed types are the same, and errors
   and warnings match in text and location. Check it with
   `scripts/test_error_output_parity.sh` and the `super_errors` build tests.

**The implementation may differ from OCaml.** Different algorithms, data
structures, evaluation order, laziness and type-node sharing are all fine as
long as both points hold. When two implementations satisfy the contract, pick
the simpler and more explicit one:

- an enum for state that moves through phases, not a combination of bools and
  `Option`s;
- a parameter, not a mutable field that is armed before a call and cleared
  after it;
- forcing a lazy value where it is needed, not capturing paths to force later.

Do not add mechanisms whose only purpose is reproducing OCaml's typedtree
sharing, stamp order or force order. Remove existing ones when they are in the
way and the contract still holds.

**No intermediate representation is compared with OCaml.** The parse tree,
the PPX-facing parsetree0 and `.ast` files, the typed tree, raw and optimized
Lambda, and identifier stamps may all differ from OCaml's; there are no parity
tests for them. The dump flags (`-dparsetree`, `-dtypedtree`, `-drawlambda`,
`-dlambda-sexp`, ...) remain as debugging aids for finding where a JavaScript
or diagnostic difference starts. The checks of ReScript the parser and printer
emit (formatting, JSX output, syntax errors) stay, through the syntax tests.

Beyond the two points above, keep these working:

- Artifacts other tools read: `.cmi`, `.cmt`, `.cmti`, `.ast` and `.cmj` files
  must stay usable by editor tooling, analysis and incremental builds.
- Determinism: output must not depend on thread count, scheduling or hash
  iteration order.

### Using the OCaml source

The OCaml compiler under `compiler/` is the reference for **behaviour**. When
the JavaScript or a diagnostic differs, read the OCaml code to learn what it does
and why, then implement that behaviour in whatever form is cleanest in Rust.
When a piece of Rust exists only to reproduce a non-obvious OCaml behaviour,
cite the OCaml location (`compiler/ml/<file>.ml:<line>`) in a comment.

### Verifying a change

- Refactors with no intended behaviour change: `cargo build` and `cargo test`
  for `compiler-rust` and `rewatch`, plus `./scripts/test_js_output_parity.sh`.
- Type checker changes: also `./scripts/test_error_output_parity.sh` and the
  `super_errors` build tests.
- Lambda or JS backend changes: JS output parity (including
  `./scripts/test_stdlib_output_parity.sh` and
  `./scripts/test_gentype_output_parity.sh`) is the gate.
- Parser or printer changes: `make test-syntax` and
  `./scripts/test_rust_parity.sh --skip-js` (the Rust parser against the
  ReScript and syntax-error snapshots).

### Rebuilding the OCaml bsc

If you modify OCaml source files (e.g., under `compiler/ml/`), rebuild with:
```bash
eval $(opam env) && dune clean --root . && dune build --root .
```
This is worktree-specific — other worktrees have their own dune build.

## Compiler Architecture

### Compilation Pipeline

```
ReScript Source (.res)
  ↓ (ReScript Parser - compiler/syntax/)
Surface Syntax Tree
  ↓ (Frontend transformations - compiler/frontend/)
Surface Syntax Tree
  ↓ (OCaml Type Checker - compiler/ml/)
Typedtree
  ↓ (Lambda compilation - compiler/core/lam_*)
Lambda IR
  ↓ (JS compilation - compiler/core/js_*)
JS IR
  ↓ (JS output - compiler/core/js_dump*)
JavaScript Code
```

### Platform-specific compiler modules

The Dune `browser` profile builds the playground compiler. Platform-dependent
modules are stored below `platform/native/` and `platform/playground/` in their
owning compiler directory. Rules in that directory's `dune` file copy the
selected implementation into the build directory as an ordinary `.ml` module;
all other profiles select the native source. Generated module paths in errors
or stack traces therefore map back to one of those two source directories.

### Key Directory Structure

```
compiler/
├── syntax/          # ReScript syntax parser (MIT licensed)
├── frontend/        # AST transformations, FFI processing
├── ml/              # OCaml compiler infrastructure
├── core/            # Core compilation (lam_*, js_* files)
├── ext/             # Extended utilities and data structures
└── gentype/         # TypeScript generation

analysis/            # Language server and tooling
packages/@rescript/
├── runtime/         # Runtime and standard library
└── <platform>/      # Platform-specific binaries

tests/
├── syntax_tests/    # Parser/syntax layer tests
├── tests/           # Runtime library tests
├── build_tests/     # Integration tests
└── ounit_tests/     # Compiler unit tests
```

## Working on the Compiler

### Development Workflow

Read the area guide before changing a compiler subsystem:

- [`compiler/syntax/README.md`](compiler/syntax/README.md) for parsing,
  printing, and JSX transformation
- [`compiler/ml/README.md`](compiler/ml/README.md) for the type checker and
  typed tree
- [`compiler/core/README.md`](compiler/core/README.md) for Lambda
  optimization and JavaScript generation
- [`analysis/README.md`](analysis/README.md) for editor analysis
- [`rewatch/README.md`](rewatch/README.md) for the build system
- [`tools/README.md`](tools/README.md) for `rescript-tools`

1. **Understand which layer you're working on:**
   - **Syntax layer** (`compiler/syntax/`): Parsing and surface syntax
   - **ML layer** (`compiler/ml/`): Type checking and AST transformations
   - **Lambda layer** (`compiler/core/lam_*`): Intermediate representation and optimizations
   - **JS layer** (`compiler/core/js_*`): JavaScript generation

2. **Always run appropriate tests:**

   ```bash
   # For compiler or stdlib changes
   make test

   # For syntax changes
   make test-syntax

   # For specific test types
   make test-syntax-roundtrip
   make test-gentype
   make test-analysis
   ```

3. **Test your changes thoroughly:**
   - Syntax tests for new language features
   - Integration tests for behavior changes
   - Unit tests for utility functions
   - Always check JavaScript output quality

4. **Add a `CHANGELOG.md` entry** for any user-facing change (bug fix, feature, or breaking change). Put it under the matching section of the current `(Unreleased)` version and end the line with the PR link. See [CONTRIBUTING.md](CONTRIBUTING.md). PRs are expected to include one.

### Debugging Techniques

#### View Intermediate Representations

```bash
# Source code (for debugging preprocessing)
./packages/@rescript/<platform>/bin/bsc.exe -dsource myfile.res

# Parse tree (surface syntax after parsing)
./packages/@rescript/<platform>/bin/bsc.exe -dparsetree myfile.res

# Typed tree (after type checking)
./packages/@rescript/<platform>/bin/bsc.exe -dtypedtree myfile.res

# Raw lambda (unoptimized intermediate representation)
./packages/@rescript/<platform>/bin/bsc.exe -drawlambda myfile.res

# Use lambda printing for debugging (add in compiler/core/lam_print.ml)
```

#### Common Debug Scenarios

- **JavaScript formatting issues**: Check `compiler/ml/pprintast.ml`
- **Type checking issues**: Look in `compiler/ml/` type checker modules
- **Optimization bugs**: Check `compiler/core/lam_*.ml` analysis passes
- **Code generation bugs**: Look in `compiler/core/js_*.ml` modules

### Testing Requirements

#### When to Add Tests

- **Always** for new language features
- **Always** for bug fixes
- **When modifying** analysis passes
- **When changing** JavaScript generation

#### Test Types to Include

1. **Syntax tests** (`tests/syntax_tests/`) - Parser validation
2. **Integration tests** (`tests/tests/`) - End-to-end behavior
3. **Unit tests** (`tests/ounit_tests/`) - Compiler functions
4. **Build tests** (`tests/build_tests/`) - Error cases and edge cases
5. **Type tests** (`tests/build_tests/super_errors/`) - Single-file type checking errors
6. **Multi-file error tests** (`tests/build_tests/super_errors_multi/`) - Cross-module errors that need separate `.res` / `.resi` files

#### Error variant catalog

[`tests/ERROR_VARIANTS.md`](tests/ERROR_VARIANTS.md) is a per-module
catalog of every error and warning variant the compiler can emit, with
each entry mapped to a fixture (or a documented reason it's unreachable).

**When adding or removing an error variant**, also update the catalog:

1. Add (or remove) the row in the relevant module section.
2. Set the status (`✓` covered / `⚠` unreachable / `☐` TODO).
3. If covered, link the fixture path; if unreachable, note the reason.

**When adding or removing a fixture**, update the corresponding row's
`Fixture` and status columns so the catalog stays in sync with the test
suite. The catalog is the primary tool for finding coverage gaps and
dead-code removal candidates; stale entries make both jobs harder.

## Build Commands & Development

### Essential Commands

```bash
# Build compiler
make

# Build compiler in watch mode
make watch

# Build compiler and standard library
make lib

# Build compiler and standard library and run all tests
make test

# Build artifacts and update artifact list
make artifacts

# Clean build
make clean
```

### Testing Commands

```bash
# Specific test types
make test-syntax           # Syntax parser tests
make test-syntax-roundtrip # Roundtrip syntax tests
make test-gentype         # GenType tests
make test-analysis        # Analysis tests
make test-tools           # Tools tests
make test-rewatch         # Rewatch tests

# Single file debugging
./packages/@rescript/<platform>/bin/bsc.exe myfile.res
```

### Code Quality

```bash
# Format code
make format

# Check formatting
make checkformat

# Lint with Biome
npm run check
npm run check:all

# TypeScript type checking
npm run typecheck
```

## Performance Considerations

The compiler is designed for fast feedback loops and scales to large codebases:

- **Avoid meaningless symbols** in generated JavaScript
- **Maintain readable JavaScript output**
- **Consider compilation speed impact** of changes
- **Use appropriate optimization passes** in Lambda and JS IRs
- **Profile** before and after performance-related changes

### High-Performance Compiler Engineering

These principles apply to all performance-sensitive Rust code in the compiler, especially the parser, type checker, and code generator. They are informed by data-oriented design (DOD) research from OXC, Zig, Roc, Sorbet, and academic work.

#### Data layout principles

- **Prefer arenas for compiler graphs** — Use typed `Vec` pools with small indices (such as `ExprIdx(u32)`) for ASTs and IRs whose nodes share a lifetime; this avoids per-node allocations and reference-count updates. Prefer owned or borrowed data (`Box<T>`, `&T`, `Cow<'a, T>`) when sharing is unnecessary. When shared ownership is genuinely needed, use `Rc` for worker-local state and `Arc` for cross-thread sharing. `Rc` cannot cross threads; `Arc<T>` supports cross-thread sharing only when `T` is `Send + Sync`. Do not introduce reference counting merely to work around an unclear ownership model; measure performance-sensitive changes.

- **Keep enums small (≤16 bytes)** — Rust enums are sized by their largest variant. If 85% of variants fit in 8 bytes but one variant needs 100 bytes, every instance wastes 92 bytes. Box the large, rare variants. OXC measured 10% speedup from enforcing 16-byte AST enums.

- **Separate hot and cold data** — Fields accessed on every iteration belong together in one struct. Rarely-used fields (error recovery state, diagnostics, attributes) belong in a separate struct or side table. A 280-byte struct spanning 5 cache lines forces the CPU to load 4 cache lines of cold data to access 1 cache line of hot data. The Roc compiler gained 12% by splitting hot/cold data in their `Defs` type.

- **Side tables for sparse data** — If a field is None/empty >80% of the time, don't store it inline. Use a `HashMap<NodeIdx, T>` or `Vec<Option<T>>` side table. Each inline `Vec<Attribute>` wastes 24 bytes when empty (pointer + length + capacity), and ~95% of AST nodes have no attributes.

- **Prefer arrays over pointer-chased trees** — Sequential array access runs at ~0.96 instructions/cycle. Random pointer chasing runs at ~0.12 instructions/cycle (CPU stalled 87.5% of the time waiting for memory). Flattening a pointer-based AST into arena-indexed arrays gave 2.4x speedup in academic benchmarks. The CPU prefetcher can predict linear access but not pointer dereferences.

- **Bottom-up construction enables linear traversal** — When expressions are built bottom-up (children before parents), a depth-first traversal of the flattened array becomes a linear forward scan. This is automatically prefetcher-friendly and gives an additional ~8% speedup on top of flattening.

#### Allocation patterns

- **Arena allocate, bulk free** — Parser AST nodes have correlated lifetimes: they're all created during parsing and discarded together. Arena/bump allocation (single pointer increment) is near-zero cost vs `malloc` (free list search, metadata update). OXC measured 20% speedup from `bumpalo`. Even without bumpalo, storing nodes in `Vec<T>` pools with `u32` indices achieves similar benefits.

- **Pre-size collections** — If you know the approximate count (from source size heuristics or arena counts), pre-allocate Vecs and HashMaps. Repeated reallocation and copying is pure waste.

- **SmallVec for small, fixed-arity collections** — Function arguments average 1-3 items, tuple elements 2-4. `SmallVec<[T; 3]>` stores these inline without heap allocation. Only falls back to heap for the rare >N case.

#### String handling

- **Zero-copy from source** — Use `&'a str` or `Cow<'a, str>` to borrow from the source buffer rather than allocating `String`. Only allocate for strings that need transformation (escape sequences). The scanner produces borrowed strings for 99% of tokens.

- **Intern repeated strings** — Identifiers like `t`, `x`, `unit` appear thousands of times. Store each unique string once and reference by `StrIdx(u32)`. Comparison becomes integer equality instead of byte-by-byte string comparison.

- **Propagate borrows into the AST** — If strings are never modified after parsing, carry `Cow<'a, str>` or `&'a str` all the way into AST node types rather than converting to owned `String` at the token→AST boundary.

#### Serialization

- **Replace HashMaps with indexed Vecs for arena-keyed lookups** — If your keys are already arena indices (`PosIdx`, `LocIdx`, `StrIdx`), use `Vec<Option<u32>>` indexed by the raw index value. O(1) with no hashing, no pointer chasing, and the Vec can be pre-sized from the arena count.

- **Pre-allocate output buffers** — Binary output size correlates with source size. Pre-allocate based on a heuristic (e.g., 4x source bytes) rather than growing from a small default.

#### Measurement

- **Always benchmark with `hyperfine`** — Every performance change must have before/after numbers. "Should be faster" is not evidence. Use `hyperfine` with multiple runs and a representative `--prepare` step for clean-build measurements, then report the mean, standard deviation, and min/max range.

- **CI blocks instruction increases** — The `Instruction count` workflow counts the instructions of a clean `tests/tests` build (cachegrind, one worker thread) with the pull request's `rescript` and its base's, both built like a release, and fails when the pull request's executes more than 0.1% more. When a change has to cost more, give one of its commits an `Instruction-count-increase: <why>` trailer. On Linux, `scripts/compare_build_instructions.py` runs the same comparison locally.

- **Profile before optimizing** — Use flamegraphs (`cargo flamegraph`), `perf stat` (cache misses, branch misses), or DHAT (heap profiling) to find actual bottlenecks. Don't guess.

- **Measure struct sizes** — Add `assert_eq!(std::mem::size_of::<T>(), N)` tests for critical types. Enum size regressions (someone adds a large variant) silently degrade cache performance across the entire codebase.

## Coding Conventions

### Naming

- **OCaml code**: snake_case (e.g., `to_string`)
- **ReScript code**: camelCase (e.g., `toString`)

### Commit Standards

- Use DCO sign-off: `Signed-Off-By: Your Name <email>`
- Include appropriate tests with all changes
- Build must pass before committing
- **Commit atomically** - Each commit should address exactly one concern (one bug fix, one feature, one refactor). When making multiple related changes, split them into separate atomic commits. For example, if fixing a parity issue requires adding a new field to a struct and then using that field in parsing logic, make two commits: one for the struct change, one for the parsing logic. This makes it easier to review changes, bisect issues, revert specific changes if needed, and understand the evolution of the codebase. Each commit message should clearly describe what was changed and why.

### Stacked pull requests

When a PR depends on another unmerged PR, make a native GitHub stack. Keep the
branches linear and in the same repository, then run `gh stack link BOTTOM
[NEXT...]`, listing the stack bottom to top. Each argument is a branch name or
a PR number: the command pushes each branch, reuses the PR that already exists
for it, and opens one where there is none, so branches alone are enough. Open
the PRs yourself first if you want to write their titles and descriptions.

Linking sets each PR's base to the branch below it, leaving only the bottom PR
on `master`. CI runs on every PR in the stack.

### Code Quality

- Follow existing patterns in the codebase
- Prefer existing utility functions over reinventing
- Comment complex algorithms and non-obvious logic
- Maintain backward compatibility where possible

## Development Environment

- **OCaml**: 5.5.0+ with opam
- **Build System**: dune with profiles (dev, release, browser)
- **JavaScript**: Node.js 20+ for tooling
- **Rust**: Toolchain needed for rewatch

## Common Tasks

### Adding New Language Features

1. Update parser in `compiler/syntax/`
2. Update AST definitions in `compiler/ml/`
3. Implement type checking in `compiler/ml/`
4. Add Lambda IR handling in `compiler/core/lam_*`
5. Implement JS generation in `compiler/core/js_*`
6. Add comprehensive tests

### Debugging Compilation Issues

1. Identify which compilation phase has the issue
2. Use appropriate debugging flags (`-dparsetree`, `-dtypedtree`)
3. Check intermediate representations
4. Add debug output in relevant compiler modules
5. Verify with minimal test cases

### Working with Lambda IR

- Remember Lambda IR is the core optimization layer
- All `lam_*.ml` files process this representation
- Use `lam_print.ml` for debugging lambda expressions
- Test both with and without optimization passes

## Working on the Build System

### Rewatch Architecture

Rewatch is ReScript's build system written in Rust. It provides fast incremental builds, better error messages, and improved developer experience.

#### Key Components

```
rewatch/src/
├── build/              # Core build system logic
│   ├── build_types.rs  # Core data structures (BuildState, Module, etc.)
│   ├── compile.rs      # Compilation logic and bsc argument generation
│   ├── parse.rs        # AST generation and parser argument handling
│   ├── packages.rs     # Package discovery and dependency resolution
│   ├── deps.rs         # Dependency analysis and module graph
│   ├── clean.rs        # Build artifact cleanup
│   └── logs.rs         # Build logging and error reporting
├── cli.rs              # Command-line interface definitions
├── config.rs           # rescript.json configuration parsing
├── watcher.rs          # File watching and incremental builds
└── main.rs             # Application entry point
```

#### Build System Flow

1. **Initialization** (`build::initialize_build`)
   - Parse `rescript.json` configuration
   - Discover packages and dependencies
   - Set up compiler information
   - Create initial `BuildState`

2. **AST Generation** (`build::parse`)
   - Generate AST files using `bsc -bs-ast`
   - Handle PPX transformations
   - Process JSX

3. **Dependency Analysis** (`build::deps`)
   - Analyze module dependencies from AST files
   - Build dependency graph
   - Detect circular dependencies

4. **Compilation** (`build::compile`)
   - Generate `bsc` compiler arguments
   - Compile modules in dependency order
   - Handle warnings and errors
   - Generate JavaScript output

5. **Incremental Updates** (`watcher.rs`)
   - Watch for file changes
   - Determine dirty modules
   - Recompile only affected modules

### Development Guidelines

#### Adding New Features

1. **CLI Arguments**: Add to `cli.rs` in `BuildArgs` and `WatchArgs`
2. **Configuration**: Extend `config.rs` for new `rescript.json` fields
3. **Build Logic**: Modify appropriate `build/*.rs` modules
4. **Thread Parameters**: Pass new parameters through the build system chain
5. **Add Tests**: Include unit tests for new functionality

#### Common Patterns

- **Parameter Threading**: New CLI flags need to be passed through:
  - `main.rs` → `build::build()` → `initialize_build()` → `BuildState`
  - `main.rs` → `watcher::start()` → `async_watch()` → `initialize_build()`

- **Configuration Precedence**: Command-line flags override `rescript.json` config
- **Error Handling**: Use `anyhow::Result` for error propagation
- **Logging**: Use `log::debug!` for development debugging

#### Testing

```bash
# Run rewatch tests (from project root)
cargo test --manifest-path rewatch/Cargo.toml

# Test specific functionality
cargo test --manifest-path rewatch/Cargo.toml config::tests::test_get_warning_args

# Run clippy for code quality
cargo clippy --manifest-path rewatch/Cargo.toml --all-targets --all-features

# Check formatting
cargo fmt --check --manifest-path rewatch/Cargo.toml

# Build rewatch
cargo build --manifest-path rewatch/Cargo.toml

# Or use the Makefile shortcuts
make rewatch          # Build rewatch
make test-rewatch     # Run integration tests
```

**Note**: The rewatch project is located in the `rewatch/` directory with its own `Cargo.toml` file. All cargo commands should be run from the project root using the `--manifest-path rewatch/Cargo.toml` flag, as shown in the CI workflow.

**Integration Tests**: The `make test-rewatch` command runs bash-based integration tests located in `rewatch/tests/suite.sh`. These tests use the `rewatch/testrepo/` directory as a test workspace with various package configurations to verify rewatch's behavior across different scenarios.

**Running Individual Integration Tests**: You can run individual test scripts directly by setting up the environment manually:

```bash
cd rewatch/tests
export REWATCH_EXECUTABLE="$(realpath ../target/debug/rescript)"
eval $(node ./get_bin_paths.js)
export RESCRIPT_RUNTIME
source ./utils.sh
bash ./watch/06-watch-missing-source-folder.sh
```

This is useful for iterating on a specific test without running the full suite.

#### Debugging

- **Build State**: Use `log::debug!` to inspect `BuildState` contents
- **Compiler Args**: Check generated `bsc` arguments in `compile.rs`
- **Dependencies**: Inspect module dependency graph in `deps.rs`
- **File Watching**: Monitor file change events in `watcher.rs`

#### OpenTelemetry Tracing

Rewatch supports OpenTelemetry (OTEL) tracing for build and watch commands. To visualize traces locally, run a Jaeger all-in-one container:

```bash
docker run -d --name jaeger \
  -p 4317:4317 -p 4318:4318 -p 16686:16686 \
  jaegertracing/all-in-one
```

Then run rewatch with the OTLP endpoint set:

```bash
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318 cargo run --manifest-path rewatch/Cargo.toml -- build
```

Open http://localhost:16686 to view traces in the Jaeger UI.

Note: Use `tracing::debug!` (not `log::debug!`) for events you want to appear in OTEL traces — they use separate logging systems.

##### Honored environment variables

Rewatch follows the OTEL spec for configuration — no rewatch-specific knobs exist.

| Variable | Purpose |
|---|---|
| `OTEL_EXPORTER_OTLP_ENDPOINT` | Base endpoint of the collector (e.g. `http://localhost:4318`). `/v1/traces` is appended for the trace exporter. Setting this (or `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT`) is what enables telemetry — if neither is set, tracing is a no-op. |
| `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT` | Full trace endpoint used verbatim. Overrides the general endpoint for traces. |
| `OTEL_EXPORTER_OTLP_HEADERS` | Extra headers on exporter requests (e.g. `authorization=Bearer xyz`). |
| `OTEL_SERVICE_NAME` | Service name reported on spans. Defaults to `rewatch`. |
| `OTEL_RESOURCE_ATTRIBUTES` | Comma-separated `key=value` pairs added as resource attributes (e.g. `deployment.environment=ci,host.name=$HOSTNAME`). |
| `RUST_LOG` | Controls which span/event levels are captured (e.g. `RUST_LOG=info`, `RUST_LOG=rewatch=debug`). Defaults to `debug` when telemetry is enabled. |

#### Running Rewatch Directly

When running the rewatch binary directly (via `cargo run` or the compiled binary) during development, point it at the local runtime. Otherwise, rewatch will try to use the installed version:

```bash
# Set the runtime path
export RESCRIPT_RUNTIME=$(realpath packages/@rescript/runtime)

# Now you can run rewatch directly
cargo run --manifest-path rewatch/Cargo.toml -- build
```

Builds compile in-process with the Rust compiler linked into rewatch: they
write the JavaScript plus the `.cmi`/`.cmt`/`.cmti` files editor tooling reads,
and need no `bsc` executable. One-shot builds recompile every module (watch
mode keeps state in memory).

Note that the dev binary is `./rewatch/target/debug/rescript`, not `rewatch`. The binary name is `rescript` because that's the package name in `Cargo.toml`.

This is useful when testing rewatch changes against local compiler modifications without running a full `make` build cycle.

Use `-v` for info-level logging or `-vv` for debug-level logging (e.g., to see which folders are being watched in watch mode):

```bash
cargo run --manifest-path rewatch/Cargo.toml -- -vv watch <folder>
```

#### Performance Considerations

- **Incremental Builds**: Only recompile dirty modules
- **Parallel Compilation**: Use `rayon` for parallel processing
- **Memory Usage**: Be mindful of `BuildState` size in large projects
- **File I/O**: Minimize file system operations

#### Performance vs Code Quality Trade-offs

When clippy suggests refactoring that could impact performance, consider the trade-offs:

- **Parameter Structs vs Many Arguments**: While clippy prefers parameter structs for functions with many arguments, sometimes the added complexity isn't worth it. Use `#[allow(clippy::too_many_arguments)]` for functions that legitimately need many parameters and where a struct would add unnecessary complexity.

- **Cloning vs Borrowing**: Sometimes cloning is necessary due to Rust's borrow checker rules. If the clone is:
  - Small and one-time (e.g., `Vec<String>` with few elements)
  - Necessary for correct ownership semantics
  - Not in a hot path

  Then accept the clone rather than over-engineering the solution.

- **When to Optimize**: Profile before optimizing. Most "performance concerns" in build systems are negligible compared to actual compilation time.

- **Avoid Unnecessary Type Conversions**: When threading parameters through multiple function calls, use consistent types (e.g., `String` throughout) rather than converting between `String` and `&str` at each boundary. This eliminates unnecessary allocations and conversions.

### Common Tasks

#### Adding New CLI Flags

1. Add to `BuildArgs` and `WatchArgs` in `cli.rs`
2. Update `From<BuildArgs> for WatchArgs` implementation
3. Pass through `main.rs` to build functions
4. Thread through build system to where it's needed
5. Add unit tests for the new functionality

#### Modifying Compiler Arguments

1. Update `compiler_args()` in `build/compile.rs`
2. Consider both parsing and compilation phases
3. Handle precedence between CLI flags and config
4. Test with various `rescript.json` configurations

#### Working with Dependencies

1. Use `packages.rs` for package discovery
2. Update `deps.rs` for dependency analysis
3. Handle both local and external dependencies
4. Consider dev dependencies vs regular dependencies

#### File Watching

1. Modify `watcher.rs` for file change handling
2. Update `AsyncWatchArgs` for new parameters
3. Handle different file types (`.res`, `.resi`, etc.)
4. Consider performance impact of watching many files

## CI Gotchas

- **`sleep` is fragile** — Prefer polling (e.g., `wait_for_file`) over fixed sleeps. CI runners are slower than local machines.
- **`exit_watcher` is async** — It only signals the watcher to stop (removes the lock file), it doesn't wait for the process to exit. Avoid triggering config-change events before exiting, as the watcher may start a concurrent rebuild.
- **`sed -i` differs across platforms** — macOS requires `sed -i '' ...`, Linux does not. Use the `replace` / `normalize_paths` helpers from `rewatch/tests/utils.sh` instead of raw `sed`.

---

## OCaml to Rust Compiler Rewrite

The compiler is being rewritten from OCaml to Rust. This is a major undertaking documented in the `compiler-rust/` directory.

### Rewrite Constraints

1. **No global state** - The Rust compiler must support concurrent compilation
2. **Drop-in replacement** - Must be backward compatible at all times
3. **Identical output** - JavaScript output must be byte-for-byte identical, and
   type checking must accept, reject and report the same programs (see
   "The Correctness Contract")

### Migration Phases

1. **Phase 1: Foundation** - Core types, contexts, FFI boundary (`compiler/ext/` → Rust)
2. **Phase 2: Parser** - ReScript parser in Rust (`compiler/syntax/` → Rust)
3. **Phase 3: Backend** - Lambda IR and JS generation (`compiler/core/` → Rust)
4. **Phase 4: Type Checker** - Type system in Rust (`compiler/ml/` → Rust)
5. **Phase 5: Integration** - Single Rust binary, OCaml removed

### Development Commands

```bash
# Build the Rust compiler crate
cargo build --manifest-path compiler-rust/Cargo.toml

# Run tests
cargo test --manifest-path compiler-rust/Cargo.toml

# Run tests with thread sanitizer (nightly)
RUSTFLAGS="-Z sanitizer=thread" cargo test --manifest-path compiler-rust/Cargo.toml

# Check for issues
cargo clippy --manifest-path compiler-rust/Cargo.toml --all-targets
```

Optimized builds of the `rescript` executable:

```bash
# The release profile: fat LTO. Use it for benchmarks and parity runs.
cargo build --release --manifest-path rewatch/Cargo.toml

# Thin LTO trades some runtime performance for faster optimized builds.
# Use it for iteration, not shipping or release-performance comparisons.
# Switching the LTO setting invalidates the existing build artifacts.
CARGO_PROFILE_RELEASE_LTO=thin cargo build --release --manifest-path rewatch/Cargo.toml

# What ships: a profile-guided build, two release builds long.
make rewatch-pgo
```

### Comparing Against the OCaml Compiler

When the Rust JavaScript or a diagnostic differs from OCaml, run both
compilers on the same `.res` file and compare layer by layer (`-dparsetree`,
`-dtypedtree`, `-drawlambda`, then the JavaScript) to find where the difference
starts. This is a debugging aid: a difference in an intermediate layer is fine
on its own. Fix the cause in the layer it starts in; do not patch the symptom in
a later one. Commit each fix on its own.

### Key Design Decisions

- **Thread-safe ID generation** - `IdGenerator` with `AtomicI32` instead of global `currentstamp`
- **Explicit contexts** - `CompilationContext`, `TypeContext` passed through pipeline
- **Arena-per-compilation** - Type arenas owned by `TypeContext`, not shared
- **No `static mut`** - All mutable state in explicit contexts
