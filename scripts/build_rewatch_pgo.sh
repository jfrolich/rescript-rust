#!/bin/bash
# Build a profile-guided (PGO) release build of rewatch, whose in-process
# compiler runs the whole build in one process.
#
# 1. Build an instrumented rewatch in rewatch/target/pgo/instrumented.
# 2. Train it by compiling a copy of tests/tests in-process (a clean build,
#    several times).
# 3. Merge the raw profiles and rebuild rewatch/target/release/rescript with
#    -Cprofile-use.
#
# Needs the llvm-tools rustup component (`rustup component add llvm-tools`).
# The final binary replaces the normal release build; a later plain
# `cargo build --release` rebuilds it without PGO because RUSTFLAGS differ.
#
# Usage: scripts/build_rewatch_pgo.sh [--runs N]
set -euo pipefail

RUNS=3
while [[ $# -gt 0 ]]; do
    case "$1" in
        --runs)
            RUNS="$2"
            shift 2
            ;;
        *)
            echo "Unknown argument: $1" >&2
            exit 2
            ;;
    esac
done

script_dir=$(cd "$(dirname "$0")"; pwd -P)
PROJECT_ROOT=$(cd "$script_dir/.."; pwd -P)
PGO_DIR="$PROJECT_ROOT/rewatch/target/pgo"
PROFILE_DIR="$PGO_DIR/profiles"
TRAIN_DIR="$PGO_DIR/train-tests"
INSTRUMENTED_TARGET="$PGO_DIR/instrumented"
MERGED="$PGO_DIR/merged.profdata"

SYSROOT=$(rustc --print sysroot)
HOST=$(rustc -vV | sed -n 's/^host: //p')
LLVM_PROFDATA="$SYSROOT/lib/rustlib/$HOST/bin/llvm-profdata"
if [[ ! -x "$LLVM_PROFDATA" ]]; then
    echo "llvm-profdata not found at $LLVM_PROFDATA; run: rustup component add llvm-tools" >&2
    exit 1
fi

echo "==> Building instrumented rewatch"
mkdir -p "$PROFILE_DIR"
find "$PROFILE_DIR" -name '*.profraw' -type f -delete
CARGO_TARGET_DIR="$INSTRUMENTED_TARGET" \
    RUSTFLAGS="-Cprofile-generate=$PROFILE_DIR" \
    cargo build --release --manifest-path "$PROJECT_ROOT/rewatch/Cargo.toml"

# Train on a copy so the checked-in tests/tests outputs are not rewritten. The
# copy stays inside the repository so @rescript/react still resolves from the
# root node_modules.
echo "==> Preparing training project"
mkdir -p "$TRAIN_DIR"
rsync -a --delete --exclude node_modules --exclude lib "$PROJECT_ROOT/tests/tests/" "$TRAIN_DIR/"

export RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
INSTRUMENTED="$INSTRUMENTED_TARGET/release/rescript"
echo "==> Training ($RUNS clean in-process builds)"
for _ in $(seq "$RUNS"); do
    "$INSTRUMENTED" clean "$TRAIN_DIR" > /dev/null
    LLVM_PROFILE_FILE="$PROFILE_DIR/%p-%m.profraw" "$INSTRUMENTED" build "$TRAIN_DIR" > /dev/null
done

echo "==> Merging profiles"
"$LLVM_PROFDATA" merge -o "$MERGED" "$PROFILE_DIR"/*.profraw

echo "==> Building PGO-optimized rewatch"
RUSTFLAGS="-Cprofile-use=$MERGED" \
    cargo build --release --manifest-path "$PROJECT_ROOT/rewatch/Cargo.toml"

echo "PGO build ready: $PROJECT_ROOT/rewatch/target/release/rescript"
