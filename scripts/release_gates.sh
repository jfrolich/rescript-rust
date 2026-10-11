#!/bin/bash
# Run the Rust release validation gates locally, mirroring
# .github/workflows/rust-rewrite-validation.yml.
#
# Usage: ./scripts/release_gates.sh [--no-ocaml]
#
#   --no-ocaml    Reuse the existing OCaml build (_build) and runtime.
#
# Each step logs to temp/release-gates/<step>.log; a summary is printed at the end.
# Exit status is non-zero when any step fails.

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$ROOT"

BUILD_OCAML=1
while [[ $# -gt 0 ]]; do
    case "$1" in
        --no-ocaml) BUILD_OCAML=0 ;;
        -h|--help) sed -n '2,10p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) echo "Unknown option: $1" >&2; exit 2 ;;
    esac
    shift
done

LOG_DIR="$ROOT/temp/release-gates"
mkdir -p "$LOG_DIR"
RESULTS=()
FAILED=0

step() {
    local name=$1
    shift
    local log="$LOG_DIR/$name.log"
    local start=$SECONDS
    echo "=== $name"
    "$@" >"$log" 2>&1
    local rc=$?
    local status=ok
    if [[ $rc -ne 0 ]]; then
        status="FAILED (rc=$rc)"
        FAILED=1
    fi
    RESULTS+=("$(printf '%-22s %-16s %5ss' "$name" "$status" "$((SECONDS - start))")")
    tail -n 5 "$log"
    return $rc
}

summary() {
    echo
    echo "===== Summary (logs in $LOG_DIR)"
    printf '%s\n' "${RESULTS[@]}"
}

if [[ $BUILD_OCAML -eq 1 ]]; then
    step ocaml-build make lib || { summary; exit 1; }
fi

step rust-build bash -c '
    cargo build --release --locked --manifest-path compiler-rust/Cargo.toml &&
    cargo build --release --locked --manifest-path rewatch/Cargo.toml' || { summary; exit 1; }

# The compiler unit tests read the compiled tests/tests corpus.
step fixtures env \
    RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime" \
    ./rewatch/target/release/rescript build tests/tests

step cargo-test-compiler cargo test --release --locked --manifest-path compiler-rust/Cargo.toml
step cargo-test-rewatch cargo test --release --locked --manifest-path rewatch/Cargo.toml

summary
exit $FAILED
