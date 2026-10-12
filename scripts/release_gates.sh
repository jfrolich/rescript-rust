#!/bin/bash
# Run the Rust release validation gates locally, mirroring
# .github/workflows/rust-rewrite-validation.yml.
#
# Usage: ./scripts/release_gates.sh [--no-ocaml] [--skip-tests] [--with-tella] [--parallel N]
#
#   --no-ocaml    Reuse the existing OCaml reference build (_build) and runtime.
#   --skip-tests  Skip `cargo test` for compiler-rust and rewatch.
#   --with-tella  Also run the external Tella output parity (TELLA_DIR).
#   --parallel N  Parallelism for the typedtree/lambda parity scripts (default 4).
#
# Each step logs to temp/release-gates/<step>.log; a summary is printed at the end.
# Exit status is non-zero when any step fails.

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$ROOT"

BUILD_OCAML=1
RUN_TESTS=1
RUN_TELLA=0
PARALLEL=4
while [[ $# -gt 0 ]]; do
    case "$1" in
        --no-ocaml) BUILD_OCAML=0 ;;
        --skip-tests) RUN_TESTS=0 ;;
        --with-tella) RUN_TELLA=1 ;;
        --parallel) PARALLEL=$2; shift ;;
        -h|--help) sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
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
    # The OCaml bsc the parity scripts build their reference with
    # (the hidden `rescript build-reference --bsc`).
    step ocaml-reference make compiler || { summary; exit 1; }
fi

step rust-build bash -c '
    cargo build --release --locked --manifest-path compiler-rust/Cargo.toml &&
    cargo build --release --locked --manifest-path rewatch/Cargo.toml &&
    ./scripts/rust_compiler_shims.sh release' || { summary; exit 1; }


step fixtures env RESCRIPT_RUNTIME="$ROOT/packages/@rescript/runtime" \
    ./rewatch/target/release/rescript build tests/tests

if [[ $RUN_TESTS -eq 1 ]]; then
    step cargo-test-compiler cargo test --release --locked --manifest-path compiler-rust/Cargo.toml
    step cargo-test-rewatch cargo test --release --locked --manifest-path rewatch/Cargo.toml
fi

step typedtree ./scripts/test_typedtree_parity.sh --release --parallel "$PARALLEL"
step raw-lambda ./scripts/test_lambda_parity.sh --release --raw --parallel "$PARALLEL"
step lambda ./scripts/test_lambda_parity.sh --release --parallel "$PARALLEL"
step js ./scripts/test_js_output_parity.sh --release
step errors env -u OCAMLRUNPARAM -u RUST_BACKTRACE ./scripts/test_error_output_parity.sh --release
if [[ $RUN_TELLA -eq 1 ]]; then
    step tella ./scripts/test_tella_output_parity.sh --release
fi

summary
exit $FAILED
