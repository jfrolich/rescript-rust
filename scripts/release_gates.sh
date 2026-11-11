#!/bin/bash
# Run the Rust release validation gates locally, mirroring
# .github/workflows/rust-rewrite-validation.yml.
#
# Usage: ./scripts/release_gates.sh [--no-ocaml] [--skip-tests] [--with-tella]
#
#   --no-ocaml    Reuse the existing OCaml reference build (_build) and runtime.
#   --skip-tests  Skip `cargo test` for compiler-rust and rewatch.
#   --with-tella  Also run the external Tella output parity (TELLA_DIR).
#
# Each step logs to temp/release-gates/<step>.log; a summary is printed at the end.
# Exit status is non-zero when any step fails.

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$ROOT"

BUILD_OCAML=1
RUN_TESTS=1
RUN_TELLA=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --no-ocaml) BUILD_OCAML=0 ;;
        --skip-tests) RUN_TESTS=0 ;;
        --with-tella) RUN_TELLA=1 ;;
        -h|--help) sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
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
    # The OCaml bsc the reference builds use
    # (the hidden `rescript build-reference --bsc`).
    step ocaml-reference make compiler || { summary; exit 1; }
fi

step rust-build bash -c '
    cargo build --release --locked --manifest-path compiler-rust/Cargo.toml &&
    cargo build --release --locked --manifest-path rewatch/Cargo.toml &&
    ./scripts/rust_compiler_shims.sh release' || { summary; exit 1; }


# The compiler unit fixtures compile tests/tests sources file by file against
# .cmi files, which only the OCaml reference build writes.
step fixtures env PROJECT_ROOT="$ROOT" RUST_TARGET=release bash -c \
    'source scripts/parity_lib.sh && parity_build_ocaml_reference "$PROJECT_ROOT/tests/tests"'

if [[ $RUN_TESTS -eq 1 ]]; then
    step cargo-test-compiler cargo test --release --locked --manifest-path compiler-rust/Cargo.toml
    step cargo-test-rewatch cargo test --release --locked --manifest-path rewatch/Cargo.toml
fi

step js ./scripts/test_js_output_parity.sh --release
step errors env -u OCAMLRUNPARAM -u RUST_BACKTRACE ./scripts/test_error_output_parity.sh --release
step stdlib env RUST_TARGET=release ./scripts/test_stdlib_output_parity.sh
step gentype env GENTYPE_PARITY_WITHOUT_TELLA=1 \
    REWATCH_BIN="$ROOT/rewatch/target/release/rescript" \
    RUST_BSC="$ROOT/rewatch/target/release/bsc" \
    ./scripts/test_gentype_output_parity.sh
if [[ $RUN_TELLA -eq 1 ]]; then
    step tella ./scripts/test_tella_output_parity.sh --release
fi

summary
exit $FAILED
