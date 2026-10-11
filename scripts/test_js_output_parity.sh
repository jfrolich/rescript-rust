#!/bin/bash

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)
include_external=false
include_spice_ppx=false
fixture_args=()
local_args=()
tella_args=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --with-external)
            include_external=true
            shift
            ;;
        --with-spice-ppx)
            include_spice_ppx=true
            shift
            ;;
        --release)
            fixture_args+=("$1")
            local_args+=("$1")
            tella_args+=("$1")
            shift
            ;;
        -q|--quick)
            fixture_args+=("$1")
            tella_args+=("$1")
            shift
            ;;
        *)
            fixture_args+=("$1")
            local_args+=("$1")
            tella_args+=("$1")
            shift
            ;;
    esac
done

if [[ "${fixture_args[0]:-}" == "--help" || "${fixture_args[0]:-}" == "-h" ]]; then
    echo "Usage: $0 [--with-external] [--release] [test_rust_parity.sh options]"
    echo ""
    echo "Runs the dedicated JS output parity mode using the existing Rust parity harness."
    echo "By default it checks focused JS output fixtures and the canonical in-repo"
    echo "JS snapshot suite under tests/tests/src."
    echo "This skips parser AST, syntax, and Spice PPX AST parity sections."
    echo "With --with-external, local tests still use the per-file harness, while Tella"
    echo "is compared as an OCaml reference build against an in-process rescript build."
    echo ""
    echo "Options:"
    echo "  --with-external  Include the external corpus via TELLA_DIR as well."
    echo "  --with-spice-ppx Also run Spice PPX AST parity through test_rust_parity.sh."
    echo "  --release        Use target/release Rust compiler and rewatch artifacts."
    echo "  -q, --quick      Stop early in focused fixtures and external Tella build."
    echo ""
    echo "Equivalent to:"
    echo "  TELLA_DIR=$project_root/.no_external_js_corpus ./scripts/test_rust_parity.sh --skip-parser-ast --skip-syntax --skip-spice-ppx [options]"
    exit 0
fi

if [[ "$include_spice_ppx" != "true" ]]; then
    local_args+=("--skip-spice-ppx")
fi

if [[ "$include_external" == "true" ]]; then
    set +e
    "$project_root/scripts/test_js_output_parity_fixtures.sh" "${fixture_args[@]}"
    fixture_status=$?

    TELLA_DIR="$project_root/.no_external_js_corpus" \
        "$project_root/scripts/test_rust_parity.sh" --skip-parser-ast --skip-syntax "${local_args[@]}"
    local_status=$?

    "$project_root/scripts/test_tella_output_parity.sh" "${tella_args[@]}"
    tella_status=$?
    set -e

    if [[ "$fixture_status" -ne 0 ]]; then
        exit "$fixture_status"
    fi
    if [[ "$local_status" -ne 0 ]]; then
        exit "$local_status"
    fi
    exit "$tella_status"
fi

set +e
"$project_root/scripts/test_js_output_parity_fixtures.sh" "${fixture_args[@]}"
fixture_status=$?

TELLA_DIR="$project_root/.no_external_js_corpus" \
    "$project_root/scripts/test_rust_parity.sh" --skip-parser-ast --skip-syntax "${local_args[@]}"
local_status=$?
set -e

if [[ "$fixture_status" -ne 0 ]]; then
    exit "$fixture_status"
fi
exit "$local_status"
