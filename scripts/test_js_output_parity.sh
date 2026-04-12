#!/bin/bash

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)
include_external=false
forward_args=()

while [[ $# -gt 0 ]]; do
    case "$1" in
        --with-external)
            include_external=true
            shift
            ;;
        *)
            forward_args+=("$1")
            shift
            ;;
    esac
done

if [[ "${forward_args[0]:-}" == "--help" || "${forward_args[0]:-}" == "-h" ]]; then
    echo "Usage: $0 [--with-external] [test_rust_parity.sh options]"
    echo ""
    echo "Runs the dedicated JS output parity mode using the existing Rust parity harness."
    echo "By default it only checks the canonical 657 files under tests/tests/src."
    echo "This keeps Spice PPX parity enabled and skips only parser AST and syntax sections."
    echo ""
    echo "Options:"
    echo "  --with-external  Include the external corpus via TELLA_DIR as well."
    echo ""
    echo "Equivalent to:"
    echo "  TELLA_DIR=$project_root/.no_external_js_corpus ./scripts/test_rust_parity.sh --skip-parser-ast --skip-syntax [options]"
    exit 0
fi

if [[ "$include_external" == "true" ]]; then
    exec "$project_root/scripts/test_rust_parity.sh" --skip-parser-ast --skip-syntax "${forward_args[@]}"
fi

TELLA_DIR="$project_root/.no_external_js_corpus" \
    exec "$project_root/scripts/test_rust_parity.sh" --skip-parser-ast --skip-syntax "${forward_args[@]}"
