#!/bin/bash

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
    echo "Usage: $0 [test_rust_parity.sh options]"
    echo ""
    echo "Runs the dedicated JS output parity mode using the existing Rust parity harness."
    echo "This keeps Spice PPX parity enabled and skips only parser AST and syntax sections."
    echo ""
    echo "Equivalent to:"
    echo "  ./scripts/test_rust_parity.sh --skip-parser-ast --skip-syntax [options]"
    exit 0
fi

exec "$project_root/scripts/test_rust_parity.sh" --skip-parser-ast --skip-syntax "$@"
