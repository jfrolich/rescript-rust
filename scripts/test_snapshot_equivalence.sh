#!/usr/bin/env bash
# Compare snapshot/source JavaScript, diagnostics and dependent stored records.
set -euo pipefail
exec python3 "$(dirname "$0")/test_snapshot_equivalence.py" "$@"
