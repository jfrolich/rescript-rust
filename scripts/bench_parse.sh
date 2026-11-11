#!/usr/bin/env bash
# Whole-process instruction counts; timed region excludes corpus loading.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release --manifest-path compiler-rust/Cargo.toml --example parse_bench
binary="${CARGO_TARGET_DIR:-compiler-rust/target}/release/examples/parse_bench"
iterations="${ITERATIONS:-1}"
work=$(mktemp -d)
trap 'rm -f "$work/counts" "$work/output"; rmdir "$work"' EXIT
for mode in scan parse; do
    echo "mode=$mode iterations=$iterations"
    args=(--mode "$mode" --iterations "$iterations" tests/tests/src packages/@rescript/runtime)
    if command -v valgrind >/dev/null 2>&1; then
        valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file="$work/counts" \
            "$binary" "${args[@]}" > "$work/output"
        cat "$work/output"
        awk -v iterations="$iterations" '
            /^files=/ { for (i=1; i<=NF; i++) if ($i ~ /^lines=/) { split($i,a,"="); lines=a[2] } }
            /^summary:/ { if (lines == 0) exit 1; printf "instructions=%s instructions_per_line=%.6f\n", $2, $2/(lines*iterations) }
        ' "$work/output" "$work/counts"
    else
        echo "valgrind unavailable: timing only (no instruction count)" >&2
        "$binary" "${args[@]}"
    fi
done
