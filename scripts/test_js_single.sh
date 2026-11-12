#!/bin/bash
# Quick single-file JS output parity test
#
# Usage:
#   ./scripts/test_js_single.sh src/adt_optimize_test.res
#   ./scripts/test_js_single.sh adt_optimize_test          # auto-finds .res
#   ./scripts/test_js_single.sh src/adt_optimize_test.res --diff   # show diff
#   ./scripts/test_js_single.sh src/adt_optimize_test.res --rust   # show Rust output
#   ./scripts/test_js_single.sh src/adt_optimize_test.res --expected  # show expected
#
# Compiles a single .res file with Rust bsc, diffs against the OCaml snapshot.
# Exits 0 on match, 1 on diff, 2 on compile error.

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)

RUST_TARGET="${RUST_TARGET:-debug}"
RUST_BSC="$project_root/rewatch/target/$RUST_TARGET/bsc"
"$project_root/scripts/rust_compiler_shims.sh" "$RUST_TARGET"
RESCRIPT_CLI="$project_root/packages/@rescript/$($script_dir/platform.sh)/bin/rescript.exe"
TESTS_DIR="$project_root/tests/tests"
TIMEOUT_SECONDS=10
SHOW_MODE=""

# Parse args
file_arg=""
for arg in "$@"; do
    case "$arg" in
        --diff) SHOW_MODE="diff" ;;
        --rust) SHOW_MODE="rust" ;;
        --expected) SHOW_MODE="expected" ;;
        --help|-h)
            echo "Usage: $0 <file> [--diff|--rust|--expected]"
            echo ""
            echo "  <file>       .res file (relative to tests/tests/, or just module name)"
            echo "  --diff       Show unified diff between expected and actual"
            echo "  --rust       Show Rust compiler output"
            echo "  --expected   Show expected OCaml output"
            exit 0 ;;
        *) file_arg="$arg" ;;
    esac
done

if [[ -z "$file_arg" ]]; then
    echo "Usage: $0 <file> [--diff|--rust|--expected]"
    exit 1
fi

# Resolve the file path
res_file=""
if [[ -f "$TESTS_DIR/$file_arg" ]]; then
    res_file="$file_arg"
elif [[ -f "$TESTS_DIR/src/${file_arg}" ]]; then
    res_file="src/${file_arg}"
elif [[ -f "$TESTS_DIR/src/${file_arg}.res" ]]; then
    res_file="src/${file_arg}.res"
elif [[ -f "$file_arg" ]]; then
    res_file="$file_arg"
else
    echo "Could not find: $file_arg"
    echo "Tried: $TESTS_DIR/$file_arg, $TESTS_DIR/src/$file_arg, $TESTS_DIR/src/${file_arg}.res"
    exit 1
fi

cd "$TESTS_DIR"

# Find expected snapshot
expected_file="${res_file%.res}.mjs"
if [[ ! -f "$expected_file" ]]; then
    expected_file="${res_file%.res}.bs.js"
fi
if [[ ! -f "$expected_file" ]]; then
    echo "No expected snapshot for $res_file"
    echo "Looked for: ${res_file%.res}.mjs and ${res_file%.res}.bs.js"
    exit 2
fi

# Get compiler args from project
full_res="$TESTS_DIR/$res_file"
compiler_args=()

find_project_root() {
    local d
    d=$(dirname "$1")
    while [[ "$d" != "/" && -n "$d" ]]; do
        if [[ -f "$d/rescript.json" || -f "$d/bsconfig.json" ]] && [[ -d "$d/lib/rescript" ]]; then
            echo "$d"
            return 0
        fi
        d=$(dirname "$d")
    done
    return 1
}

project_dir=$(find_project_root "$full_res") || project_dir=""
if [[ -n "$project_dir" && -x "$RESCRIPT_CLI" ]]; then
    args_json=$("$RESCRIPT_CLI" compiler-args "$full_res" 2>/dev/null) || args_json=""
    if [[ -n "$args_json" ]]; then
        while IFS= read -r arg; do
            compiler_args+=("$arg")
        done < <(printf '%s' "$args_json" | python3 -c 'import json,sys; [print(arg) for arg in json.load(sys.stdin).get("compiler_args", [])]')
    fi
fi

# Compile with Rust
tmp_dir=$(mktemp -d)

cleanup_dir_tree() {
    local dir="$1"
    [[ -n "$dir" && -d "$dir" ]] || return 0
    find "$dir" -type f -exec rm -f {} + 2>/dev/null || true
    find "$dir" -type l -exec rm -f {} + 2>/dev/null || true
    find "$dir" -depth -type d -empty -exec rmdir {} \; 2>/dev/null || true
}

output_name=$(basename "$expected_file")
actual_file="$tmp_dir/$output_name"
compile_output="$tmp_dir/compile.txt"

compile_ok=false
if [[ "${#compiler_args[@]}" -gt 0 && -d "$project_dir/lib/rescript" ]]; then
    if (cd "$project_dir/lib/rescript" && timeout "$TIMEOUT_SECONDS" "$RUST_BSC" "${compiler_args[@]}" -o "$actual_file") > "$compile_output" 2>&1; then
        compile_ok=true
    fi
else
    ext="${expected_file##*.}"
    if [[ "$ext" == "mjs" ]]; then
        if timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-package-name rescript-tests -bs-module-type esmodule "$res_file" -o "$actual_file" > "$compile_output" 2>&1; then
            compile_ok=true
        fi
    else
        if timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-package-name rescript-tests "$res_file" -o "$actual_file" > "$compile_output" 2>&1; then
            compile_ok=true
        fi
    fi
fi

if ! $compile_ok; then
    echo "COMPILE ERROR: $res_file"
    cat "$compile_output"
    cleanup_dir_tree "$tmp_dir"
    exit 2
fi

if [[ ! -f "$actual_file" ]]; then
    echo "NO OUTPUT: $res_file (compiled but no .js file produced)"
    cat "$compile_output"
    cleanup_dir_tree "$tmp_dir"
    exit 2
fi

# Show requested output
case "$SHOW_MODE" in
    diff)
        diff -u "$expected_file" "$actual_file" || true
        ;;
    rust)
        cat "$actual_file"
        ;;
    expected)
        cat "$expected_file"
        ;;
    *)
        if diff -q "$expected_file" "$actual_file" > /dev/null 2>&1; then
            echo "PASS: $res_file"
            cleanup_dir_tree "$tmp_dir"
            exit 0
        else
            echo "FAIL: $res_file"
            hunks=$(diff -u "$expected_file" "$actual_file" | grep -c '^@@' || true)
            echo "  $hunks hunks differ"
            echo ""
            echo "  Quick commands:"
            echo "    $0 $res_file --diff       # see diff"
            echo "    $0 $res_file --rust       # see Rust output"
            echo "    $0 $res_file --expected   # see OCaml output"
            cleanup_dir_tree "$tmp_dir"
            exit 1
        fi
        ;;
esac

cleanup_dir_tree "$tmp_dir"
