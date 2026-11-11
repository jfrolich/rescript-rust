#!/bin/bash
# Fast JS parity retest — only tests previously-failing files
#
# Usage:
#   ./scripts/test_js_failing.sh              # retest only failing files from last full run
#   ./scripts/test_js_failing.sh --update     # retest and update the passlist cache
#   ./scripts/test_js_failing.sh --category "temp-var-naming"  # only test files in a triage category
#
# This script reads the diff files from the last full parity run (temp/rust-parity/diffs/)
# and only re-compiles those files. ~10x faster than a full run.
#
# Workflow:
#   1. Run full suite once:    ./scripts/test_js_output_parity.sh
#   2. Triage failures:        ./scripts/triage_js_failures.sh
#   3. Fix a root cause
#   4. Rebuild:                cargo build --manifest-path rewatch/Cargo.toml
#   5. Fast retest:            ./scripts/test_js_failing.sh
#   6. Repeat 3-5 until category is clear
#   7. Full suite to confirm:  ./scripts/test_js_output_parity.sh

set -e

script_dir=$(cd "$(dirname "$0")"; pwd -P)
project_root=$(cd "$script_dir/.."; pwd -P)

RUST_TARGET="${RUST_TARGET:-debug}"
RUST_BSC="$project_root/rewatch/target/$RUST_TARGET/bsc"
"$project_root/scripts/rust_compiler_shims.sh" "$RUST_TARGET"
RESCRIPT_CLI="$project_root/packages/@rescript/$($script_dir/platform.sh)/bin/rescript.exe"
TESTS_DIR="$project_root/tests/tests"
DIFF_DIR="$project_root/temp/rust-parity/diffs"
TIMEOUT_SECONDS=10
UPDATE_PASSLIST=false
CATEGORY_FILTER=""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

while [[ $# -gt 0 ]]; do
    case "$1" in
        --update) UPDATE_PASSLIST=true; shift ;;
        --category) CATEGORY_FILTER="$2"; shift 2 ;;
        -h|--help)
            echo "Usage: $0 [--update] [--category PATTERN]"
            echo ""
            echo "  --update            Update passlist after retesting"
            echo "  --category PATTERN  Only retest files matching a triage category"
            echo "                      (matches against the diff filename, e.g. 'mario' or 'test_list')"
            exit 0 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if [[ ! -d "$DIFF_DIR" ]]; then
    echo "No diffs found. Run the full suite first:"
    echo "  ./scripts/test_js_output_parity.sh"
    exit 1
fi

# Collect failing files from existing diffs
failing_files=()
for diff_file in "$DIFF_DIR"/js_src_*.diff; do
    [[ -f "$diff_file" ]] || continue
    # Extract: js_src_foo_test.res.diff → src/foo_test.res
    base=$(basename "$diff_file" .diff)
    base="${base#js_}"         # remove js_ prefix
    res_file="${base//_/\/}.res"  # This is approximate; handle edge cases below

    # The diff files use _ as separator but filenames may have _
    # Better: extract from the diff header
    expected=$(head -1 "$diff_file" | sed 's/^--- //' | awk '{print $1}')
    if [[ -n "$expected" && -f "$TESTS_DIR/$expected" ]]; then
        res_file="${expected%.mjs}.res"
        [[ -f "$TESTS_DIR/$res_file" ]] || res_file="${expected%.bs.js}.res"
    fi

    if [[ -n "$CATEGORY_FILTER" ]]; then
        if [[ "$base" != *"$CATEGORY_FILTER"* ]]; then
            continue
        fi
    fi

    if [[ -f "$TESTS_DIR/$res_file" ]]; then
        failing_files+=("$res_file")
    fi
done

if [[ ${#failing_files[@]} -eq 0 ]]; then
    echo -e "${GREEN}No failing files to retest!${RESET}"
    exit 0
fi

echo -e "${BOLD}Retesting ${#failing_files[@]} previously-failing files...${RESET}"
echo ""

cd "$TESTS_DIR"

pass_count=0
fail_count=0
error_count=0
newly_passing=()
still_failing=()

cleanup_dir_tree() {
    local dir="$1"
    [[ -n "$dir" && -d "$dir" ]] || return 0
    find "$dir" -type f -exec rm -f {} + 2>/dev/null || true
    find "$dir" -type l -exec rm -f {} + 2>/dev/null || true
    find "$dir" -depth -type d -empty -exec rmdir {} \; 2>/dev/null || true
}

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

for res_file in "${failing_files[@]}"; do
    full_res="$TESTS_DIR/$res_file"

    # Find expected
    expected_file="${res_file%.res}.mjs"
    [[ -f "$expected_file" ]] || expected_file="${res_file%.res}.bs.js"
    [[ -f "$expected_file" ]] || continue

    # Get compiler args
    compiler_args=()
    project_dir=$(find_project_root "$full_res") || project_dir=""
    if [[ -n "$project_dir" && -x "$RESCRIPT_CLI" ]]; then
        args_json=$("$RESCRIPT_CLI" compiler-args "$full_res" 2>/dev/null) || args_json=""
        if [[ -n "$args_json" ]]; then
            while IFS= read -r arg; do
                compiler_args+=("$arg")
            done < <(printf '%s' "$args_json" | python3 -c 'import json,sys; [print(arg) for arg in json.load(sys.stdin).get("compiler_args", [])]')
        fi
    fi

    # Compile
    tmp_dir=$(mktemp -d)
    output_name=$(basename "$expected_file")
    actual_file="$tmp_dir/$output_name"
    compile_output="$tmp_dir/compile.txt"

    compile_ok=false
    if [[ "${#compiler_args[@]}" -gt 0 && -n "$project_dir" && -d "$project_dir/lib/rescript" ]]; then
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

    if ! $compile_ok || [[ ! -f "$actual_file" ]]; then
        error_count=$((error_count + 1))
        still_failing+=("$res_file (compile error)")
        cleanup_dir_tree "$tmp_dir"
        continue
    fi

    if diff -q "$expected_file" "$actual_file" > /dev/null 2>&1; then
        pass_count=$((pass_count + 1))
        newly_passing+=("$res_file")
        # Remove the diff file since it now passes
        if $UPDATE_PASSLIST; then
            safe=$(echo "$res_file" | tr '/' '_')
            rm -f "$DIFF_DIR/js_${safe}.diff"
        fi
    else
        fail_count=$((fail_count + 1))
        still_failing+=("$res_file")
        # Update the diff file
        safe=$(echo "$res_file" | tr '/' '_')
        diff -u "$expected_file" "$actual_file" > "$DIFF_DIR/js_${safe}.diff" 2>&1 || true
    fi

    cleanup_dir_tree "$tmp_dir"
done

# Report
echo -e "${BOLD}Results${RESET}"
echo "========"
total=$((pass_count + fail_count + error_count))
echo -e "Retested:     $total files"
echo -e "Now passing:  ${GREEN}$pass_count${RESET}"
echo -e "Still failing: ${RED}$fail_count${RESET}"
if [[ $error_count -gt 0 ]]; then
    echo -e "Errors:       ${RED}$error_count${RESET}"
fi

if [[ ${#newly_passing[@]} -gt 0 ]]; then
    echo ""
    echo -e "${GREEN}Newly passing:${RESET}"
    for f in "${newly_passing[@]}"; do
        echo "  + $f"
    done
fi

if [[ ${#still_failing[@]} -gt 0 && ${#still_failing[@]} -le 20 ]]; then
    echo ""
    echo -e "${YELLOW}Still failing:${RESET}"
    for f in "${still_failing[@]}"; do
        echo "  - $f"
    done
fi

echo ""
remaining_diffs=$(ls "$DIFF_DIR"/js_src_*.diff 2>/dev/null | wc -l | tr -d ' ')
echo -e "Total remaining failures: ${BOLD}$remaining_diffs${RESET}"
