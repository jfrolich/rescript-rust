#!/bin/bash

# Runtime/stdlib JS output parity: build the runtime package in process with
# `rescript build`, then with the OCaml bsc (`rescript build-reference`), and
# compare the CommonJS/ESM output of each implementation module.
#
# Usage:
#   ./scripts/test_stdlib_output_parity.sh [OPTIONS] [FILE|PATTERN]
#
# Options:
#   --reformat       Normalize JavaScript (default: exact)
#   -q, --quick       Stop on first failure
#   -v, --verbose     Show progress for each file
#   -h, --help        Show this help message

set -e

QUICK_MODE=false
VERBOSE=false
FILE_ARG=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --reformat)
            PARITY_COMPARE_MODE=reformat
            shift
            ;;
        -q|--quick)
            QUICK_MODE=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            sed -n '4,14p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            FILE_ARG="$1"
            shift
            ;;
    esac
done

script_dir=$(cd "$(dirname "$0")"; pwd -P)
PROJECT_ROOT=$(cd "$script_dir/.."; pwd -P)
RUNTIME_DIR="$PROJECT_ROOT/packages/@rescript/runtime"
RUST_TARGET="${RUST_TARGET:-debug}"
source "$PROJECT_ROOT/scripts/parity_lib.sh"
parity_init_comparison
CACHE_DIR="$PROJECT_ROOT/.parity-cache/stdlib-output"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    exit 1
fi

if [[ ! -x "$RESCRIPT_CLI" ]]; then
    echo -e "${RED}Error: rescript CLI not found at $RESCRIPT_CLI${RESET}"
    exit 1
fi

if [[ ! -f "$RUNTIME_DIR/rescript.json" ]]; then
    echo -e "${RED}Error: runtime rescript.json not found at $RUNTIME_DIR${RESET}"
    exit 1
fi

TEMP_DIR=$(mktemp -d)
find "$CACHE_DIR" -type f -delete 2>/dev/null || true
mkdir -p "$CACHE_DIR/diffs" "$CACHE_DIR/errors" "$CACHE_DIR/rust"

cleanup_temp_dir() {
    if [[ -n "${TEMP_DIR:-}" && -d "$TEMP_DIR" ]]; then
        find "$TEMP_DIR" -type f -delete 2>/dev/null || true
        find "$TEMP_DIR" -depth -type d -empty -delete 2>/dev/null || true
        rmdir "$TEMP_DIR" 2>/dev/null || true
    fi
}
trap cleanup_temp_dir EXIT

echo -e "${BOLD}Stdlib JS Output Parity${RESET}"
echo "============================================"
echo "Runtime project: $RUNTIME_DIR"
echo "OCaml bsc:       $OCAML_BSC"
echo "rescript:        $RESCRIPT_CLI"
echo "Artifact cache:  $CACHE_DIR"
echo ""

# Copy the runtime's generated JavaScript to $1/{js,es6}.
snapshot_js() {
    mkdir -p "$1/js" "$1/es6"
    find "$RUNTIME_DIR/lib/js" -maxdepth 1 -name '*.cjs' -exec cp {} "$1/js/" \; 2>/dev/null || true
    find "$RUNTIME_DIR/lib/es6" -maxdepth 1 -name '*.mjs' -exec cp {} "$1/es6/" \; 2>/dev/null || true
}

echo -e "${BOLD}Step 1: Building stdlib/runtime in process with rescript...${RESET}"
if ! RESCRIPT_RUNTIME="$RUNTIME_DIR" "$RESCRIPT_CLI" build "$RUNTIME_DIR" > "$CACHE_DIR/errors/rust-build.err" 2>&1; then
    echo -e "${YELLOW}Warning: the in-process build reported errors (see $CACHE_DIR/errors/rust-build.err)${RESET}"
fi
snapshot_js "$TEMP_DIR/rust"
echo -e "${BOLD}Step 2: Building stdlib/runtime with OCaml bsc...${RESET}"
RESCRIPT_RUNTIME="$RUNTIME_DIR" "$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" "$RUNTIME_DIR" 2>&1 | tail -5
snapshot_js "$TEMP_DIR/ocaml"
echo ""

if [[ -n "$FILE_ARG" ]]; then
    if [[ -f "$FILE_ARG" ]]; then
        printf '%s\n' "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$RUNTIME_DIR/$FILE_ARG" ]]; then
        printf '%s\n' "$RUNTIME_DIR/$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$RUNTIME_DIR/${FILE_ARG}.res" ]]; then
        printf '%s\n' "$RUNTIME_DIR/${FILE_ARG}.res" > "$TEMP_DIR/files.txt"
    else
        find "$RUNTIME_DIR" -maxdepth 1 -name "*.res" -type f 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
    fi
else
    find "$RUNTIME_DIR" -maxdepth 1 -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
fi

if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
    echo -e "${RED}Error: no runtime implementation files found${RESET}"
    exit 1
fi

TOTAL_FILES=$(wc -l < "$TEMP_DIR/files.txt" | tr -d ' ')
echo "Testing $TOTAL_FILES implementation files"
echo ""

pass_count=0
diff_count=0
compile_error_count=0
missing_output_count=0
skipped_count=0
failed_files=""

while IFS= read -r file; do
    [[ -n "$file" ]] || continue
    full_file="$file"
    if [[ "$full_file" != /* ]]; then
        full_file="$PROJECT_ROOT/$full_file"
    fi
    rel_path="${full_file#$RUNTIME_DIR/}"
    module_name=$(basename "$rel_path" .res)
    safe_name=$(echo "$rel_path" | tr '/:' '__')
    expected_cjs="$TEMP_DIR/ocaml/js/${module_name}.cjs"
    expected_mjs="$TEMP_DIR/ocaml/es6/${module_name}.mjs"
    actual_cjs="$TEMP_DIR/rust/js/${module_name}.cjs"
    actual_mjs="$TEMP_DIR/rust/es6/${module_name}.mjs"
    diff_file="$CACHE_DIR/diffs/${safe_name}.diff"

    if [[ ! -f "$expected_cjs" && ! -f "$expected_mjs" ]]; then
        skipped_count=$((skipped_count + 1))
        continue
    fi
    if [[ ! -f "$actual_cjs" && ! -f "$actual_mjs" ]]; then
        compile_error_count=$((compile_error_count + 1))
        failed_files="$failed_files$rel_path (no Rust output)\n"
        if [[ "$QUICK_MODE" == "true" ]]; then
            echo -e "${RED}Quick mode: stopping on missing Rust output${RESET}"
            exit 1
        fi
        continue
    fi

    file_failed=false
    : > "$diff_file"

    if [[ -f "$expected_cjs" ]]; then
        if [[ ! -f "$actual_cjs" ]]; then
            missing_output_count=$((missing_output_count + 1))
            failed_files="$failed_files$rel_path (missing CommonJS output)\n"
            printf 'missing output: %s\n' "$actual_cjs" >> "$diff_file"
            file_failed=true
        elif ! parity_compare_js "$expected_cjs" "$actual_cjs" >> "$diff_file" 2>&1; then
            printf '%s\n' "--- CommonJS: $module_name ---" >> "$diff_file"
            file_failed=true
        fi
    fi

    if [[ -f "$expected_mjs" ]]; then
        if [[ ! -f "$actual_mjs" ]]; then
            missing_output_count=$((missing_output_count + 1))
            failed_files="$failed_files$rel_path (missing ESM output)\n"
            printf 'missing output: %s\n' "$actual_mjs" >> "$diff_file"
            file_failed=true
        elif ! parity_compare_js "$expected_mjs" "$actual_mjs" >> "$diff_file" 2>&1; then
            printf '%s\n' "--- ESM: $module_name ---" >> "$diff_file"
            file_failed=true
        fi
    fi

    if $file_failed; then
        diff_count=$((diff_count + 1))
        cp "$actual_cjs" "$CACHE_DIR/rust/${module_name}.cjs" 2>/dev/null || true
        cp "$actual_mjs" "$CACHE_DIR/rust/${module_name}.mjs" 2>/dev/null || true
        failed_files="$failed_files$rel_path (output differs)\n"
        if [[ "$VERBOSE" == "true" ]]; then
            echo -e "${RED}FAIL${RESET} $rel_path"
        fi
        if [[ "$QUICK_MODE" == "true" ]]; then
            echo -e "${RED}Quick mode: stopping on output diff${RESET}"
            head -120 "$diff_file"
            exit 1
        fi
    else
        pass_count=$((pass_count + 1))
        if [[ "$VERBOSE" == "true" ]]; then
            echo -e "${GREEN}PASS${RESET} $rel_path"
        fi
    fi
done < "$TEMP_DIR/files.txt"

tested_count=$((pass_count + diff_count + compile_error_count))
echo ""
echo -e "${BOLD}Summary${RESET}"
if [[ "$tested_count" -gt 0 ]]; then
    pct=$(python3 -c "print(f'{100 * $pass_count / $tested_count:.1f}')")
    echo -e "Passed: ${GREEN}$pass_count${RESET}/$tested_count (${pct}%)"
else
    echo -e "Passed: ${YELLOW}0/0${RESET}"
fi
echo -e "Output differs: ${YELLOW}$diff_count${RESET}"
echo -e "Rust errors:    ${RED}$compile_error_count${RESET}"
echo -e "Missing output: ${RED}$missing_output_count${RESET}"
echo "Skipped:        $skipped_count"
echo "Diffs:          $CACHE_DIR/diffs"
echo "Errors:         $CACHE_DIR/errors"

if [[ -n "$failed_files" ]]; then
    echo ""
    echo -e "${BOLD}Failed files:${RESET}"
    echo -e "$failed_files" | grep -v '^$' | head -20 | while read -r line; do
        echo "  - $line"
    done
fi

if [[ "$diff_count" -gt 0 || "$compile_error_count" -gt 0 || "$missing_output_count" -gt 0 ]]; then
    exit 1
fi
