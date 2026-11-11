#!/bin/bash

# Rust Compiler Output Test Suite
#
# 1. Syntax: the Rust parser against the checked-in snapshots of
#    tests/syntax_tests that print ReScript (printer, conversion, JSX) or
#    syntax errors (parsing/errors, infiniteLoops, recovery).
# 2. JS: the JavaScript the Rust compiler emits for tests/tests/src (and Tella
#    when TELLA_DIR exists) against the checked-in output of the OCaml compiler.
#
# No intermediate representation is compared: only ReScript and JavaScript
# output and diagnostics count (see "The Correctness Contract" in AGENTS.md).

set -e

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)

# Directories
RUST_TARGET="${RUST_TARGET:-debug}"
RUST_BSC="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc"
RUST_PARSER="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/res_parser_rust"
RUST_RESCRIPT="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/rescript"
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
export RESCRIPT_RUNTIME

# Output directories
TEMP_DIR="$PROJECT_ROOT/temp/rust-parity"
DIFF_DIR="$TEMP_DIR/diffs"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
DIM='\033[2m'
RESET='\033[0m'

# Configuration
TIMEOUT_SECONDS=10
SHOW_MAX_FAILURES=10

# Counters for overall summary
total_tests=0
total_passed=0
total_failed=0

# Parse arguments
SKIP_SYNTAX=false
SKIP_JS=false
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --reformat)
            PARITY_COMPARE_MODE=reformat
            shift
            ;;
        --skip-syntax)
            SKIP_SYNTAX=true
            shift
            ;;
        --skip-js)
            SKIP_JS=true
            shift
            ;;
        --release)
            RUST_TARGET=release
            RUST_BSC="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc"
            RUST_PARSER="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/res_parser_rust"
            RUST_RESCRIPT="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/rescript"
            shift
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  --skip-syntax      Skip syntax tests"
            echo "  --skip-js          Skip JS compilation snapshot tests"
            echo "  --reformat         Normalize JS comparisons (default: exact)"
            echo "  --release          Use target/release Rust compiler/parser artifacts"
            echo "  --verbose, -v      Show more detailed output"
            echo "  --help, -h         Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

source "$PROJECT_ROOT/scripts/parity_lib.sh"
parity_init_comparison

# Utility functions
print_header() {
    echo ""
    echo -e "${BOLD}$1${RESET}"
    echo "----------------------------------------------------------------------"
}

print_section_header() {
    echo ""
    echo -e "${BOLD}══════════════════════════════════════════════════════════════════════${RESET}"
    echo -e "${BOLD}$1${RESET}"
    echo -e "${BOLD}══════════════════════════════════════════════════════════════════════${RESET}"
}

# Check prerequisites
check_prerequisites() {
    local missing=false

    "$PROJECT_ROOT/scripts/rust_compiler_shims.sh" "$RUST_TARGET"
    if [[ ! -x "$RUST_BSC" ]]; then
        echo -e "${RED}Error: Rust bsc not found at $RUST_BSC${RESET}"
        if [[ "$RUST_TARGET" == "release" ]]; then
            echo "Run 'cargo build --release --manifest-path rewatch/Cargo.toml' first."
        else
            echo "Run 'cargo build --manifest-path rewatch/Cargo.toml' first."
        fi
        missing=true
    fi

    if [[ ! -x "$RUST_PARSER" ]]; then
        echo -e "${RED}Error: Rust parser not found at $RUST_PARSER${RESET}"
        if [[ "$RUST_TARGET" == "release" ]]; then
            echo "Run 'cargo build --release --manifest-path rewatch/Cargo.toml' first."
        else
            echo "Run 'cargo build --manifest-path rewatch/Cargo.toml' first."
        fi
        missing=true
    fi

    if $missing; then
        exit 2
    fi
}

# Setup temp directory
setup_temp_dir() {
    if [[ -z "$PROJECT_ROOT" || "$PROJECT_ROOT" == "/" || "$TEMP_DIR" != "$PROJECT_ROOT/temp/rust-parity" ]]; then
        echo "Refusing to clean unexpected parity temp directory: $TEMP_DIR" >&2
        exit 2
    fi
    if [[ -L "$TEMP_DIR" || ( -e "$TEMP_DIR" && ! -d "$TEMP_DIR" ) ]]; then
        echo "Refusing to clean unsafe parity temp path: $TEMP_DIR" >&2
        exit 2
    fi
    mkdir -p "$TEMP_DIR"
    find "$TEMP_DIR" -mindepth 1 -type f -delete
    find "$TEMP_DIR" -mindepth 1 -depth -type d -empty -delete
    mkdir -p "$DIFF_DIR"
}

# The nearest directory above file $1 with a rescript.json.
find_rescript_config_root() {
    local current_dir
    current_dir=$(dirname "$1")
    while [[ "$current_dir" != "/" && -n "$current_dir" ]]; do
        if [[ -f "$current_dir/rescript.json" ]]; then
            echo "$current_dir"
            return 0
        fi
        current_dir=$(dirname "$current_dir")
    done
    return 1
}

# =============================================================================
# TEST 1: Syntax Tests
# =============================================================================
run_syntax_tests() {
    if $SKIP_SYNTAX; then
        echo -e "${DIM}Skipping syntax tests${RESET}"
        return
    fi

    print_header "SYNTAX TESTS"

    local pass_count=0
    local fail_count=0
    local failed_files=""

    cd "$PROJECT_ROOT/tests"
    mkdir -p "$TEMP_DIR/syntax"

    # Function to get expected path
    exp() {
        echo "$(dirname $1)/expected/$(basename $1).txt"
    }

    # Collect all syntax test files
    local all_files=""

    # Parsing tests with recovery: the syntax errors (and the recovered tree)
    find syntax_tests/data/parsing/{errors,infiniteLoops,recovery} -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/syntax_parsing_recovery.txt"

    # Printing tests
    find syntax_tests/data/{printer,conversion} -name "*.res" -o -name "*.resi" -o -name "*.ml" -o -name "*.mli" 2>/dev/null | sort > "$TEMP_DIR/syntax_printer.txt"

    # PPX tests
    find syntax_tests/data/ppx/react syntax_tests/data/printer-jsx4 -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/syntax_ppx.txt"

    local file_count=$(cat "$TEMP_DIR"/syntax_*.txt | wc -l | tr -d ' ')
    echo "Testing $file_count files..."

    # Process parsing tests with recovery
    while read -r file; do
        local expected=$(exp "$file")
        local actual="$TEMP_DIR/syntax/$(echo "$file" | tr '/' '_').txt"

        if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" -recover -print ml "$file" > "$actual" 2>&1; then
            if diff -q "$expected" "$actual" > /dev/null 2>&1; then
                pass_count=$((pass_count + 1))
            else
                fail_count=$((fail_count + 1))
                failed_files="$failed_files$file (output differs)\n"
                diff -u "$expected" "$actual" > "$DIFF_DIR/syntax_$(echo "$file" | tr '/' '_').diff" 2>&1 || true
            fi
        else
            fail_count=$((fail_count + 1))
            failed_files="$failed_files$file (parse error/timeout)\n"
        fi
    done < "$TEMP_DIR/syntax_parsing_recovery.txt"

    # Process printing tests
    while read -r file; do
        local expected=$(exp "$file")
        local actual="$TEMP_DIR/syntax/$(echo "$file" | tr '/' '_').txt"

        if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" "$file" > "$actual" 2>&1; then
            if diff -q "$expected" "$actual" > /dev/null 2>&1; then
                pass_count=$((pass_count + 1))
            else
                fail_count=$((fail_count + 1))
                failed_files="$failed_files$file (output differs)\n"
                diff -u "$expected" "$actual" > "$DIFF_DIR/syntax_$(echo "$file" | tr '/' '_').diff" 2>&1 || true
            fi
        else
            fail_count=$((fail_count + 1))
            failed_files="$failed_files$file (parse error/timeout)\n"
        fi
    done < "$TEMP_DIR/syntax_printer.txt"

    # Process PPX tests
    while read -r file; do
        local expected=$(exp "$file")
        local actual="$TEMP_DIR/syntax/$(echo "$file" | tr '/' '_').txt"

        if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" -jsx-version 4 "$file" > "$actual" 2>&1; then
            if diff -q "$expected" "$actual" > /dev/null 2>&1; then
                pass_count=$((pass_count + 1))
            else
                fail_count=$((fail_count + 1))
                failed_files="$failed_files$file (output differs)\n"
                diff -u "$expected" "$actual" > "$DIFF_DIR/syntax_$(echo "$file" | tr '/' '_').diff" 2>&1 || true
            fi
        else
            fail_count=$((fail_count + 1))
            failed_files="$failed_files$file (parse error/timeout)\n"
        fi
    done < "$TEMP_DIR/syntax_ppx.txt"

    cd "$PROJECT_ROOT"

    # Report results
    local total=$((pass_count + fail_count))
    if [[ $total -gt 0 ]]; then
        local pct=$(python3 -c "print(f'{100 * $pass_count / $total:.1f}')")
        echo -e "Passed: ${GREEN}$pass_count${RESET}/$total (${pct}%)"
    else
        echo -e "Passed: ${YELLOW}0/0${RESET} (no files)"
    fi

    if [[ $fail_count -gt 0 ]]; then
        echo -e "Failed: ${RED}$fail_count${RESET}"
    fi

    # Show failed files
    if [[ -n "$failed_files" ]]; then
        echo ""
        echo -e "${BOLD}Failed (first $SHOW_MAX_FAILURES):${RESET}"
        echo -e "$failed_files" | grep -v "^$" | head -$SHOW_MAX_FAILURES | while read -r line; do
            echo "  - $line"
        done
        local total_failures=$(echo -e "$failed_files" | grep -v "^$" | wc -l | tr -d ' ')
        if [[ $total_failures -gt $SHOW_MAX_FAILURES ]]; then
            echo "  ... and $((total_failures - SHOW_MAX_FAILURES)) more"
        fi
    fi

    # Update global counters
    total_tests=$((total_tests + total))
    total_passed=$((total_passed + pass_count))
    total_failed=$((total_failed + fail_count))
}

# =============================================================================
# TEST 2: JS Compilation Snapshots
# =============================================================================
run_js_compilation_tests() {
    if $SKIP_JS; then
        echo -e "${DIM}Skipping JS compilation snapshot tests${RESET}"
        return
    fi

    print_header "JS COMPILATION SNAPSHOTS"

    local pass_count=0
    local compile_error_count=0
    local diff_count=0
    local failed_files=""

    cd "$PROJECT_ROOT/tests/tests"
    mkdir -p "$TEMP_DIR/js"

    # Find all local .res files (some may not have snapshots and are skipped below).
    find src -name "*.res" 2>/dev/null | sort > "$TEMP_DIR/js_files.txt"

    # Include external corpus by reference (no file copying).
    # Expected snapshots there are checked-in .bs.js files next to sources.
    if [[ -d "$TELLA_DIR" ]]; then
        find "$TELLA_DIR" \
            -type d \( -name .git -o -name target -o -name .next -o -name _build -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
            -o -type f -name "*.res" -print 2>/dev/null | \
            sort >> "$TEMP_DIR/js_files.txt"
    fi

    sort -u "$TEMP_DIR/js_files.txt" -o "$TEMP_DIR/js_files.txt"
    grep -Ev '(^|/)lib/(bs|ocaml)(/|$)' "$TEMP_DIR/js_files.txt" > "$TEMP_DIR/js_files.filtered.txt" || true
    mv "$TEMP_DIR/js_files.filtered.txt" "$TEMP_DIR/js_files.txt"
    local file_count=$(wc -l < "$TEMP_DIR/js_files.txt" | tr -d ' ')

    echo "Testing $file_count files..."

    # The Rust side is one in-process `rescript build` per project, which
    # writes its JS over the checked-in snapshots. Save the snapshots first,
    # compare each build output against its saved copy, then restore them.
    local snapshot_dir="$TEMP_DIR/js/snapshots"
    local -a js_projects=()
    while read -r res_file; do
        local abs_res="$res_file"
        [[ "$abs_res" == /* ]] || abs_res="$PROJECT_ROOT/tests/tests/$res_file"
        local snapshot="${abs_res%.res}.mjs"
        [[ -f "$snapshot" ]] || snapshot="${abs_res%.res}.bs.js"
        [[ -f "$snapshot" ]] || continue
        mkdir -p "$snapshot_dir$(dirname "$snapshot")"
        cp "$snapshot" "$snapshot_dir$snapshot"
        # A module the build fails to compile must not pass on its old JS.
        rm "$snapshot"
        local project
        project=$(find_rescript_config_root "$abs_res") || continue
        [[ " ${js_projects[*]} " == *" $project "* ]] || js_projects+=("$project")
    done < "$TEMP_DIR/js_files.txt"
    find "$snapshot_dir" -type f | sed "s|^$snapshot_dir||" > "$TEMP_DIR/js_snapshots.txt"
    restore_js_snapshots() {
        while read -r snapshot; do
            cp "$snapshot_dir$snapshot" "$snapshot"
        done < "$TEMP_DIR/js_snapshots.txt"
    }
    trap restore_js_snapshots EXIT
    local js_build_log="$TEMP_DIR/js/build.log"
    : > "$js_build_log"
    RESCRIPT_RUNTIME="$RESCRIPT_RUNTIME" "$RUST_RESCRIPT" build "$RESCRIPT_RUNTIME" >> "$js_build_log" 2>&1 || true
    for project in "${js_projects[@]}"; do
        echo "Building $project in process..."
        RESCRIPT_RUNTIME="$RESCRIPT_RUNTIME" "$RUST_RESCRIPT" build "$project" >> "$js_build_log" 2>&1 || true
    done

    local file_index=0
    while read -r res_file; do
        file_index=$((file_index + 1))
        local full_res_file="$res_file"
        if [[ "$full_res_file" != /* ]]; then
            full_res_file="$PROJECT_ROOT/tests/tests/$res_file"
        fi

        # Progress indicator
        if [[ $((file_index % 50)) -eq 0 ]] && $VERBOSE; then
            echo "  Progress: $file_index / $file_count files..."
        fi

        # Resolve expected snapshot:
        # - internal tests use .mjs snapshots
        # - external corpora (e.g. tella) use checked-in .bs.js snapshots
        local expected_file="${res_file%.res}.mjs"
        if [[ ! -f "$expected_file" ]]; then
            expected_file="${res_file%.res}.bs.js"
        fi

        # Skip files without an in-source expected snapshot.
        if [[ ! -f "$expected_file" ]]; then
            continue
        fi

        local saved_snapshot="$snapshot_dir$(cd "$(dirname "$expected_file")" && pwd -P)/$(basename "$expected_file")"
        local actual_mjs="$(cd "$(dirname "$expected_file")" && pwd -P)/$(basename "$expected_file")"
        local compile_output="$js_build_log"
        expected_file="$saved_snapshot"
        local compile_ok=false
        if [[ -f "$saved_snapshot" ]]; then
            compile_ok=true
        fi
        if $compile_ok; then
            # Check if output file was created
            if [[ -f "$actual_mjs" ]]; then
                if parity_compare_js "$expected_file" "$actual_mjs" > "$DIFF_DIR/js_$(echo "$res_file" | tr '/' '_').diff" 2>&1; then
                    pass_count=$((pass_count + 1))
                else
                    diff_count=$((diff_count + 1))
                    failed_files="$failed_files$res_file (output differs)\n"
                fi
            else
                compile_error_count=$((compile_error_count + 1))
                failed_files="$failed_files$res_file (no output file)\n"
                cp "$compile_output" "$DIFF_DIR/js_$(echo "$res_file" | tr '/' '_').err" 2>/dev/null || true
            fi
        else
            compile_error_count=$((compile_error_count + 1))
            failed_files="$failed_files$res_file (compile error)\n"
            cp "$compile_output" "$DIFF_DIR/js_$(echo "$res_file" | tr '/' '_').err" 2>/dev/null || true
        fi

    done < "$TEMP_DIR/js_files.txt"

    restore_js_snapshots
    trap - EXIT
    cd "$PROJECT_ROOT"

    # Report results
    local total=$((pass_count + compile_error_count + diff_count))
    if [[ $total -gt 0 ]]; then
        local pct=$(python3 -c "print(f'{100 * $pass_count / $total:.1f}')")
        echo -e "Passed: ${GREEN}$pass_count${RESET}/$total (${pct}%)"
    else
        echo -e "Passed: ${YELLOW}0/0${RESET} (no files with snapshots)"
    fi

    if [[ $compile_error_count -gt 0 ]]; then
        echo -e "Compile errors: ${RED}$compile_error_count${RESET}"
    fi

    if [[ $diff_count -gt 0 ]]; then
        echo -e "Output differs: ${YELLOW}$diff_count${RESET}"
    fi

    # Show failed files
    if [[ -n "$failed_files" ]]; then
        echo ""
        echo -e "${BOLD}Failed (first $SHOW_MAX_FAILURES):${RESET}"
        echo -e "$failed_files" | grep -v "^$" | head -$SHOW_MAX_FAILURES | while read -r line; do
            echo "  - $line"
        done
        local total_failures=$(echo -e "$failed_files" | grep -v "^$" | wc -l | tr -d ' ')
        if [[ $total_failures -gt $SHOW_MAX_FAILURES ]]; then
            echo "  ... and $((total_failures - SHOW_MAX_FAILURES)) more"
        fi
    fi

    # Update global counters
    total_tests=$((total_tests + total))
    total_passed=$((total_passed + pass_count))
    total_failed=$((total_failed + compile_error_count + diff_count))
}

# =============================================================================
# Main
# =============================================================================

print_section_header "RUST COMPILER PARITY REPORT"
echo ""
echo "Rust bsc:     $RUST_BSC"
echo "Rust parser:  $RUST_PARSER"
echo "Rust target:  $RUST_TARGET"
echo "Timeout:      ${TIMEOUT_SECONDS}s per file"
echo ""

check_prerequisites
setup_temp_dir

run_syntax_tests
run_js_compilation_tests

# Final summary
print_section_header "OVERALL SUMMARY"
echo ""

if [[ $total_tests -gt 0 ]]; then
    pct=$(python3 -c "print(f'{100 * $total_passed / $total_tests:.1f}')")
    echo -e "${BOLD}Total:${RESET} $total_passed / $total_tests tests passed (${pct}% parity)"
else
    echo -e "${YELLOW}No tests were run${RESET}"
fi

echo ""
echo "Diff files saved to: $DIFF_DIR"
echo ""

# Exit code
if [[ $total_failed -eq 0 && $total_passed -gt 0 ]]; then
    echo -e "${GREEN}${BOLD}SUCCESS: 100% parity achieved!${RESET}"
    exit 0
elif [[ $total_passed -eq 0 ]]; then
    echo -e "${RED}${BOLD}ERROR: No tests passed${RESET}"
    exit 2
else
    echo -e "${YELLOW}${BOLD}INCOMPLETE: $total_failed tests failed${RESET}"
    exit 1
fi
