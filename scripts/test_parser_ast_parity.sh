#!/bin/bash

# AST Parity Test Suite: Comprehensive comparison of Rust and OCaml compilers
#
# Tests performed:
#
# Parser parity (using res_parser for readable diffs):
# 1. sexp-locs parity - AST structure + locations + attributes match
#
# Compiler binary output parity (using bsc -bs-ast):
# 2. bsc-ast parity - Full compiler binary AST output is byte-identical
#    (includes dependency extraction + marshalled parsetree)
#
# REGRESSION TRACKING:
# The script maintains baseline files in tests/parity_baselines/ for each test type.
# - When a file passes, it's added to the baseline (append-only)
# - If a file in the baseline fails, it's flagged as a REGRESSION
# - Regressions cause the test to fail, preventing parity from decreasing
#
# NOTE: Printer parity (res/ml output) is tested by test_syntax.sh
# NOTE: Parsetree0/PPX parity is tested by test_parser_ast0_parity.sh
#
# Uses test files from tests/syntax_tests/data/{idempotency,printer,ppx,conversion,ast-mapping}
#
# USAGE:
#   ./scripts/test_parser_ast_parity.sh [OPTIONS] [FILE|PATTERN]
#
# OPTIONS:
#   -q, --quick       Stop on first failure (useful for quick iteration)
#   -j, --parallel N  Run N tests in parallel (default: 16)
#   -v, --verbose     Show progress for each file
#   -h, --help        Show this help message
#   --info            Show detailed usage information and examples
#
# EXAMPLES:
#   # Test a single file (fastest for iteration):
#   ./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/apply.res
#
#   # Test files matching a pattern:
#   ./scripts/test_parser_ast_parity.sh "printer/expr/*.res"
#
#   # Run all tests, stop on first failure:
#   ./scripts/test_parser_ast_parity.sh --quick
#
#   # Run all tests in parallel (default 16 jobs):
#   ./scripts/test_parser_ast_parity.sh
#
#   # Quick iteration on a specific test:
#   ./scripts/test_parser_ast_parity.sh -v tests/syntax_tests/data/printer/expr/apply.res

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=16
VERBOSE=false
FILE_ARG=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -q|--quick)
            QUICK_MODE=true
            PARALLEL_JOBS=1  # Quick mode forces sequential for clean output
            shift
            ;;
        -j|--parallel)
            PARALLEL_JOBS="$2"
            shift 2
            ;;
        -j*)
            PARALLEL_JOBS="${1#-j}"
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            head -45 "$0" | tail -40
            exit 0
            ;;
        --info)
            cat << 'EOF'
AST Parity Test Suite
=====================

This is the comprehensive test for verifying Rust compiler parity with OCaml.

WHAT IT TESTS:

  1. sexp-locs     Parser AST with locations (readable diffs for debugging)
  2. bsc-ast       Full `bsc -bs-ast` output (production format with deps)

For Parsetree0/PPX parity tests, see test_parser_ast0_parity.sh

QUICK START:

  # Run all tests (parallel by default):
  ./scripts/test_parser_ast_parity.sh

  # Test a single file (fastest for iteration):
  ./scripts/test_parser_ast_parity.sh tests/syntax_tests/data/printer/expr/apply.res

  # Test files matching a pattern:
  ./scripts/test_parser_ast_parity.sh "record"

  # Stop on first failure (useful when fixing issues):
  ./scripts/test_parser_ast_parity.sh --quick

  # Verbose output showing each file:
  ./scripts/test_parser_ast_parity.sh -v

REGRESSION TRACKING:

  The script maintains baseline files in tests/parity_baselines/. When a file
  passes, it's added to the baseline. If a file that was passing starts failing,
  it's flagged as a REGRESSION and the test fails.

  This ensures parity can only increase, never decrease.

UNDERSTANDING FAILURES:

  - sexp-locs diff: Look at the diff to see AST structure differences
  - bsc-ast diff: Full compiler output differs (includes dependency extraction)

OUTPUT FORMATS:

  bsc -bs-ast output format (used by build system):
    [4 bytes]     Size of dependencies section (binary int)
    [N bytes]     Dependencies (newline-separated module names, e.g. "React\nBelt\n")
    [string]      Source filename + newline
    [marshalled]  OCaml-marshalled parsetree

  res_parser -print binary output format:
    [magic]       AST magic number (ast_impl_magic or ast_intf_magic)
    [marshalled]  Filename (OCaml string)
    [marshalled]  Parsetree

DIFF FILES:

  When tests fail, diff files are saved to a temp directory (shown in output).
  Use these to debug what's different between Rust and OCaml output.

EOF
            exit 0
            ;;
        *)
            FILE_ARG="$1"
            shift
            ;;
    esac
done

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)
DUNE_BIN_DIR="$PROJECT_ROOT/_build/install/default/bin"

# Parser executables (for sexp output - readable diffs)
RUST_PARSER="$PROJECT_ROOT/compiler-rust/target/release/res_parser_rust"
OCAML_PARSER="$DUNE_BIN_DIR/res_parser"

# Compiler executables (for bsc -bs-ast output - production format)
RUST_BSC="$PROJECT_ROOT/compiler-rust/target/release/bsc"
OCAML_BSC="$PROJECT_ROOT/packages/@rescript/$($PROJECT_ROOT/scripts/platform.sh)/bin/bsc.exe"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

# Configuration
TIMEOUT_SECONDS=5

# Baseline files for regression tracking (one per test type)
BASELINE_DIR="$PROJECT_ROOT/tests/parity_baselines"
BASELINE_SEXP_LOCS="$BASELINE_DIR/sexp_locs.txt"
BASELINE_BSC_AST="$BASELINE_DIR/bsc_ast.txt"

# Check if executables exist
if [[ ! -x "$OCAML_PARSER" ]]; then
    echo -e "${RED}Error: OCaml parser not found at $OCAML_PARSER${RESET}"
    echo "Run 'make' first to build the OCaml parser."
    exit 1
fi

if [[ ! -x "$RUST_PARSER" ]]; then
    echo -e "${RED}Error: Rust parser not found at $RUST_PARSER${RESET}"
    echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml --release' first."
    exit 1
fi

if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    echo "Run 'make' first to build the OCaml compiler."
    exit 1
fi

if [[ ! -x "$RUST_BSC" ]]; then
    echo -e "${RED}Error: Rust bsc not found at $RUST_BSC${RESET}"
    echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml --release' first."
    exit 1
fi

# Create temp directory
TEMP_DIR=$(mktemp -d)
trap "rm -rf $TEMP_DIR" EXIT

echo -e "${BOLD}AST Parity Test${RESET}"
echo "============================================"
echo "OCaml parser: $OCAML_PARSER"
echo "Rust parser:  $RUST_PARSER"
echo "OCaml bsc:    $OCAML_BSC"
echo "Rust bsc:     $RUST_BSC"
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

# Find test files based on arguments
cd "$PROJECT_ROOT/tests"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        # Convert absolute/relative path to path relative to tests/ directory
        abs_path=$(cd "$(dirname "$FILE_ARG")" && pwd)/$(basename "$FILE_ARG")
        rel_path="${abs_path#$PROJECT_ROOT/tests/}"
        echo "$rel_path" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        # Convert project-relative path to tests-relative path
        rel_path="${FILE_ARG#tests/}"
        echo "$rel_path" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/tests/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        # Treat as a pattern and use find with -path
        find syntax_tests/data/idempotency syntax_tests/data/printer syntax_tests/data/ppx syntax_tests/data/conversion syntax_tests/data/ast-mapping \( -name "*.res" -o -name "*.resi" \) 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
            echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
            echo "Hint: Try a pattern like 'printer/expr/apply' or a full path"
            exit 1
        fi
    fi
else
    # Find all test files
    find syntax_tests/data/idempotency syntax_tests/data/printer syntax_tests/data/ppx syntax_tests/data/conversion syntax_tests/data/ast-mapping \( -name "*.res" -o -name "*.resi" \) 2>/dev/null | sort > "$TEMP_DIR/files.txt"
fi

TOTAL_FILES=$(wc -l < "$TEMP_DIR/files.txt" | tr -d ' ')

if [[ "$TOTAL_FILES" -eq 1 ]]; then
    echo -e "Testing ${BOLD}1${RESET} file: $(cat "$TEMP_DIR/files.txt")"
else
    echo -e "Found ${BOLD}$TOTAL_FILES${RESET} test files"
fi
echo ""

# Create results directory
RESULTS_DIR="$TEMP_DIR/results"
mkdir -p "$RESULTS_DIR"
mkdir -p "$TEMP_DIR/locs_diffs"
mkdir -p "$TEMP_DIR/bsc_ast_parity_diffs"

# Export variables for parallel execution
export OCAML_PARSER RUST_PARSER OCAML_BSC RUST_BSC TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE

# Function to test a single file - writes results to a file
test_single_file() {
    local file="$1"
    local safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    # Initialize result
    local locs_pass=0 locs_diff=0
    local bsc_ast_diff=0
    local ocaml_fail=0 rust_fail=0

    # Determine if it's an interface file
    local intf_flag=""
    case "$file" in
        *.resi)
            intf_flag="-interface"
            ;;
    esac

    # Create per-file temp directory for parallel safety
    local file_temp="$TEMP_DIR/work/$safe_name"
    mkdir -p "$file_temp"

    # Run OCaml parser with sexp-locs (primary test - includes all attributes)
    local ocaml_success=false
    if timeout "$TIMEOUT_SECONDS" "$OCAML_PARSER" $intf_flag -print sexp-locs "$file" > "$file_temp/ocaml.sexp-locs" 2>/dev/null; then
        ocaml_success=true
    else
        ocaml_fail=1
    fi

    # Run Rust parser with sexp-locs
    local rust_success=false
    if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" $intf_flag -print sexp-locs "$file" > "$file_temp/rust.sexp-locs" 2>/dev/null; then
        rust_success=true
    else
        rust_fail=1
    fi

    # Compare sexp-locs outputs if both succeeded
    if $ocaml_success && $rust_success; then
        if diff -q "$file_temp/ocaml.sexp-locs" "$file_temp/rust.sexp-locs" > /dev/null 2>&1; then
            locs_pass=1
        else
            locs_diff=1
            diff -u "$file_temp/ocaml.sexp-locs" "$file_temp/rust.sexp-locs" > "$TEMP_DIR/locs_diffs/$safe_name.diff" 2>&1 || true
        fi

        # Test bsc -bs-ast parity (full compiler binary AST output with dependencies)
        # This is the production format used by the build system
        # Note: Both OCaml and Rust bsc create .iast files for interface (.resi) files,
        # ignoring the -o extension. We check for both possible output locations.
        local ocaml_ast_file="$file_temp/ocaml.ast"
        local rust_ast_file="$file_temp/rust.ast"
        local ocaml_iast_file="$file_temp/ocaml.iast"
        local rust_iast_file="$file_temp/rust.iast"
        if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -bs-ast "$file" -o "$ocaml_ast_file" 2>/dev/null && \
           timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-ast "$file" -o "$rust_ast_file" 2>/dev/null; then
            # Both compilers create .iast for .resi files (regardless of -o), so check for that
            if [[ -f "$ocaml_iast_file" && ! -f "$ocaml_ast_file" ]]; then
                ocaml_ast_file="$ocaml_iast_file"
            fi
            if [[ -f "$rust_iast_file" && ! -f "$rust_ast_file" ]]; then
                rust_ast_file="$rust_iast_file"
            fi
            if [[ -f "$ocaml_ast_file" && -f "$rust_ast_file" ]]; then
                if ! diff -q "$ocaml_ast_file" "$rust_ast_file" > /dev/null 2>&1; then
                    bsc_ast_diff=1
                    {
                        echo "OCaml bsc-ast size: $(wc -c < "$ocaml_ast_file") bytes"
                        echo "Rust bsc-ast size:  $(wc -c < "$rust_ast_file") bytes"
                        echo ""
                        echo "First differing bytes (hex dump):"
                        diff <(xxd "$ocaml_ast_file" | head -50) <(xxd "$rust_ast_file" | head -50) || true
                    } > "$TEMP_DIR/bsc_ast_parity_diffs/$safe_name.diff" 2>&1
                fi
            fi
        fi
    fi

    # Write results
    echo "$file:$locs_pass:$locs_diff:$bsc_ast_diff:$ocaml_fail:$rust_fail" > "$result_file"

    # Clean up per-file temp
    rm -rf "$file_temp"
}

export -f test_single_file
export RESULTS_DIR

echo -e "${BOLD}Running AST parity tests...${RESET}"
if $QUICK_MODE; then
    echo -e "  (quick mode: will stop on first failure)"
fi
if [[ $PARALLEL_JOBS -gt 1 ]]; then
    echo -e "  (running $PARALLEL_JOBS parallel jobs)"
fi
echo ""

# Create work directory
mkdir -p "$TEMP_DIR/work"

# Run tests
if $QUICK_MODE; then
    # Sequential mode with early exit
    while read -r file; do
        if $VERBOSE; then
            echo "  Testing: $file"
        fi

        test_single_file "$file"

        # Check result
        safe_name=$(echo "$file" | tr '/' '_')
        result=$(cat "$RESULTS_DIR/$safe_name.result")
        IFS=':' read -r _ locs_pass locs_diff bsc_ast_diff ocaml_fail rust_fail <<< "$result"

        if [[ "$locs_diff" -eq 1 ]]; then
            echo -e "${RED}FAIL:${RESET} $file (sexp-locs differs)"
            echo ""
            echo "Diff:"
            head -30 "$TEMP_DIR/locs_diffs/$safe_name.diff"
            echo ""
            echo -e "${YELLOW}Quick mode: stopping on first failure${RESET}"
            break
        fi
    done < "$TEMP_DIR/files.txt"
else
    # Parallel mode
    if $VERBOSE; then
        cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'echo "  Testing: {}"; test_single_file "$@"' _ {}
    else
        # Show progress every 100 files
        total=$TOTAL_FILES
        cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {} &
        pid=$!

        while kill -0 $pid 2>/dev/null; do
            completed=$(ls -1 "$RESULTS_DIR" 2>/dev/null | wc -l | tr -d ' ')
            if [[ $completed -gt 0 ]]; then
                printf "\r  Progress: %d / %d files..." "$completed" "$total"
            fi
            sleep 0.5
        done
        wait $pid
        printf "\r  Progress: %d / %d files... done\n" "$total" "$total"
    fi
fi

# Aggregate results
locs_pass_count=0
locs_diff_count=0
bsc_ast_parity_diff_count=0
ocaml_fail_count=0
rust_fail_count=0

locs_diff_files=""
bsc_ast_parity_diff_files=""
ocaml_fail_files=""
rust_fail_files=""

for result_file in "$RESULTS_DIR"/*.result; do
    [[ -f "$result_file" ]] || continue
    result=$(cat "$result_file")
    IFS=':' read -r file locs_pass locs_diff bsc_ast_diff ocaml_fail rust_fail <<< "$result"

    locs_pass_count=$((locs_pass_count + locs_pass))
    locs_diff_count=$((locs_diff_count + locs_diff))
    bsc_ast_parity_diff_count=$((bsc_ast_parity_diff_count + bsc_ast_diff))
    ocaml_fail_count=$((ocaml_fail_count + ocaml_fail))
    rust_fail_count=$((rust_fail_count + rust_fail))

    [[ "$locs_diff" -eq 1 ]] && locs_diff_files="$locs_diff_files$file\n"
    [[ "$bsc_ast_diff" -eq 1 ]] && bsc_ast_parity_diff_files="$bsc_ast_parity_diff_files$file\n"
    [[ "$ocaml_fail" -eq 1 ]] && ocaml_fail_files="$ocaml_fail_files$file\n"
    [[ "$rust_fail" -eq 1 ]] && rust_fail_files="$rust_fail_files$file\n"
done

# Build lists of tested and passing files for each test type
all_tested_files=""
sexp_locs_pass_files=""
bsc_ast_pass_files=""

for result_file in "$RESULTS_DIR"/*.result; do
    [[ -f "$result_file" ]] || continue
    result=$(cat "$result_file")
    IFS=':' read -r file locs_pass locs_diff bsc_ast_diff ocaml_fail rust_fail <<< "$result"

    # Track all tested files
    all_tested_files="$all_tested_files$file\n"

    # A file passes if it didn't fail and didn't have a diff
    if [[ "$locs_pass" -eq 1 && "$locs_diff" -eq 0 ]]; then
        sexp_locs_pass_files="$sexp_locs_pass_files$file\n"
    fi
    if [[ "$locs_pass" -eq 1 && "$bsc_ast_diff" -eq 0 ]]; then
        bsc_ast_pass_files="$bsc_ast_pass_files$file\n"
    fi
done

# Get sorted list of all tested files (filtered to test suite only)
tested_files_sorted=$(echo -e "$all_tested_files" | grep -v "^$" | grep "^syntax_tests/data/" | sort -u)

# Function to detect regressions and update baseline
# Args: $1=baseline_file, $2=current_pass_files (newline-separated), $3=test_name, $4=tested_files (sorted)
detect_regressions_and_update() {
    local baseline_file="$1"
    local current_pass="$2"
    local test_name="$3"
    local tested_files="$4"
    local regressions=""
    local new_passes=""

    # Create baseline dir if needed
    mkdir -p "$(dirname "$baseline_file")"

    # Get current passing files as sorted list
    # Only include files from the test suite (syntax_tests/data/), not arbitrary paths like /tmp/
    local current_sorted=$(echo -e "$current_pass" | grep -v "^$" | grep "^syntax_tests/data/" | sort -u)

    if [[ -f "$baseline_file" ]]; then
        local baseline_sorted=$(sort -u "$baseline_file")

        # Find regressions: files that are in baseline AND were tested AND did not pass
        # First: files in baseline that were tested
        local baseline_and_tested=$(comm -12 <(echo "$baseline_sorted") <(echo "$tested_files") || true)
        # Then: of those, which ones did NOT pass
        if [[ -n "$baseline_and_tested" ]]; then
            regressions=$(comm -23 <(echo "$baseline_and_tested") <(echo "$current_sorted") | grep -v "^$" || true)
        fi

        # Find new passes: files in current but not in baseline
        new_passes=$(comm -13 <(echo "$baseline_sorted") <(echo "$current_sorted") | grep -v "^$" || true)
    else
        # No baseline yet - all current passes are new
        new_passes="$current_sorted"
    fi

    # Report regressions
    if [[ -n "$regressions" ]]; then
        local reg_count=$(echo "$regressions" | wc -l | tr -d ' ')
        echo -e "${RED}${BOLD}REGRESSION in $test_name: $reg_count file(s) that previously passed now fail:${RESET}"
        echo "$regressions" | head -20 | while read -r file; do
            [[ -n "$file" ]] && echo "  $file"
        done
        if [[ $reg_count -gt 20 ]]; then
            echo "  ... and $((reg_count - 20)) more"
        fi
        echo ""
        # Store regressions in temp for summary
        echo "$regressions" > "$TEMP_DIR/regressions_${test_name// /_}.txt"
    fi

    # Append new passes to baseline (only append, never remove)
    if [[ -n "$new_passes" ]]; then
        local new_count=$(echo "$new_passes" | wc -l | tr -d ' ')
        echo -e "${GREEN}New passes in $test_name: $new_count file(s)${RESET}"
        echo "$new_passes" >> "$baseline_file"
        # Re-sort and dedupe the baseline file
        sort -u "$baseline_file" -o "$baseline_file"
    fi
}

echo ""
echo -e "${BOLD}Checking for regressions against baseline...${RESET}"
echo ""

# Detect regressions for each test type
detect_regressions_and_update "$BASELINE_SEXP_LOCS" "$sexp_locs_pass_files" "sexp-locs" "$tested_files_sorted"
detect_regressions_and_update "$BASELINE_BSC_AST" "$bsc_ast_pass_files" "bsc-ast" "$tested_files_sorted"

# Count total regressions
total_regressions=0
for reg_file in "$TEMP_DIR"/regressions_*.txt; do
    [[ -f "$reg_file" ]] && total_regressions=$((total_regressions + $(wc -l < "$reg_file" | tr -d ' ')))
done

echo ""
echo ""
echo -e "${BOLD}============================================${RESET}"
echo -e "${BOLD}RESULTS${RESET}"
echo -e "${BOLD}============================================${RESET}"
echo ""

# Show baseline statistics
baseline_sexp_locs_count=0
baseline_bsc_ast_count=0

[[ -f "$BASELINE_SEXP_LOCS" ]] && baseline_sexp_locs_count=$(wc -l < "$BASELINE_SEXP_LOCS" | tr -d ' ')
[[ -f "$BASELINE_BSC_AST" ]] && baseline_bsc_ast_count=$(wc -l < "$BASELINE_BSC_AST" | tr -d ' ')

echo -e "${BOLD}Summary:${RESET}"
echo "  Total files tested:         $TOTAL_FILES"
echo ""
echo "  ${BOLD}Baseline (files that must not regress):${RESET}"
echo "    sexp-locs:                $baseline_sexp_locs_count"
echo "    bsc-ast:                  $baseline_bsc_ast_count"
echo ""
echo "  ${BOLD}Parser parity (sexp output for debugging):${RESET}"
echo "    sexp-locs matches:        $locs_pass_count"
echo "    sexp-locs differences:    $locs_diff_count"
echo ""
echo "  ${BOLD}Compiler parity (bsc -bs-ast output):${RESET}"
echo "    bsc-ast differences:      $bsc_ast_parity_diff_count"
echo ""
echo "  ${BOLD}Parse failures:${RESET}"
echo "    OCaml failures:           $ocaml_fail_count"
echo "    Rust failures:            $rust_fail_count"
echo ""

# Show sexp-locs mismatches
if [[ $locs_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${YELLOW}Files with location differences ($locs_diff_count):${RESET}"
    echo -e "$locs_diff_files" | grep -v "^$" | head -30 | while read file; do
        echo "  $file"
    done
    if [[ $locs_diff_count -gt 30 ]]; then
        remaining=$((locs_diff_count - 30))
        echo "  ... and $remaining more"
    fi
    echo ""

    # Show first locs diff as example
    echo -e "${BOLD}Example location diff (first file):${RESET}"
    first_locs_diff=$(ls "$TEMP_DIR/locs_diffs/"*.diff 2>/dev/null | head -1)
    if [[ -n "$first_locs_diff" ]]; then
        head -50 "$first_locs_diff"
        lines=$(wc -l < "$first_locs_diff")
        if [[ $lines -gt 50 ]]; then
            echo "  ... (diff truncated, $lines total lines)"
        fi
    fi
    echo ""
fi

# Show bsc-ast parity differences (full compiler output)
if [[ $bsc_ast_parity_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${RED}Files with bsc-ast parity differences ($bsc_ast_parity_diff_count):${RESET}"
    echo "  (bsc -bs-ast output differs - includes deps + marshalled parsetree)"
    echo -e "$bsc_ast_parity_diff_files" | grep -v "^$" | head -15 | while read file; do
        echo "  $file"
    done
    if [[ $bsc_ast_parity_diff_count -gt 15 ]]; then
        remaining=$((bsc_ast_parity_diff_count - 15))
        echo "  ... and $remaining more"
    fi
    echo ""

    # Show first bsc-ast diff as example
    echo -e "${BOLD}Example bsc-ast diff (first file):${RESET}"
    first_bsc_diff=$(ls "$TEMP_DIR/bsc_ast_parity_diffs/"*.diff 2>/dev/null | head -1)
    if [[ -n "$first_bsc_diff" ]]; then
        head -30 "$first_bsc_diff"
    fi
    echo ""
fi

# Show Rust failures (if not too many)
if [[ $rust_fail_count -gt 0 && $rust_fail_count -le 50 ]]; then
    echo -e "${BOLD}${YELLOW}Files where Rust parser failed ($rust_fail_count):${RESET}"
    echo -e "$rust_fail_files" | grep -v "^$" | head -20 | while read file; do
        echo "  $file"
    done
    if [[ $rust_fail_count -gt 20 ]]; then
        remaining=$((rust_fail_count - 20))
        echo "  ... and $remaining more"
    fi
    echo ""
elif [[ $rust_fail_count -gt 50 ]]; then
    echo -e "${BOLD}${YELLOW}Rust parser failed on $rust_fail_count files (too many to list)${RESET}"
    echo ""
fi

# Show OCaml failures (if any)
if [[ $ocaml_fail_count -gt 0 ]]; then
    echo -e "${BOLD}${YELLOW}Files where OCaml parser failed ($ocaml_fail_count):${RESET}"
    echo -e "$ocaml_fail_files" | grep -v "^$" | head -10 | while read file; do
        echo "  $file"
    done
    if [[ $ocaml_fail_count -gt 10 ]]; then
        remaining=$((ocaml_fail_count - 10))
        echo "  ... and $remaining more"
    fi
    echo ""
fi

echo -e "${BOLD}============================================${RESET}"

# Determine exit status
all_pass=true
exit_code=0

# Check for regressions first - these are the most important failures
if [[ $total_regressions -gt 0 ]]; then
    echo -e "${RED}${BOLD}REGRESSION DETECTED: $total_regressions file(s) that previously passed now fail!${RESET}"
    echo "  Review the regression lists above and fix before proceeding."
    all_pass=false
    exit_code=1
fi

if [[ $locs_diff_count -gt 0 ]]; then
    pct_match=$(python3 -c "print(f'{100 * $locs_pass_count / ($locs_pass_count + $locs_diff_count):.1f}')")
    echo -e "${RED}${BOLD}FAILED: $locs_diff_count files have sexp-locs differences ($pct_match% match)${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $bsc_ast_parity_diff_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: $bsc_ast_parity_diff_count files have bsc-ast differences${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $locs_pass_count -eq 0 ]]; then
    echo -e "${RED}${BOLD}ERROR: No files could be compared${RESET}"
    exit 1
fi

if $all_pass; then
    echo -e "${GREEN}${BOLD}SUCCESS: All $locs_pass_count files have full parity!${RESET}"
fi

exit $exit_code
