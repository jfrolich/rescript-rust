#!/bin/bash

# Typed Tree Parity Test Suite: Compare typed tree output between OCaml and Rust compilers
#
# Tests performed:
# 1. typed-sexp parity - Typed tree structure matches between OCaml and Rust (without locations)
#
# Uses rewatch to build dependencies first, then compares typed tree output file by file.
#
# USAGE:
#   ./scripts/test_typedtree_parity.sh [OPTIONS] [FILE|PATTERN]
#
# OPTIONS:
#   -q, --quick       Stop on first failure (useful for quick iteration)
#   -j, --parallel N  Run N tests in parallel (default: 16)
#   -v, --verbose     Show progress for each file
#   --no-build        Skip the initial rewatch build (assume already built)
#   --tella           Test against tella-fusion project (default: ~/dev/tella-fusion)
#   -h, --help        Show this help message
#
# EXAMPLES:
#   # Test a single file (fastest for iteration):
#   ./scripts/test_typedtree_parity.sh tests/tests/src/a.res
#
#   # Test files matching a pattern:
#   ./scripts/test_typedtree_parity.sh "Core_Array"
#
#   # Run all tests, stop on first failure:
#   ./scripts/test_typedtree_parity.sh --quick
#
#   # Run all tests in parallel (default 16 jobs):
#   ./scripts/test_typedtree_parity.sh
#
#   # Test tella-fusion project:
#   ./scripts/test_typedtree_parity.sh --tella

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=16
VERBOSE=false
FILE_ARG=""
SKIP_BUILD=false
TELLA_MODE=false
TELLA_JSX_MODE=false

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
        --no-build)
            SKIP_BUILD=true
            shift
            ;;
        --tella)
            TELLA_MODE=true
            shift
            ;;
        --tella-jsx)
            TELLA_MODE=true
            TELLA_JSX_MODE=true
            shift
            ;;
        -h|--help)
            head -38 "$0" | tail -33
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
OCAML_BSC="$DUNE_BIN_DIR/bsc"
RUST_BSC="$PROJECT_ROOT/compiler-rust/target/release/bsc"
# Prefer freshly built rewatch binary (has --bsc support) over installed rescript.exe
REWATCH_BUILT="$PROJECT_ROOT/rewatch/target/release/rescript"
if [[ -x "$REWATCH_BUILT" ]]; then
    RESCRIPT_CLI="$REWATCH_BUILT"
else
    RESCRIPT_CLI="$PROJECT_ROOT/packages/@rescript/darwin-arm64/bin/rescript.exe"
fi
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
BUILD_DIR="$TEST_PROJECT"

# Tella mode configuration
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
if [[ "$TELLA_MODE" == "true" ]]; then
    if [[ ! -d "$TELLA_DIR" ]]; then
        echo -e "Error: tella-fusion not found at $TELLA_DIR"
        echo "Set TELLA_DIR environment variable to the tella-fusion directory."
        exit 1
    fi
    BUILD_DIR="$TELLA_DIR"
    TEST_PROJECT="$TELLA_DIR/packages/core/webapp"
    if [[ ! -f "$TEST_PROJECT/rescript.json" ]]; then
        echo -e "Error: rescript.json not found at $TEST_PROJECT"
        exit 1
    fi
fi

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

# Configuration
if [[ "$TELLA_MODE" == "true" ]]; then
    TIMEOUT_SECONDS=30
else
    TIMEOUT_SECONDS=10
fi

# Check if compilers exist
if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    echo "Run 'make' first to build the OCaml compiler."
    exit 1
fi

if [[ ! -x "$RUST_BSC" ]]; then
    echo -e "${YELLOW}Warning: Rust bsc not found at $RUST_BSC${RESET}"
    echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml --release' to build the Rust compiler."
    echo "For now, testing OCaml compiler only."
    RUST_AVAILABLE=false
else
    RUST_AVAILABLE=true
fi

if [[ ! -x "$RESCRIPT_CLI" ]]; then
    echo -e "${RED}Error: rescript CLI not found at $RESCRIPT_CLI${RESET}"
    echo "Run 'make' first to build the toolchain."
    exit 1
fi

# Create temp directory
TEMP_DIR=$(mktemp -d)
CACHE_DIR=".parity-cache"
mkdir -p "$CACHE_DIR/tests/diffs" "$CACHE_DIR/tests/ocaml" "$CACHE_DIR/tests/rust"
trap "cp -r $TEMP_DIR/diffs/* $CACHE_DIR/tests/diffs/ 2>/dev/null; rm -rf $TEMP_DIR" EXIT

if [[ "$TELLA_JSX_MODE" == "true" ]]; then
    echo -e "${BOLD}Typed Tree Parity Test (tella-fusion, JSX-heavy files only)${RESET}"
elif [[ "$TELLA_MODE" == "true" ]]; then
    echo -e "${BOLD}Typed Tree Parity Test (tella-fusion, excluding JSX-heavy files)${RESET}"
else
    echo -e "${BOLD}Typed Tree Parity Test${RESET}"
fi
echo "============================================"
echo "OCaml bsc: $OCAML_BSC"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo "Rust bsc:  $RUST_BSC"
else
    echo "Rust bsc:  (not available)"
fi
if [[ "$TELLA_MODE" == "true" ]]; then
    echo "Tella dir: $TELLA_DIR"
fi
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

# Tella cache paths (set regardless of --no-build)
if [[ "$TELLA_MODE" == "true" ]]; then
    PARITY_CACHE="$TELLA_DIR/.parity-cache"
    OCAML_SEXP_CACHE="$PARITY_CACHE/ocaml-sexp"
fi

# Step 1: Build with rewatch to ensure all dependencies are compiled
if [[ "$SKIP_BUILD" != "true" ]]; then
    echo -e "${BOLD}Step 1: Building project with rewatch...${RESET}"
    cd "$BUILD_DIR"
    if [[ "$TELLA_MODE" == "true" ]]; then
        OCAML_SEXP_COUNT=$(find "$OCAML_SEXP_CACHE" -name "*.sexp" 2>/dev/null | wc -l | tr -d ' ')

        # Step 1a: Generate OCaml sexp (skip if cached)
        if [[ "$OCAML_SEXP_COUNT" -gt 0 ]]; then
            echo "Using $OCAML_SEXP_COUNT cached OCaml sexp files from $OCAML_SEXP_CACHE"
        else
            echo "Generating OCaml sexp (first run, may take ~10min)..."
            if ! RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build --dump-typed-sexp "$TELLA_DIR" 2>&1 | tail -5; then
                echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
            fi
            # Copy .sexp files to cache (before Rust build cleans lib/)
            mkdir -p "$OCAML_SEXP_CACHE"
            find "$TEST_PROJECT/lib/ocaml" -name "*.sexp" -exec cp {} "$OCAML_SEXP_CACHE/" \;
            OCAML_SEXP_COUNT=$(find "$OCAML_SEXP_CACHE" -name "*.sexp" 2>/dev/null | wc -l | tr -d ' ')
            echo "Cached $OCAML_SEXP_COUNT OCaml sexp files to $OCAML_SEXP_CACHE"
        fi

        # Step 1b: Generate Rust sexp (subprocess mode with timeout)
        echo "Generating Rust sexp with subprocess mode..."
        if ! RESCRIPT_BSC_EXE="$RUST_BSC" "$RESCRIPT_CLI" build --subprocess --dump-typed-sexp "$TELLA_DIR" 2>&1 | tail -5; then
            echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
        fi
    else
        # Use the standard OCaml bsc for the initial build
        RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" clean 2>/dev/null || true
        if ! RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build 2>&1 | tail -5; then
            echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
        fi
    fi
    cd "$PROJECT_ROOT"
    echo ""
fi

# ============================================================
# TELLA MODE: Compare .ocaml-sexp and .sexp files from lib/ocaml/
# OCaml sexp: generated by `rescript build --dump-typed-sexp` (RESCRIPT_BSC_EXE=ocaml bsc)
# Rust sexp:  generated by `rescript build --rust --subprocess --dump-typed-sexp` (RESCRIPT_BSC_EXE=rust bsc)
# ============================================================
if [[ "$TELLA_MODE" == "true" ]]; then
    RUST_SEXP_DIR="$TEST_PROJECT/lib/ocaml"
    echo -e "${BOLD}Step 2: Comparing sexp files...${RESET}"
    echo "  OCaml sexp: $OCAML_SEXP_CACHE"
    echo "  Rust sexp:  $RUST_SEXP_DIR"
    echo ""

    mkdir -p "$TEMP_DIR/diffs"

    OCAML_PASS=0 OCAML_FAIL=0
    RUST_PASS=0 RUST_FAIL=0 RUST_TIMEOUTS=0 RUST_CRASHES=0
    PARITY_PASS=0 PARITY_FAIL=0
    OCAML_FAILURES=""
    RUST_FAILURES=""
    RUST_TIMEOUT_LIST=""
    RUST_CRASH_LIST=""
    PARITY_FAILURES=""

    # Tella large files list (>5MB sexp output, mostly JSX-heavy components)
    # --tella: skips these files, --tella-jsx: only runs these files
    TELLA_LARGE_FILES_PATH="$PROJECT_ROOT/scripts/tella_large_sexp_files.txt"

    is_tella_large_file() {
        grep -qxF "$1" "$TELLA_LARGE_FILES_PATH" 2>/dev/null
    }

    # Iterate over cached OCaml sexp files
    for ocaml_sexp in "$OCAML_SEXP_CACHE"/*.sexp; do
        [[ -f "$ocaml_sexp" ]] || continue
        basename_no_ext=$(basename "$ocaml_sexp" .sexp)

        # Filter based on --tella vs --tella-jsx
        if [[ "$TELLA_JSX_MODE" == "true" ]]; then
            # --tella-jsx: only large files
            is_tella_large_file "$basename_no_ext" || continue
        else
            # --tella: skip large files
            is_tella_large_file "$basename_no_ext" && continue
        fi
        rust_sexp="$RUST_SEXP_DIR/${basename_no_ext}.sexp"

        # OCaml sexp exists (file was compiled)
        if [[ -s "$ocaml_sexp" ]]; then
            OCAML_PASS=$((OCAML_PASS + 1))
        else
            OCAML_FAIL=$((OCAML_FAIL + 1))
            OCAML_FAILURES="$OCAML_FAILURES  $basename_no_ext\n"
            continue
        fi

        # Check Rust sexp
        if [[ -f "$rust_sexp" && -s "$rust_sexp" ]]; then
            RUST_PASS=$((RUST_PASS + 1))

            # Compare
            if diff -a -q "$ocaml_sexp" "$rust_sexp" > /dev/null 2>&1; then
                PARITY_PASS=$((PARITY_PASS + 1))
            else
                PARITY_FAIL=$((PARITY_FAIL + 1))
                PARITY_FAILURES="$PARITY_FAILURES  $basename_no_ext\n"
                diff -a -u "$ocaml_sexp" "$rust_sexp" > "$TEMP_DIR/diffs/${basename_no_ext}.diff" 2>&1 || true
            fi
        elif [[ -f "$rust_sexp" && ! -s "$rust_sexp" ]]; then
            # Empty = timeout
            RUST_FAIL=$((RUST_FAIL + 1))
            RUST_TIMEOUTS=$((RUST_TIMEOUTS + 1))
            RUST_TIMEOUT_LIST="$RUST_TIMEOUT_LIST  $basename_no_ext\n"
        else
            # Missing = crash
            RUST_FAIL=$((RUST_FAIL + 1))
            RUST_CRASHES=$((RUST_CRASHES + 1))
            RUST_CRASH_LIST="$RUST_CRASH_LIST  $basename_no_ext\n"
        fi
    done

    # Also count modules that have .sexp but no .ocaml-sexp (shouldn't happen, but just in case)
    TOTAL_OCAML=$((OCAML_PASS + OCAML_FAIL))
    echo -e "Found ${BOLD}$TOTAL_OCAML${RESET} modules with OCaml sexp"
    echo ""

else
# ============================================================
# NORMAL MODE: Per-file bsc invocation
# ============================================================

# Find test files based on arguments
cd "$PROJECT_ROOT"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        find tests/tests/src -name "*.res" 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
            echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
            echo "Hint: Try a pattern like 'Core_Array' or a full path"
            exit 1
        fi
    fi
else
    # Find all .res files in tests/tests/src
    find tests/tests/src -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
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
mkdir -p "$TEMP_DIR/diffs"

# Export variables for parallel execution
export OCAML_BSC RUST_BSC RESCRIPT_CLI TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE RUST_AVAILABLE PROJECT_ROOT RESULTS_DIR TEST_PROJECT

# Function to test a single file - writes results to a file
test_single_file() {
    local file="$1"
    local safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    # Initialize result
    local ocaml_pass=0 rust_pass=0 parity_pass=0
    local ocaml_fail=0 rust_fail=0 parity_fail=0
    local rust_timeout=0 rust_crash=0

    # Create per-file temp directory for parallel safety
    local file_temp="$TEMP_DIR/work/$safe_name"
    mkdir -p "$file_temp"

    # Determine full file path (handle both absolute and relative paths)
    local full_file_path
    if [[ "$file" = /* ]]; then
        full_file_path="$file"
    else
        full_file_path="$PROJECT_ROOT/$file"
    fi

    # Get relative path from test project
    local rel_path="${full_file_path#$TEST_PROJECT/}"

    # Helper: run Rust bsc and classify exit code
    run_rust_bsc() {
        local rust_exit=0
        timeout "$TIMEOUT_SECONDS" "$RUST_BSC" "$@" || rust_exit=$?
        if [[ "$rust_exit" -eq 0 ]]; then
            rust_pass=1
        elif [[ "$rust_exit" -eq 124 ]]; then
            rust_timeout=1
            rust_fail=1
        else
            rust_crash=1
            rust_fail=1
        fi
    }

    # Get compiler arguments from rewatch
    local compiler_args_json
    compiler_args_json=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null) || true

    if [[ -z "$compiler_args_json" ]]; then
        # If compiler-args fails, try direct compilation
        if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -dtyped-sexp "$full_file_path" 2> "$file_temp/ocaml.sexp" 1>/dev/null; then
            ocaml_pass=1
        else
            ocaml_fail=1
        fi

        if [[ "$RUST_AVAILABLE" == "true" ]]; then
            run_rust_bsc -dtyped-sexp "$full_file_path" 2> "$file_temp/rust.sexp" 1>/dev/null
        fi
    else
        # Parse the compiler_args array from JSON
        local args
        args=$(echo "$compiler_args_json" | python3 -c "import sys, json; d=json.load(sys.stdin); print(' '.join(d.get('compiler_args', [])))" 2>/dev/null) || args=""

        if [[ -n "$args" ]]; then
            cd "$TEST_PROJECT/lib/bs"
            if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -dtyped-sexp $args 2> "$file_temp/ocaml.sexp" 1>/dev/null; then
                ocaml_pass=1
            else
                ocaml_fail=1
            fi

            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                run_rust_bsc -dtyped-sexp $args 2> "$file_temp/rust.sexp" 1>/dev/null
            fi
            cd "$PROJECT_ROOT"
        else
            ocaml_fail=1
            rust_fail=1
        fi
    fi

    # Compare if both succeeded
    if [[ "$RUST_AVAILABLE" == "true" && "$ocaml_pass" -eq 1 && "$rust_pass" -eq 1 ]]; then
        if diff -q "$file_temp/ocaml.sexp" "$file_temp/rust.sexp" > /dev/null 2>&1; then
            parity_pass=1
        else
            parity_fail=1
            # Save diff for inspection
            diff -ua "$file_temp/ocaml.sexp" "$file_temp/rust.sexp" > "$TEMP_DIR/diffs/$safe_name.diff" 2>&1 || true
            # Save sexp files to persistent cache
            cp "$file_temp/ocaml.sexp" "$CACHE_DIR/tests/ocaml/$safe_name.sexp" 2>/dev/null || true
            cp "$file_temp/rust.sexp" "$CACHE_DIR/tests/rust/$safe_name.sexp" 2>/dev/null || true
        fi
    fi

    # Write result
    echo "$file:ocaml_pass=$ocaml_pass:ocaml_fail=$ocaml_fail:rust_pass=$rust_pass:rust_fail=$rust_fail:rust_timeout=$rust_timeout:rust_crash=$rust_crash:parity_pass=$parity_pass:parity_fail=$parity_fail" > "$result_file"

    # Verbose output
    if [[ "$VERBOSE" == "true" ]]; then
        if [[ "$ocaml_pass" -eq 1 ]]; then
            echo -e "${GREEN}PASS${RESET} [OCaml] $file"
        else
            echo -e "${RED}FAIL${RESET} [OCaml] $file"
        fi
        if [[ "$RUST_AVAILABLE" == "true" ]]; then
            if [[ "$rust_pass" -eq 1 ]]; then
                echo -e "${GREEN}PASS${RESET} [Rust] $file"
            elif [[ "$rust_timeout" -eq 1 ]]; then
                echo -e "${YELLOW}TIMEOUT${RESET} [Rust] $file"
            elif [[ "$rust_crash" -eq 1 ]]; then
                echo -e "${RED}CRASH${RESET} [Rust] $file"
            fi
            if [[ "$parity_pass" -eq 1 ]]; then
                echo -e "${GREEN}PASS${RESET} [Parity] $file"
            elif [[ "$parity_fail" -eq 1 ]]; then
                echo -e "${RED}FAIL${RESET} [Parity] $file"
            fi
        fi
    fi

    # Quick mode - exit on failure
    if [[ "$QUICK_MODE" == "true" && ("$ocaml_fail" -eq 1 || "$parity_fail" -eq 1) ]]; then
        echo -e "${RED}Quick mode: stopping on first failure${RESET}"
        if [[ -f "$TEMP_DIR/diffs/$safe_name.diff" ]]; then
            echo -e "\nParity diff:"
            head -50 "$TEMP_DIR/diffs/$safe_name.diff"
        fi
        exit 1
    fi
}

export -f test_single_file

# Run tests
echo -e "${BOLD}Step 2: Running typed tree parity tests...${RESET}"
echo ""
if [[ "$PARALLEL_JOBS" -eq 1 ]]; then
    while IFS= read -r file; do
        test_single_file "$file"
    done < "$TEMP_DIR/files.txt"
else
    cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {}
fi

# Aggregate results
OCAML_PASS=0 OCAML_FAIL=0
RUST_PASS=0 RUST_FAIL=0 RUST_TIMEOUTS=0 RUST_CRASHES=0
PARITY_PASS=0 PARITY_FAIL=0
OCAML_FAILURES=""
RUST_FAILURES=""
RUST_TIMEOUT_LIST=""
RUST_CRASH_LIST=""
PARITY_FAILURES=""

for result_file in "$RESULTS_DIR"/*.result; do
    [[ -f "$result_file" ]] || continue
    result=$(cat "$result_file")
    file=$(echo "$result" | cut -d: -f1)

    if echo "$result" | grep -q "ocaml_pass=1"; then
        OCAML_PASS=$((OCAML_PASS + 1))
    elif echo "$result" | grep -q "ocaml_fail=1"; then
        OCAML_FAIL=$((OCAML_FAIL + 1))
        OCAML_FAILURES="$OCAML_FAILURES  $file\n"
    fi

    if [[ "$RUST_AVAILABLE" == "true" ]]; then
        if echo "$result" | grep -q "rust_pass=1"; then
            RUST_PASS=$((RUST_PASS + 1))
        elif echo "$result" | grep -q "rust_fail=1"; then
            RUST_FAIL=$((RUST_FAIL + 1))
            if echo "$result" | grep -q "rust_timeout=1"; then
                RUST_TIMEOUTS=$((RUST_TIMEOUTS + 1))
                RUST_TIMEOUT_LIST="$RUST_TIMEOUT_LIST  $file\n"
            elif echo "$result" | grep -q "rust_crash=1"; then
                RUST_CRASHES=$((RUST_CRASHES + 1))
                RUST_CRASH_LIST="$RUST_CRASH_LIST  $file\n"
            else
                RUST_FAILURES="$RUST_FAILURES  $file\n"
            fi
        fi

        if echo "$result" | grep -q "parity_pass=1"; then
            PARITY_PASS=$((PARITY_PASS + 1))
        elif echo "$result" | grep -q "parity_fail=1"; then
            PARITY_FAIL=$((PARITY_FAIL + 1))
            PARITY_FAILURES="$PARITY_FAILURES  $file\n"
        fi
    fi
done

fi # end normal mode

echo -e "OCaml bsc:    ${GREEN}$OCAML_PASS passed${RESET}, ${RED}$OCAML_FAIL failed${RESET}"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    RUST_DETAIL="${GREEN}$RUST_PASS passed${RESET}, ${RED}$RUST_FAIL failed${RESET}"
    if [[ "$RUST_TIMEOUTS" -gt 0 ]]; then
        RUST_DETAIL="$RUST_DETAIL (${YELLOW}$RUST_TIMEOUTS timed out${RESET})"
    fi
    if [[ "$RUST_CRASHES" -gt 0 ]]; then
        RUST_DETAIL="$RUST_DETAIL (${RED}$RUST_CRASHES crashed${RESET})"
    fi
    echo -e "Rust bsc:     $RUST_DETAIL"
    echo -e "Parity:       ${GREEN}$PARITY_PASS passed${RESET}, ${RED}$PARITY_FAIL failed${RESET}"
fi

# Show failures
if [[ -n "$OCAML_FAILURES" && "$OCAML_FAIL" -gt 0 && "$OCAML_FAIL" -le 50 ]]; then
    echo ""
    echo -e "${YELLOW}OCaml failures:${RESET}"
    echo -e "$OCAML_FAILURES"
fi

if [[ "$RUST_AVAILABLE" == "true" && "$RUST_TIMEOUTS" -gt 0 ]]; then
    echo ""
    echo -e "${YELLOW}Rust timeouts (>${TIMEOUT_SECONDS}s):${RESET}"
    echo -e "$RUST_TIMEOUT_LIST"
fi

if [[ "$RUST_AVAILABLE" == "true" && "$RUST_CRASHES" -gt 0 ]]; then
    echo ""
    echo -e "${RED}Rust crashes ($RUST_CRASHES):${RESET}"
    echo -e "$RUST_CRASH_LIST"
fi

if [[ "$RUST_AVAILABLE" == "true" && -n "$RUST_FAILURES" && "$RUST_FAIL" -gt "$((RUST_TIMEOUTS + RUST_CRASHES))" ]]; then
    RUST_OTHER=$((RUST_FAIL - RUST_TIMEOUTS - RUST_CRASHES))
    if [[ "$RUST_OTHER" -le 50 ]]; then
        echo ""
        echo -e "${YELLOW}Rust other failures:${RESET}"
        echo -e "$RUST_FAILURES"
    fi
fi

if [[ "$RUST_AVAILABLE" == "true" && -n "$PARITY_FAILURES" && "$PARITY_FAIL" -gt 0 ]]; then
    echo ""
    if [[ "$PARITY_FAIL" -le 200 ]]; then
        echo -e "${YELLOW}Parity failures (diffs saved in $TEMP_DIR/diffs/):${RESET}"
        echo -e "$PARITY_FAILURES"
    else
        echo -e "${YELLOW}Parity failures: $PARITY_FAIL files (too many to list)${RESET}"
    fi
fi

# Calculate and display parity percentage
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    # Only count files where both compilers succeeded
    BOTH_SUCCEEDED=$((PARITY_PASS + PARITY_FAIL))
    if [[ "$BOTH_SUCCEEDED" -gt 0 ]]; then
        PARITY_PCT=$((100 * PARITY_PASS / BOTH_SUCCEEDED))
        echo ""
        echo "============================================"
        if [[ "$PARITY_FAIL" -eq 0 ]]; then
            echo -e "${GREEN}${BOLD}SUCCESS: All $PARITY_PASS files have matching typed trees!${RESET}"
        else
            # Count total hunks across all diff files
            TOTAL_HUNKS=0
            for diff_file in "$TEMP_DIR"/diffs/*.diff; do
                if [[ -f "$diff_file" ]]; then
                    file_hunks=$(grep -c '^@@' "$diff_file" 2>/dev/null || echo 0)
                    TOTAL_HUNKS=$((TOTAL_HUNKS + file_hunks))
                fi
            done
            echo -e "${YELLOW}${BOLD}Parity: $PARITY_PASS/$BOTH_SUCCEEDED files match ($PARITY_PCT%), $TOTAL_HUNKS hunk mismatches${RESET}"
        fi
    fi
fi
