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
#   -j, --parallel N  Run N tests in parallel (default: 8)
#   -v, --verbose     Show progress for each file
#   --release         Use target/release Rust compiler artifacts
#   --tella           Test tella-fusion, skipping large JSX-heavy files
#   --tella-jsx       Test only large JSX-heavy tella files
#   --tella-fast      Extra-fast tella mode (also skip files > 5000 bytes)
#   --stdlib          Test the runtime/standard-library sources
#   --tella-max-source-bytes N
#                     In tella mode, skip source files larger than N bytes
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
#   # Run all tests in parallel (default 8 jobs):
#   ./scripts/test_typedtree_parity.sh
#
#   # Test tella-fusion project:
#   ./scripts/test_typedtree_parity.sh --tella
#
#   # Test only large JSX-heavy tella files:
#   ./scripts/test_typedtree_parity.sh --tella-jsx
#
#   # Extra-fast tella run:
#   ./scripts/test_typedtree_parity.sh --tella-fast
#
#   # Test runtime/standard-library sources:
#   ./scripts/test_typedtree_parity.sh --stdlib

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=8
VERBOSE=false
FILE_ARG=""
TELLA_MODE=false
TELLA_JSX_MODE=false
TELLA_MAX_SOURCE_BYTES=0
STDLIB_MODE=false

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
        --release)
            RUST_TARGET=release
            shift
            ;;
        --no-build)
            echo -e "Error: --no-build was removed."
            echo "This script now always rebuilds the test project's ReScript artifacts."
            echo "Run ./scripts/test_typedtree_parity.sh without --no-build."
            exit 2
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
        --tella-fast)
            TELLA_MODE=true
            TELLA_MAX_SOURCE_BYTES=5000
            shift
            ;;
        --stdlib)
            STDLIB_MODE=true
            shift
            ;;
        --tella-max-source-bytes)
            TELLA_MODE=true
            TELLA_MAX_SOURCE_BYTES="$2"
            shift 2
            ;;
        -h|--help)
            sed -n '10,48p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        -*)
            echo -e "Error: unknown option: $1"
            exit 2
            ;;
        *)
            FILE_ARG="$1"
            shift
            ;;
    esac
done

if ! [[ "$TELLA_MAX_SOURCE_BYTES" =~ ^[0-9]+$ ]]; then
    echo -e "Error: --tella-max-source-bytes expects a non-negative integer"
    exit 1
fi

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)
RUST_TARGET="${RUST_TARGET:-debug}"
source "$PROJECT_ROOT/scripts/parity_lib.sh"
RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
BUILD_DIR="$TEST_PROJECT"
STDLIB_PROJECT="$PROJECT_ROOT/packages/@rescript/runtime"

# Tella mode configuration
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
if [[ "$STDLIB_MODE" == "true" && "$TELLA_MODE" == "true" ]]; then
    echo -e "Error: --stdlib cannot be combined with --tella"
    exit 1
fi

if [[ "$STDLIB_MODE" == "true" ]]; then
    if [[ ! -f "$STDLIB_PROJECT/rescript.json" ]]; then
        echo -e "Error: runtime rescript.json not found at $STDLIB_PROJECT"
        exit 1
    fi
    BUILD_DIR="$STDLIB_PROJECT"
    TEST_PROJECT="$STDLIB_PROJECT"
elif [[ "$TELLA_MODE" == "true" ]]; then
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
    TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-30}"
else
    TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10}"
fi

# Check if compilers exist
if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    echo "Run 'make' first to build the OCaml compiler."
    exit 1
fi

# The Rust side is the compiler linked into rescript, run in process.
if [[ ! -x "$RESCRIPT_CLI" ]]; then
    echo -e "${RED}Error: rescript not found at $RESCRIPT_CLI${RESET}"
    if [[ "$RUST_TARGET" == "release" ]]; then
        echo "Run 'cargo build --release --manifest-path rewatch/Cargo.toml' first."
    else
        echo "Run 'cargo build --manifest-path rewatch/Cargo.toml' first."
    fi
    exit 1
fi
RUST_AVAILABLE=true


if [[ ! -d "$RESCRIPT_RUNTIME" ]]; then
    echo -e "${RED}Error: ReScript runtime package not found at $RESCRIPT_RUNTIME${RESET}"
    echo "Set RESCRIPT_RUNTIME to the runtime package matching the compiler under test."
    exit 1
fi
export RESCRIPT_RUNTIME

# Create temp directory
if [[ -n "${TMPDIR:-}" ]]; then
    mkdir -p "$TMPDIR"
    TEMP_DIR=$(mktemp -d "$TMPDIR/typedtree-parity.XXXXXX")
else
    TEMP_DIR=$(mktemp -d)
fi
CACHE_DIR="$PROJECT_ROOT/.parity-cache"
mkdir -p "$CACHE_DIR/tests/diffs" "$CACHE_DIR/tests/ocaml" "$CACHE_DIR/tests/rust"
BUILD_LOCK_DIR="$CACHE_DIR/typedtree-build.lock"
BUILD_LOCK_HELD=false

copy_cached_diffs() {
    cp -r "$TEMP_DIR"/diffs/* "$CACHE_DIR/tests/diffs/" 2>/dev/null || true
}

release_build_lock() {
    if [[ "$BUILD_LOCK_HELD" != "true" ]]; then
        return
    fi
    rm -f "$BUILD_LOCK_DIR/pid" 2>/dev/null || true
    rmdir "$BUILD_LOCK_DIR" 2>/dev/null || true
    BUILD_LOCK_HELD=false
}

cleanup() {
    copy_cached_diffs
    release_build_lock
    find "$TEMP_DIR" -type f -delete 2>/dev/null || true
    find "$TEMP_DIR" -depth -type d -empty -delete 2>/dev/null || true
}

acquire_build_lock() {
    local waited=false
    while ! mkdir "$BUILD_LOCK_DIR" 2>/dev/null; do
        if [[ -f "$BUILD_LOCK_DIR/pid" ]]; then
            local lock_pid
            lock_pid=$(cat "$BUILD_LOCK_DIR/pid" 2>/dev/null || true)
            if [[ -n "$lock_pid" ]] && ! kill -0 "$lock_pid" 2>/dev/null; then
                rm -f "$BUILD_LOCK_DIR/pid" 2>/dev/null || true
                rmdir "$BUILD_LOCK_DIR" 2>/dev/null || true
                continue
            fi
        fi
        if [[ "$waited" != "true" ]]; then
            echo "Another typedtree parity run is building shared artifacts; waiting for the build lock..."
            waited=true
        fi
        sleep 0.2
    done
    echo "$$" > "$BUILD_LOCK_DIR/pid"
    BUILD_LOCK_HELD=true
}

trap cleanup EXIT

if [[ "$STDLIB_MODE" == "true" ]]; then
    echo -e "${BOLD}Typed Tree Parity Test (stdlib/runtime)${RESET}"
elif [[ "$TELLA_MODE" == "true" ]]; then
    echo -e "${BOLD}Typed Tree Parity Test (tella-fusion)${RESET}"
else
    echo -e "${BOLD}Typed Tree Parity Test${RESET}"
fi
echo "============================================"
echo "OCaml bsc: $OCAML_BSC"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo "Rust:      $RESCRIPT_CLI (in-process build dumps)"
    echo "Rust target: $RUST_TARGET"
else
    echo "Rust bsc:  (not available)"
fi
echo "Runtime:   $RESCRIPT_RUNTIME"
if [[ "$TELLA_MODE" == "true" ]]; then
    echo "Tella dir: $TELLA_DIR"
    if [[ "$TELLA_JSX_MODE" == "true" ]]; then
        echo "Tella set: large JSX-heavy files only"
    else
        echo "Tella set: excluding large JSX-heavy files"
    fi
    if [[ "$TELLA_MAX_SOURCE_BYTES" -gt 0 ]]; then
        echo "Tella source-size cap: <= ${TELLA_MAX_SOURCE_BYTES} bytes"
    fi
fi
if [[ "$STDLIB_MODE" == "true" ]]; then
    echo "Stdlib project: $STDLIB_PROJECT"
fi
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

RUST_DUMP_DIR="$CACHE_DIR/typedtree/rust-dumps"
echo -e "${BOLD}Step 1: Building with the Rust compiler (in process, --dump typedtree)...${RESET}"
acquire_build_lock
if ! parity_build_rust_dumps "$BUILD_DIR" "$RUST_DUMP_DIR" typedtree 2>&1 | tail -5; then
    echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
fi
echo -e "${BOLD}Step 2: Building the OCaml reference...${RESET}"
if ! parity_build_ocaml_reference "$BUILD_DIR" 2>&1 | tail -5; then
    echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
fi
TEST_PACKAGE_NAME=$(parity_package_name "$TEST_PROJECT")
cd "$PROJECT_ROOT"
release_build_lock
echo ""

# Find test files based on arguments
cd "$PROJECT_ROOT"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        # Treat as a pattern
        if [[ "$STDLIB_MODE" == "true" ]]; then
            find "$STDLIB_PROJECT" -maxdepth 1 \( -name "*.res" -o -name "*.resi" \) -type f 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        elif [[ "$TELLA_MODE" == "true" ]]; then
            find "$TEST_PROJECT/src" "$TEST_PROJECT/lambda/src" "$TEST_PROJECT/chrome/src" "$TEST_PROJECT/scripts" \
                -name "*.res" -type f 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        else
            find tests/tests/src -name "*.res" 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        fi
        if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
            echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
            echo "Hint: Try a pattern like 'Core_Array' or a full path"
            exit 1
        fi
    fi
elif [[ "$STDLIB_MODE" == "true" ]]; then
    # Include interfaces in typedtree parity; bsc prints typed signatures for .iast files.
    find "$STDLIB_PROJECT" -maxdepth 1 \( -name "*.res" -o -name "*.resi" \) -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
elif [[ "$TELLA_MODE" == "true" ]]; then
    # Find all .res files in tella webapp source directories
    find "$TEST_PROJECT/src" "$TEST_PROJECT/lambda/src" "$TEST_PROJECT/chrome/src" "$TEST_PROJECT/scripts" \
        -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
else
    # Find all .res files in tests/tests/src
    find tests/tests/src -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
fi

# In tella mode, split files by precomputed large-sexp module list.
# --tella: exclude large files, --tella-jsx: include only large files.
if [[ "$TELLA_MODE" == "true" ]]; then
    TELLA_LARGE_FILES_PATH="$PROJECT_ROOT/scripts/tella_large_sexp_files.txt"
    if [[ -f "$TELLA_LARGE_FILES_PATH" ]]; then
        FILTERED_FILES="$TEMP_DIR/files.filtered.txt"
        : > "$FILTERED_FILES"
        skipped_large=0
        skipped_size=0
        kept=0

        while IFS= read -r file; do
            [[ -n "$file" ]] || continue
            basename_no_ext=$(basename "$file" .res)
            if grep -qxF "$basename_no_ext" "$TELLA_LARGE_FILES_PATH"; then
                is_large=1
            else
                is_large=0
            fi

            keep_file=1
            if [[ "$TELLA_JSX_MODE" == "true" ]]; then
                if [[ "$is_large" -eq 0 ]]; then
                    keep_file=0
                    skipped_large=$((skipped_large + 1))
                fi
            else
                if [[ "$is_large" -eq 1 ]]; then
                    keep_file=0
                    skipped_large=$((skipped_large + 1))
                fi
            fi

            if [[ "$keep_file" -eq 1 && "$TELLA_MAX_SOURCE_BYTES" -gt 0 ]]; then
                source_size=$(wc -c < "$file" | tr -d ' ')
                if [[ "$source_size" -gt "$TELLA_MAX_SOURCE_BYTES" ]]; then
                    keep_file=0
                    skipped_size=$((skipped_size + 1))
                fi
            fi

            if [[ "$keep_file" -eq 1 ]]; then
                echo "$file" >> "$FILTERED_FILES"
                kept=$((kept + 1))
            fi
        done < "$TEMP_DIR/files.txt"

        mv "$FILTERED_FILES" "$TEMP_DIR/files.txt"
        echo "Tella filter kept $kept files (skipped $skipped_large by large-file list, $skipped_size by source-size cap)"
    else
        echo -e "${YELLOW}Warning: $TELLA_LARGE_FILES_PATH not found; using all tella files${RESET}"
    fi
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
export OCAML_BSC RESCRIPT_CLI RUST_DUMP_DIR TEST_PACKAGE_NAME TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE RUST_AVAILABLE PROJECT_ROOT RESULTS_DIR TEST_PROJECT TELLA_MODE STDLIB_MODE CACHE_DIR

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

    local ocaml_cache="$CACHE_DIR/tests/ocaml/$safe_name.sexp"
    local rust_cache="$CACHE_DIR/tests/rust/$safe_name.sexp"
    local diff_cache="$CACHE_DIR/tests/diffs/$safe_name.diff"
    rm -f "$ocaml_cache" "$rust_cache" "$diff_cache"

    # Determine full file path (handle both absolute and relative paths)
    local full_file_path
    if [[ "$file" = /* ]]; then
        full_file_path="$file"
    else
        full_file_path="$PROJECT_ROOT/$file"
    fi

    # Get relative path from test project
    local rel_path="${full_file_path#$TEST_PROJECT/}"

    # The Rust output is the dump of the in-process build (Step 1).
    run_rust_bsc() {
        local dump="$RUST_DUMP_DIR/$TEST_PACKAGE_NAME/$rel_path.typedtree"
        if [[ -f "$dump" ]]; then
            cat "$dump" >&2
            rust_pass=1
        else
            echo "no typedtree dump: the in-process build did not compile $rel_path" >&2
            rust_crash=1
            rust_fail=1
        fi
    }

    # Get compiler arguments from rewatch
    local compiler_args_json
    compiler_args_json=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null) || true

    if [[ -z "$compiler_args_json" ]]; then
        # If compiler-args fails, try direct compilation
        # Run OCaml compiler directly
        if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -dtyped-sexp "$full_file_path" 2> "$file_temp/ocaml.sexp" 1>/dev/null; then
            ocaml_pass=1
        else
            ocaml_fail=1
        fi

        if [[ "$RUST_AVAILABLE" == "true" ]]; then
            run_rust_bsc -dtyped-sexp "$full_file_path" 2> "$file_temp/rust.sexp" 1>/dev/null
        fi
    else
        # Extract compiler args from JSON and build command
        # Parse the compiler_args array from JSON
        local args
        args=$(echo "$compiler_args_json" | python3 -c "import os, sys, json
d = json.load(sys.stdin)
compiler_args = d.get('compiler_args', [])
runtime = os.environ.get('RESCRIPT_RUNTIME')
rewritten = []
i = 0
while i < len(compiler_args):
    if compiler_args[i] == '-runtime-path' and i + 1 < len(compiler_args) and runtime:
        rewritten.extend([compiler_args[i], runtime])
        i += 2
    else:
        rewritten.append(compiler_args[i])
        i += 1
print(' '.join(rewritten))" 2>/dev/null) || args=""

        if [[ -n "$args" ]]; then
            # Tella keeps some checked-in JS outputs that a normal build can
            # consider up to date without regenerating lib/bs/*.ast. Generate
            # the parser artifact on demand so this harness measures typedtree
            # parity, not whether rewatch happened to rebuild the source file.
            local ast_arg parser_args
            ast_arg=$(echo "$compiler_args_json" | python3 -c "import sys, json; args=json.load(sys.stdin).get('compiler_args', []); print(args[-1] if args else '')" 2>/dev/null) || ast_arg=""
            if [[ -n "$ast_arg" && ! -f "$TEST_PROJECT/lib/bs/$ast_arg" ]]; then
                parser_args=$(echo "$compiler_args_json" | python3 -c "import sys, json; d=json.load(sys.stdin); print(' '.join(d.get('parser_args', [])))" 2>/dev/null) || parser_args=""
                if [[ -n "$parser_args" ]]; then
                    (
                        cd "$TEST_PROJECT/lib/bs"
                        mkdir -p "$(dirname "$ast_arg")"
                        timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $parser_args 2> "$file_temp/parser.err" 1>/dev/null
                    ) || true
                fi
            fi

            # Run OCaml compiler with the args + -dtyped-sexp
            cd "$TEST_PROJECT/lib/bs"
            if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -dtyped-sexp $args 2> "$file_temp/ocaml.sexp" 1>/dev/null; then
                ocaml_pass=1
            else
                ocaml_fail=1
            fi

            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                # Run Rust compiler per-file
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
            cp "$file_temp/ocaml.sexp" "$ocaml_cache" 2>/dev/null || true
            cp "$file_temp/rust.sexp" "$rust_cache" 2>/dev/null || true
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

    find "$file_temp" -type f -delete 2>/dev/null || true
    find "$file_temp" -depth -type d -empty -delete 2>/dev/null || true

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
echo -e "${BOLD}Step 3: Running typed tree parity tests...${RESET}"
echo ""
if [[ "$PARALLEL_JOBS" -eq 1 ]]; then
    while IFS= read -r file; do
        test_single_file "$file"
    done < "$TEMP_DIR/files.txt"
else
    cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {}
fi

# Aggregate results
echo ""
echo -e "${BOLD}Results${RESET}"
echo "========"

# Count results
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
# A matching subset is not a successful parity run when either compiler failed.
if [[ "$OCAML_FAIL" -gt 0 || ("$RUST_AVAILABLE" == "true" && ("$RUST_FAIL" -gt 0 || "$PARITY_FAIL" -gt 0)) ]]; then
    exit 1
fi

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
