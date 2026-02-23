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
#   --with-locs       Use -dtyped-sexp-locs (with locations) instead of -dtyped-sexp
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

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=16
VERBOSE=false
FILE_ARG=""
SKIP_BUILD=false
WITH_LOCS=false

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
        --with-locs)
            WITH_LOCS=true
            shift
            ;;
        -h|--help)
            head -35 "$0" | tail -30
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
# Prefer the pre-built bsc.exe (stable reference) over dune-built bsc (may have local patches)
PREBUILT_BSC="$PROJECT_ROOT/packages/@rescript/darwin-arm64/bin/bsc.exe"
if [[ -x "$PREBUILT_BSC" ]]; then
    OCAML_BSC="$PREBUILT_BSC"
else
    OCAML_BSC="$DUNE_BIN_DIR/bsc"
fi
RUST_BSC="$PROJECT_ROOT/compiler-rust/target/release/bsc"
RESCRIPT_CLI="$PROJECT_ROOT/packages/@rescript/darwin-arm64/bin/rescript.exe"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
GENERATED_OUTPUT_SCOPE="tests/tests/src"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

# Configuration
TIMEOUT_SECONDS=10
if [[ "$WITH_LOCS" == "true" ]]; then
    SEXP_FLAG="-dtyped-sexp-locs"
else
    SEXP_FLAG="-dtyped-sexp"
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

# Record untracked JS-like files before running so we can remove only newly generated ones.
capture_untracked_js_snapshot() {
    local output_file="$1"
    git -C "$PROJECT_ROOT" ls-files --others --exclude-standard -- "$GENERATED_OUTPUT_SCOPE" \
        | grep -E '\.(js|mjs|cjs)$' > "$output_file" || true
}

cleanup_generated_js_outputs() {
    if [[ -z "${UNTRACKED_JS_BEFORE_FILE:-}" || ! -f "$UNTRACKED_JS_BEFORE_FILE" ]]; then
        return
    fi

    local untracked_after_file="$TEMP_DIR/untracked_js_after.txt"
    local newly_generated_file="$TEMP_DIR/untracked_js_new.txt"
    local removed_count

    capture_untracked_js_snapshot "$untracked_after_file"
    comm -13 <(sort "$UNTRACKED_JS_BEFORE_FILE") <(sort "$untracked_after_file") > "$newly_generated_file" || true

    if [[ -s "$newly_generated_file" ]]; then
        while IFS= read -r rel_file; do
            [[ -n "$rel_file" ]] || continue
            rm -f "$PROJECT_ROOT/$rel_file"
        done < "$newly_generated_file"

        removed_count=$(wc -l < "$newly_generated_file" | tr -d ' ')
        echo -e "${YELLOW}Cleanup: removed ${removed_count} generated JS/MJS/CJS files.${RESET}"
    fi
}

# Create temp directory
TEMP_DIR=$(mktemp -d)
UNTRACKED_JS_BEFORE_FILE="$TEMP_DIR/untracked_js_before.txt"
capture_untracked_js_snapshot "$UNTRACKED_JS_BEFORE_FILE"
trap "cleanup_generated_js_outputs; rm -rf $TEMP_DIR" EXIT

timer_start() { date +%s; }
timer_elapsed() { local start=$1; echo "$(($(date +%s) - start))s"; }
SCRIPT_START=$(timer_start)

# Always use -dtyped-sexp-locs since rewatch --dump-typed-sexp --rust generates with-locs
SEXP_FLAG="-dtyped-sexp-locs"

# OCaml sexp cache directory
CACHE_DIR="$PROJECT_ROOT/.cache/parity"
mkdir -p "$CACHE_DIR"

echo -e "${BOLD}Typed Tree Parity Test${RESET}"
echo "============================================"
echo "OCaml bsc: $OCAML_BSC"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo "Rust bsc:  $RUST_BSC"
else
    echo "Rust bsc:  (not available)"
fi
echo "Sexp flag: $SEXP_FLAG"
echo "Rust sexp: in-process via rewatch (cached in lib/ocaml/)"
echo "OCaml cache: $CACHE_DIR"
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

# Step 1: Build with rewatch to ensure all dependencies are compiled
if [[ "$SKIP_BUILD" != "true" ]]; then
    echo -e "${BOLD}Step 1: Building test project with rewatch...${RESET}"
    cd "$TEST_PROJECT"
    RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" clean 2>/dev/null || true
    if ! RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build --dump-typed-sexp --rust 2>&1 | tail -5; then
        echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
    fi
    cd "$PROJECT_ROOT"
    echo ""
fi

# Pre-compute compiler base args once (not per-file)
PRECOMPUTE_START=$(timer_start)
TEST_BASE_ARGS=""
if [[ -d "$TEST_PROJECT/lib/bs" ]]; then
    TEST_BASE_ARGS=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args src/a.res 2>/dev/null \
        | jq -r '.compiler_args[:-1] | join(" ")' 2>/dev/null) || TEST_BASE_ARGS=""
fi
echo -e "  [timer] Pre-compute args: $(timer_elapsed $PRECOMPUTE_START)"

# Find test files based on arguments
cd "$PROJECT_ROOT"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        # Treat as a pattern and use find with -path
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
export OCAML_BSC RUST_BSC RESCRIPT_CLI TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE RUST_AVAILABLE PROJECT_ROOT RESULTS_DIR TEST_PROJECT SEXP_FLAG
export TEST_BASE_ARGS CACHE_DIR

# Function to test a single file - writes results to a file
test_single_file() {
    local file="$1"
    local safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    local ocaml_pass=0 rust_pass=0 parity_pass=0
    local ocaml_fail=0 rust_fail=0 parity_fail=0

    local file_temp="$TEMP_DIR/work/$safe_name"
    mkdir -p "$file_temp"

    local full_file_path
    if [[ "$file" = /* ]]; then
        full_file_path="$file"
    else
        full_file_path="$PROJECT_ROOT/$file"
    fi

    # --- OCaml sexp: check cache first ---
    local basename="${full_file_path##*/}"
    local ext="${basename##*.}"
    local ast_file
    if [[ "$ext" == "resi" ]]; then
        ast_file="$TEST_PROJECT/lib/ocaml/${basename%.resi}.iast"
    else
        ast_file="$TEST_PROJECT/lib/ocaml/${basename%.res}.ast"
    fi
    local cache_key="" cache_file=""
    if [[ -f "$ast_file" ]]; then
        cache_key=$(md5 -q "$ast_file" 2>/dev/null) || cache_key=""
        if [[ -n "$cache_key" ]]; then
            cache_file="$CACHE_DIR/${cache_key}.sexp"
        fi
    fi

    local ocaml_cached=false
    if [[ -n "$cache_file" && -f "$cache_file" ]]; then
        cp "$cache_file" "$file_temp/ocaml.sexp"
        ocaml_cached=true
    fi

    # --- Rust sexp: use cached from rewatch --dump-typed-sexp --rust ---
    if [[ "$RUST_AVAILABLE" == "true" ]]; then
        local stem="${basename%.*}"
        if [[ -f "$TEST_PROJECT/lib/ocaml/${stem}.sexp" ]]; then
            cp "$TEST_PROJECT/lib/ocaml/${stem}.sexp" "$file_temp/rust.sexp"
        fi
    fi

    # --- OCaml: invoke bsc if not cached ---
    if [[ "$ocaml_cached" != "true" && -n "$TEST_BASE_ARGS" ]]; then
        local rel_path="${full_file_path#$TEST_PROJECT/}"
        local ast_arg
        if [[ "$ext" == "resi" ]]; then
            ast_arg="${rel_path%.resi}.iast"
        else
            ast_arg="${rel_path%.res}.ast"
        fi
        cd "$TEST_PROJECT/lib/bs"
        timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $TEST_BASE_ARGS $ast_arg 2> "$file_temp/ocaml.sexp" 1>/dev/null || true
        cd "$PROJECT_ROOT"
    fi

    # --- Strip warnings from sexp output ---
    if [[ "$ocaml_cached" != "true" && -f "$file_temp/ocaml.sexp" ]]; then
        LC_ALL=C sed -E -n '/^\(structure|^\(signature/,$p' "$file_temp/ocaml.sexp" | LC_ALL=C sed '/^$/,$d' > "$file_temp/ocaml_clean.sexp"
        mv "$file_temp/ocaml_clean.sexp" "$file_temp/ocaml.sexp"
        # Cache result (including empty = OCaml error)
        if [[ -n "$cache_file" ]]; then
            cp "$file_temp/ocaml.sexp" "$cache_file"
        fi
    fi
    if [[ -f "$file_temp/rust.sexp" ]]; then
        LC_ALL=C sed -E -n '/^\(structure|^\(signature/,$p' "$file_temp/rust.sexp" | LC_ALL=C sed '/^$/,$d' > "$file_temp/rust_clean.sexp"
        mv "$file_temp/rust_clean.sexp" "$file_temp/rust.sexp"
    fi

    # --- Determine pass/fail ---
    if [[ -s "$file_temp/ocaml.sexp" ]]; then
        ocaml_pass=1
    else
        ocaml_fail=1
    fi
    if [[ -s "$file_temp/rust.sexp" ]]; then
        rust_pass=1
    else
        rust_fail=1
    fi

    # --- Compare if both succeeded ---
    if [[ "$RUST_AVAILABLE" == "true" && "$ocaml_pass" -eq 1 && "$rust_pass" -eq 1 ]]; then
        LC_ALL=C tr -cd '[:print:]\n' < "$file_temp/ocaml.sexp" > "$file_temp/ocaml_text.sexp" 2>/dev/null || cp "$file_temp/ocaml.sexp" "$file_temp/ocaml_text.sexp"
        LC_ALL=C tr -cd '[:print:]\n' < "$file_temp/rust.sexp" > "$file_temp/rust_text.sexp" 2>/dev/null || cp "$file_temp/rust.sexp" "$file_temp/rust_text.sexp"
        if diff -q "$file_temp/ocaml_text.sexp" "$file_temp/rust_text.sexp" > /dev/null 2>&1; then
            parity_pass=1
        else
            parity_fail=1
            diff -u "$file_temp/ocaml_text.sexp" "$file_temp/rust_text.sexp" > "$TEMP_DIR/diffs/$safe_name.diff" 2>&1 || true
        fi
    fi

    echo "$file:ocaml_pass=$ocaml_pass:ocaml_fail=$ocaml_fail:rust_pass=$rust_pass:rust_fail=$rust_fail:parity_pass=$parity_pass:parity_fail=$parity_fail" > "$result_file"

    if [[ "$VERBOSE" == "true" ]]; then
        if [[ "$parity_pass" -eq 1 ]]; then
            echo -e "${GREEN}PASS${RESET} $file"
        elif [[ "$parity_fail" -eq 1 ]]; then
            echo -e "${RED}FAIL${RESET} $file"
        elif [[ "$ocaml_pass" -eq 1 && "$rust_fail" -eq 1 ]]; then
            echo -e "${YELLOW}RUST_FAIL${RESET} $file"
        fi
    fi

    if [[ "$QUICK_MODE" == "true" && "$parity_fail" -eq 1 ]]; then
        echo -e "${RED}Quick mode: stopping on first parity failure${RESET}"
        if [[ -f "$TEMP_DIR/diffs/$safe_name.diff" ]]; then
            echo -e "\nParity diff:"
            head -50 "$TEMP_DIR/diffs/$safe_name.diff"
        fi
        exit 1
    fi
}

export -f test_single_file

# Run tests
STEP2_START=$(timer_start)
echo -e "${BOLD}Step 2: Running typed tree parity tests...${RESET}"
echo ""
if [[ "$PARALLEL_JOBS" -eq 1 ]]; then
    while IFS= read -r file; do
        test_single_file "$file"
    done < "$TEMP_DIR/files.txt"
else
    cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {}
fi

echo -e "  [timer] Step 2 (test files): $(timer_elapsed $STEP2_START)"

# Aggregate results
echo ""
echo -e "${BOLD}Results${RESET}"
echo "========"

# Count results using awk (fast single pass)
AGG_FILE="$TEMP_DIR/aggregated.sh"
cat "$RESULTS_DIR"/*.result 2>/dev/null | awk -F: '
{
    file = $1
    delete v
    for (i = 2; i <= NF; i++) {
        n = split($i, kv, "=")
        if (n == 2) v[kv[1]] = kv[2]
    }
    G["OCAML_PASS"] += v["ocaml_pass"]
    G["OCAML_FAIL"] += v["ocaml_fail"]
    G["RUST_PASS"] += v["rust_pass"]
    G["RUST_FAIL"] += v["rust_fail"]
    G["PARITY_PASS"] += v["parity_pass"]
    G["PARITY_FAIL"] += v["parity_fail"]
    if (v["ocaml_pass"] == 1 && v["rust_fail"] == 1) { G["OCAML_ONLY"]++; ocaml_only = ocaml_only "  " file "\n" }
    if (v["ocaml_fail"] == 1 && v["rust_pass"] == 1) { G["RUST_ONLY"]++; rust_only = rust_only "  " file "\n" }
    if (v["parity_fail"] == 1) parity_failures = parity_failures "  " file "\n"
}
END {
    for (k in G) printf "%s=%d\n", k, G[k]+0
    printf "PARITY_FAILURES=\"%s\"\n", parity_failures
    printf "OCAML_ONLY_FILES=\"%s\"\n", ocaml_only
    printf "RUST_ONLY_FILES=\"%s\"\n", rust_only
}
' > "$AGG_FILE"

OCAML_PASS=0 OCAML_FAIL=0 RUST_PASS=0 RUST_FAIL=0 PARITY_PASS=0 PARITY_FAIL=0 OCAML_ONLY=0 RUST_ONLY=0
PARITY_FAILURES="" OCAML_ONLY_FILES="" RUST_ONLY_FILES=""
source "$AGG_FILE"

BOTH_SUCCEEDED=$((PARITY_PASS + PARITY_FAIL))

echo -e "  OCaml type-check: ${GREEN}$OCAML_PASS${RESET}   OCaml error: ${RED}$OCAML_FAIL${RESET}"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo -e "  Rust  type-check: ${GREEN}$RUST_PASS${RESET}   Rust  error: ${RED}$RUST_FAIL${RESET}"
    if [[ "$BOTH_SUCCEEDED" -gt 0 ]]; then
        PARITY_PCT=$((100 * PARITY_PASS / BOTH_SUCCEEDED))
        echo -e "  Typecheck parity: ${GREEN}$PARITY_PASS${RESET}/$BOTH_SUCCEEDED (${PARITY_PCT}%)"
    fi
    if [[ "$OCAML_ONLY" -gt 0 ]]; then
        echo -e "  ${YELLOW}OCaml-only pass (Rust rejects): $OCAML_ONLY${RESET}"
    fi
    if [[ "$RUST_ONLY" -gt 0 ]]; then
        echo -e "  ${YELLOW}Rust-only pass (OCaml rejects): $RUST_ONLY${RESET}"
    fi
fi
echo "============================================"

if [[ "$RUST_AVAILABLE" == "true" && "$PARITY_FAIL" -eq 0 && "$BOTH_SUCCEEDED" -gt 0 ]]; then
    echo -e "${GREEN}${BOLD}SUCCESS: All $PARITY_PASS files have matching typed trees!${RESET}"
elif [[ "$BOTH_SUCCEEDED" -gt 0 ]]; then
    echo -e "${YELLOW}${BOLD}Parity: $PARITY_PASS/$BOTH_SUCCEEDED files match ($PARITY_PCT%)${RESET}"
fi

if [[ "$PARITY_FAIL" -gt 0 && -n "$PARITY_FAILURES" ]]; then
    echo ""
    echo -e "${YELLOW}Parity failures ($PARITY_FAIL):${RESET}"
    echo -e "$PARITY_FAILURES"
fi

echo -e "  [timer] Total: $(timer_elapsed $SCRIPT_START)"
echo -e "Diffs saved in: $TEMP_DIR/diffs/"
