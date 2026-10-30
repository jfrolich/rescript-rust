#!/bin/bash

# Lambda IR Parity Test Suite: Compare Lambda IR output between OCaml and Rust compilers.
#
# Tests performed:
# 1. sexp parity - Lambda IR structure matches between OCaml and Rust
# 2. sexp-locs parity - Lambda IR structure + locations match
#
# Uses rescript compiler-args to invoke both compilers with the same per-file arguments.
#
# USAGE:
#   ./scripts/test_lambda_parity.sh [OPTIONS] [FILE|PATTERN]
#
# OPTIONS:
#   -q, --quick       Stop on first failure (useful for quick iteration)
#   -j, --parallel N  Run N tests in parallel (default: 8)
#   -v, --verbose     Show progress for each file
#   --release         Use target/release Rust compiler artifacts
#   -l, --locs        Test with locations (-dlambda-sexp-locs)
#   -r, --raw         Test unoptimized lambda printer output (-drawlambda)
#   -u, --unoptimized Alias for --raw; compare pre-optimization lambda
#   --stdlib          Test runtime/standard-library implementation sources
#   -h, --help        Show this help message
#
# EXAMPLES:
#   ./scripts/test_lambda_parity.sh tests/tests/src/core/Core_ArrayTest.res
#   ./scripts/test_lambda_parity.sh "Core_"
#   ./scripts/test_lambda_parity.sh --quick
#   ./scripts/test_lambda_parity.sh
#   ./scripts/test_lambda_parity.sh --stdlib Belt_Id

set -e

QUICK_MODE=false
PARALLEL_JOBS=8
VERBOSE=false
TEST_LOCS=false
TEST_RAW=false
FILE_ARG=""
STDLIB_MODE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -q|--quick)
            QUICK_MODE=true
            PARALLEL_JOBS=1
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
        -l|--locs)
            TEST_LOCS=true
            shift
            ;;
        -r|--raw|-u|--unoptimized)
            TEST_RAW=true
            shift
            ;;
        --stdlib)
            STDLIB_MODE=true
            shift
            ;;
        -h|--help)
            sed -n '11,28p' "$0" | sed 's/^# \{0,1\}//'
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
RUST_TARGET="${RUST_TARGET:-debug}"
source "$PROJECT_ROOT/scripts/parity_lib.sh"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
BUILD_DIR="$TEST_PROJECT"
STDLIB_PROJECT="$PROJECT_ROOT/packages/@rescript/runtime"

if [[ "$STDLIB_MODE" == "true" ]]; then
    if [[ ! -f "$STDLIB_PROJECT/rescript.json" ]]; then
        echo -e "Error: runtime rescript.json not found at $STDLIB_PROJECT"
        exit 1
    fi
    TEST_PROJECT="$STDLIB_PROJECT"
    BUILD_DIR="$STDLIB_PROJECT"
fi

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

TIMEOUT_SECONDS=10

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


TEMP_DIR=$(mktemp -d)
CACHE_DIR="$PROJECT_ROOT/.parity-cache"
mkdir -p "$CACHE_DIR/lambda/diffs" "$CACHE_DIR/lambda/ocaml" "$CACHE_DIR/lambda/rust"

cleanup_temp_dir() {
    if [[ -n "${TEMP_DIR:-}" && -d "$TEMP_DIR" ]]; then
        find "$TEMP_DIR" -type f -delete 2>/dev/null || true
        find "$TEMP_DIR" -depth -type d -empty -delete 2>/dev/null || true
        rmdir "$TEMP_DIR" 2>/dev/null || true
    fi
}
trap cleanup_temp_dir EXIT

echo -e "${BOLD}Lambda IR Parity Test${RESET}"
echo "============================================"
echo "OCaml bsc: $OCAML_BSC"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo "Rust:      $RESCRIPT_CLI (in-process build dumps)"
    echo "Rust target: $RUST_TARGET"
else
    echo "Rust:      (not available)"
fi
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
if [[ "$STDLIB_MODE" == "true" ]]; then
    echo "Stdlib project: $STDLIB_PROJECT"
fi
if $TEST_RAW; then
    echo "Testing: unoptimized lambda (-drawlambda)"
elif $TEST_LOCS; then
    echo "Testing: sexp-locs (-dlambda-sexp-locs)"
else
    echo "Testing: optimized lambda sexp (-dlambda-sexp)"
fi
echo "Artifact cache: $CACHE_DIR/lambda"
echo ""

DUMP_KIND="lambda"
if [[ "$TEST_RAW" == "true" ]]; then
    DUMP_KIND="rawlambda"
elif [[ "$TEST_LOCS" == "true" ]]; then
    DUMP_KIND="lambda-locs"
fi
RUST_DUMP_DIR="$CACHE_DIR/lambda/rust-dumps"

echo -e "${BOLD}Step 1: Building with the Rust compiler (in process, --dump $DUMP_KIND)...${RESET}"
if ! parity_build_rust_dumps "$BUILD_DIR" "$RUST_DUMP_DIR" "$DUMP_KIND" 2>&1 | tail -5; then
    echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
fi
echo -e "${BOLD}Step 2: Building the OCaml reference...${RESET}"
if ! parity_build_ocaml_reference "$BUILD_DIR" 2>&1 | tail -5; then
    echo -e "${YELLOW}Warning: Some files may have failed to build${RESET}"
fi
TEST_PACKAGE_NAME=$(parity_package_name "$TEST_PROJECT")
cd "$PROJECT_ROOT"
echo ""

if [[ -n "$FILE_ARG" ]]; then
    if [[ -f "$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        if [[ "$STDLIB_MODE" == "true" ]]; then
            find "$STDLIB_PROJECT" -maxdepth 1 -name "*.res" -type f 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        else
            find tests/tests/src -name "*.res" -type f 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        fi
        if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
            echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
            echo "Hint: Try a pattern like 'Core_' or a full path"
            exit 1
        fi
    fi
elif [[ "$STDLIB_MODE" == "true" ]]; then
    # Interfaces produce no lambda, so lambda parity covers implementation sources only.
    find "$STDLIB_PROJECT" -maxdepth 1 -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
else
    find tests/tests/src -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
fi

TOTAL_FILES=$(wc -l < "$TEMP_DIR/files.txt" | tr -d ' ')

if [[ "$TOTAL_FILES" -eq 1 ]]; then
    echo -e "Testing ${BOLD}1${RESET} file: $(cat "$TEMP_DIR/files.txt")"
else
    echo -e "Found ${BOLD}$TOTAL_FILES${RESET} test files"
fi
echo ""

RESULTS_DIR="$TEMP_DIR/results"
mkdir -p "$RESULTS_DIR" "$TEMP_DIR/work"

export OCAML_BSC RESCRIPT_CLI RUST_DUMP_DIR DUMP_KIND TEST_PACKAGE_NAME TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE RUST_AVAILABLE PROJECT_ROOT RESULTS_DIR TEST_PROJECT CACHE_DIR TEST_LOCS TEST_RAW STDLIB_MODE

test_single_file() {
    local file="$1"
    local safe_name
    safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    local ocaml_pass=0 rust_pass=0 parity_pass=0
    local ocaml_fail=0 rust_fail=0 parity_fail=0
    local rust_timeout=0 rust_crash=0
    local parity_hunks=0

    local file_temp="$TEMP_DIR/work/$safe_name"
    mkdir -p "$file_temp"

    local full_file_path
    if [[ "$file" = /* ]]; then
        full_file_path="$file"
    else
        full_file_path="$PROJECT_ROOT/$file"
    fi

    local rel_path="${full_file_path#$TEST_PROJECT/}"
    local lambda_flag="-dlambda-sexp"
    if [[ "$TEST_RAW" == "true" ]]; then
        lambda_flag="-drawlambda"
    elif [[ "$TEST_LOCS" == "true" ]]; then
        lambda_flag="-dlambda-sexp-locs"
    fi

    local ocaml_cache_base="$CACHE_DIR/lambda/ocaml/$safe_name"
    local rust_cache_base="$CACHE_DIR/lambda/rust/$safe_name"
    local diff_cache="$CACHE_DIR/lambda/diffs/$safe_name.diff"
    rm -f "$ocaml_cache_base.sexp" "$ocaml_cache_base.stderr" "$rust_cache_base.sexp" "$rust_cache_base.stderr" "$diff_cache"

    # The Rust output is the dump of the in-process build (Step 1).
    run_rust_bsc() {
        local dump="$RUST_DUMP_DIR/$TEST_PACKAGE_NAME/$rel_path.$DUMP_KIND"
        if [[ -f "$dump" ]]; then
            cat "$dump" >&2
            rust_pass=1
        else
            echo "no $DUMP_KIND dump: the in-process build did not compile $rel_path" >&2
            rust_crash=1
            rust_fail=1
        fi
    }

    local compiler_args_json
    compiler_args_json=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null) || true

    if [[ -n "$compiler_args_json" ]]; then
        local -a compiler_args=()
        while IFS= read -r arg; do
            compiler_args+=("$arg")
        done < <(
            printf '%s' "$compiler_args_json" | python3 -c 'import json,sys; [print(arg) for arg in json.load(sys.stdin).get("compiler_args", [])]'
        )

        if [[ "${#compiler_args[@]}" -gt 0 ]]; then
            cd "$TEST_PROJECT/lib/bs"
            if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" "$lambda_flag" "${compiler_args[@]}" 2> "$file_temp/ocaml.out" 1>/dev/null; then
                ocaml_pass=1
            else
                ocaml_fail=1
                cp "$file_temp/ocaml.out" "$ocaml_cache_base.stderr" 2>/dev/null || true
            fi

            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                run_rust_bsc "$lambda_flag" "${compiler_args[@]}" 2> "$file_temp/rust.out" 1>/dev/null
                if [[ "$rust_fail" -eq 1 ]]; then
                    cp "$file_temp/rust.out" "$rust_cache_base.stderr" 2>/dev/null || true
                fi
            fi
            cd "$PROJECT_ROOT"
        else
            ocaml_fail=1
            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                rust_fail=1
            fi
        fi
    else
        if timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" "$lambda_flag" "$full_file_path" 2> "$file_temp/ocaml.out" 1>/dev/null; then
            ocaml_pass=1
        else
            ocaml_fail=1
            cp "$file_temp/ocaml.out" "$ocaml_cache_base.stderr" 2>/dev/null || true
        fi

        if [[ "$RUST_AVAILABLE" == "true" ]]; then
            run_rust_bsc "$lambda_flag" "$full_file_path" 2> "$file_temp/rust.out" 1>/dev/null
            if [[ "$rust_fail" -eq 1 ]]; then
                cp "$file_temp/rust.out" "$rust_cache_base.stderr" 2>/dev/null || true
            fi
        fi
    fi

    if [[ "$ocaml_pass" -eq 1 ]]; then
        cp "$file_temp/ocaml.out" "$ocaml_cache_base.sexp" 2>/dev/null || true
    fi
    if [[ "$rust_pass" -eq 1 ]]; then
        cp "$file_temp/rust.out" "$rust_cache_base.sexp" 2>/dev/null || true
    fi

    if [[ "$RUST_AVAILABLE" == "true" && "$ocaml_pass" -eq 1 && "$rust_pass" -eq 1 ]]; then
        if diff -q "$file_temp/ocaml.out" "$file_temp/rust.out" > /dev/null 2>&1; then
            parity_pass=1
        else
            parity_fail=1
            diff -ua "$file_temp/ocaml.out" "$file_temp/rust.out" > "$diff_cache" 2>&1 || true
            if [[ -f "$diff_cache" ]]; then
                parity_hunks=$(grep -c '^@@' "$diff_cache" || true)
            fi
        fi
    fi

    echo "$file:ocaml_pass=$ocaml_pass:ocaml_fail=$ocaml_fail:rust_pass=$rust_pass:rust_fail=$rust_fail:rust_timeout=$rust_timeout:rust_crash=$rust_crash:parity_pass=$parity_pass:parity_fail=$parity_fail:parity_hunks=$parity_hunks" > "$result_file"

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
            else
                echo -e "${RED}FAIL${RESET} [Rust] $file"
            fi

            if [[ "$parity_pass" -eq 1 ]]; then
                echo -e "${GREEN}PASS${RESET} [Parity] $file"
            elif [[ "$parity_fail" -eq 1 ]]; then
                echo -e "${RED}FAIL${RESET} [Parity] $file"
            fi
        fi
    fi

    if [[ "$QUICK_MODE" == "true" && ("$ocaml_fail" -eq 1 || "$rust_fail" -eq 1 || "$parity_fail" -eq 1) ]]; then
        echo -e "${RED}Quick mode: stopping on first failure${RESET}"
        if [[ -f "$diff_cache" ]]; then
            echo -e "\nParity diff:"
            head -50 "$diff_cache"
        elif [[ -f "$ocaml_cache_base.stderr" ]]; then
            echo -e "\nOCaml stderr:"
            head -50 "$ocaml_cache_base.stderr"
        elif [[ -f "$rust_cache_base.stderr" ]]; then
            echo -e "\nRust stderr:"
            head -50 "$rust_cache_base.stderr"
        fi
        exit 1
    fi
}

export -f test_single_file

echo -e "${BOLD}Step 3: Running lambda parity tests...${RESET}"
echo ""
if [[ "$PARALLEL_JOBS" -eq 1 ]]; then
    while IFS= read -r file; do
        test_single_file "$file"
    done < "$TEMP_DIR/files.txt"
else
    cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {}
fi

echo ""
echo -e "${BOLD}Results${RESET}"
echo "========"

OCAML_PASS=0
OCAML_FAIL=0
RUST_PASS=0
RUST_FAIL=0
RUST_TIMEOUTS=0
RUST_CRASHES=0
PARITY_PASS=0
PARITY_FAIL=0
PARITY_HUNKS=0
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

        if echo "$result" | grep -q ":parity_pass=1"; then
            PARITY_PASS=$((PARITY_PASS + 1))
        elif echo "$result" | grep -q ":parity_fail=1"; then
            PARITY_FAIL=$((PARITY_FAIL + 1))
            PARITY_FAILURES="$PARITY_FAILURES  $file\n"
        fi

        hunk_count=$(echo "$result" | sed -n 's/.*:parity_hunks=\([0-9][0-9]*\)$/\1/p')
        if [[ -n "$hunk_count" ]]; then
            PARITY_HUNKS=$((PARITY_HUNKS + hunk_count))
        fi
    fi
done

echo -e "OCaml bsc:    ${GREEN}${OCAML_PASS} passed${RESET}, ${RED}${OCAML_FAIL} failed${RESET}"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo -e "Rust bsc:     ${GREEN}${RUST_PASS} passed${RESET}, ${RED}${RUST_FAIL} failed${RESET}"
    echo -e "Parity:       ${GREEN}${PARITY_PASS} passed${RESET}, ${RED}${PARITY_FAIL} failed${RESET}"
    if [[ "$PARITY_HUNKS" -gt 0 ]]; then
        echo -e "Parity hunks: ${YELLOW}${PARITY_HUNKS}${RESET}"
    fi
else
    echo "Rust bsc:     (not available)"
fi
echo ""

if [[ "$OCAML_FAIL" -gt 0 ]]; then
    echo -e "${YELLOW}OCaml failures:${RESET}"
    printf "%b" "$OCAML_FAILURES"
    echo ""
fi

if [[ "$RUST_AVAILABLE" == "true" && "$RUST_FAILURES" != "" ]]; then
    echo -e "${YELLOW}Rust failures:${RESET}"
    printf "%b" "$RUST_FAILURES"
    echo ""
fi

if [[ "$RUST_TIMEOUTS" -gt 0 ]]; then
    echo -e "${YELLOW}Rust timeouts:${RESET}"
    printf "%b" "$RUST_TIMEOUT_LIST"
    echo ""
fi

if [[ "$RUST_CRASHES" -gt 0 ]]; then
    echo -e "${YELLOW}Rust crashes:${RESET}"
    printf "%b" "$RUST_CRASH_LIST"
    echo ""
fi

if [[ "$PARITY_FAIL" -gt 0 ]]; then
    echo -e "${YELLOW}Parity failures:${RESET}"
    printf "%b" "$PARITY_FAILURES"
    echo ""
    echo "Diff files saved to: $CACHE_DIR/lambda/diffs"
fi

if [[ "$OCAML_FAIL" -gt 0 || ("$RUST_AVAILABLE" == "true" && ("$RUST_FAIL" -gt 0 || "$PARITY_FAIL" -gt 0)) ]]; then
    exit 1
fi

if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo -e "${GREEN}${BOLD}SUCCESS: All ${PARITY_PASS} files have matching lambda IR!${RESET}"
else
    echo -e "${GREEN}${BOLD}SUCCESS: All ${OCAML_PASS} OCaml files compiled.${RESET}"
fi
