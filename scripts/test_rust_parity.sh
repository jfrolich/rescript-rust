#!/bin/bash

# Rust Compiler Parity Test Suite
# Tests the Rust compiler against the OCaml reference implementation
# Reports which tests failed and overall percentage parity

set -e

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)

# Directories
DUNE_BIN_DIR="$PROJECT_ROOT/_build/install/default/bin"
RUST_DIR="$PROJECT_ROOT/compiler-rust"
RUST_TARGET="${RUST_TARGET:-debug}"
RUST_BSC="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc"
RUST_PARSER="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/res_parser_rust"
OCAML_BSC="$PROJECT_ROOT/packages/@rescript/$("$scriptDir/platform.sh")/bin/bsc.exe"
RESCRIPT_CLI="$PROJECT_ROOT/packages/@rescript/$("$scriptDir/platform.sh")/bin/rescript.exe"
OCAML_PARSER="$DUNE_BIN_DIR/res_parser"
SPICE_PPX="${SPICE_PPX:-$PROJECT_ROOT/node_modules/@jfrolich/ppx-spice/ppx}"
SPICE_TEST_DIR="$PROJECT_ROOT/tests/ppx_spice/src"
INSPECT_SCRIPT="$PROJECT_ROOT/scripts/inspect_binary_ast.py"
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
SKIP_PARSER_AST=false
SKIP_SYNTAX=false
SKIP_JS=false
SKIP_SPICE_PPX=false
VERBOSE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --skip-parser-ast)
            SKIP_PARSER_AST=true
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
        --skip-spice-ppx)
            SKIP_SPICE_PPX=true
            shift
            ;;
        --release)
            RUST_TARGET=release
            RUST_BSC="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc"
            RUST_PARSER="$PROJECT_ROOT/rewatch/target/$RUST_TARGET/res_parser_rust"
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
            echo "  --skip-parser-ast  Skip parser AST parity tests"
            echo "  --skip-syntax      Skip syntax tests"
            echo "  --skip-js          Skip JS compilation snapshot tests"
            echo "  --skip-spice-ppx   Skip spice PPX parity tests"
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

    if [[ ! -x "$OCAML_BSC" ]]; then
        echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
        echo "Run 'make' first to build the OCaml compiler."
        missing=true
    fi

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

    if [[ ! -x "$OCAML_PARSER" ]]; then
        echo -e "${RED}Error: OCaml parser not found at $OCAML_PARSER${RESET}"
        echo "Run 'make' first to build the OCaml parser."
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

find_rescript_project_root() {
    local file_path="$1"
    local current_dir
    current_dir=$(dirname "$file_path")

    while [[ "$current_dir" != "/" && -n "$current_dir" ]]; do
        if [[ -f "$current_dir/rescript.json" || -f "$current_dir/bsconfig.json" ]]; then
            if [[ -d "$current_dir/lib/bs" ]]; then
                echo "$current_dir"
                return 0
            fi
        fi
        current_dir=$(dirname "$current_dir")
    done

    return 1
}

get_compiler_args_json() {
    local project_dir="$1"
    local file_path="$2"

    if [[ ! -x "$RESCRIPT_CLI" || -z "$project_dir" || -z "$file_path" ]]; then
        return 1
    fi

    if [[ "$file_path" != "$project_dir"/* ]]; then
        return 1
    fi

    local rel_path="${file_path#$project_dir/}"
    cd "$project_dir" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null
}

# =============================================================================
# TEST 1: Parser AST Parity
# =============================================================================
run_parser_ast_tests() {
    if $SKIP_PARSER_AST; then
        echo -e "${DIM}Skipping parser AST parity tests${RESET}"
        return
    fi

    print_header "PARSER AST PARITY"

    local pass_count=0
    local fail_count=0
    local ocaml_fail_count=0
    local rust_fail_count=0
    local diff_count=0
    local failed_files=""

    cd "$PROJECT_ROOT/tests"

    # Find all test files from idempotency and printer directories
    find syntax_tests/data/idempotency syntax_tests/data/printer -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/parser_files.txt"
    local file_count=$(wc -l < "$TEMP_DIR/parser_files.txt" | tr -d ' ')

    echo "Testing $file_count files..."

    local file_index=0
    while read -r file; do
        file_index=$((file_index + 1))

        # Progress indicator
        if [[ $((file_index % 100)) -eq 0 ]] && $VERBOSE; then
            echo "  Progress: $file_index / $file_count files..."
        fi

        # Determine if it's an interface file
        local intf_flag=""
        case "$file" in
            *.resi)
                intf_flag="-interface"
                ;;
        esac

        # Run OCaml parser
        local ocaml_output="$TEMP_DIR/ocaml.sexp"
        local ocaml_success=true
        if ! timeout "$TIMEOUT_SECONDS" "$OCAML_PARSER" $intf_flag -print sexp "$file" > "$ocaml_output" 2>/dev/null; then
            ocaml_success=false
            ocaml_fail_count=$((ocaml_fail_count + 1))
        fi

        # Run Rust parser
        local rust_output="$TEMP_DIR/rust.sexp"
        local rust_success=true
        if ! timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" $intf_flag -print sexp "$file" > "$rust_output" 2>/dev/null; then
            rust_success=false
            rust_fail_count=$((rust_fail_count + 1))
            failed_files="$failed_files$file (Rust parse error)\n"
        fi

        # Compare outputs if both succeeded
        if $ocaml_success && $rust_success; then
            if diff -q "$ocaml_output" "$rust_output" > /dev/null 2>&1; then
                pass_count=$((pass_count + 1))
            else
                diff_count=$((diff_count + 1))
                failed_files="$failed_files$file (AST differs)\n"

                # Save diff for inspection
                local safe_name=$(echo "$file" | tr '/' '_')
                diff -u "$ocaml_output" "$rust_output" > "$DIFF_DIR/parser_$safe_name.diff" 2>&1 || true
            fi
        fi

    done < "$TEMP_DIR/parser_files.txt"

    cd "$PROJECT_ROOT"

    # Calculate totals
    local comparable_count=$((pass_count + diff_count))
    fail_count=$((rust_fail_count + diff_count))

    # Report results
    if [[ $comparable_count -gt 0 ]]; then
        local pct=$(python3 -c "print(f'{100 * $pass_count / $comparable_count:.1f}')")
        echo -e "Passed: ${GREEN}$pass_count${RESET}/$comparable_count (${pct}%)"
    else
        echo -e "Passed: ${YELLOW}0/0${RESET} (no comparable files)"
    fi

    if [[ $rust_fail_count -gt 0 ]]; then
        echo -e "Rust parse failures: ${YELLOW}$rust_fail_count${RESET}"
    fi

    if [[ $diff_count -gt 0 ]]; then
        echo -e "AST differences: ${RED}$diff_count${RESET}"
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
    total_tests=$((total_tests + comparable_count))
    total_passed=$((total_passed + pass_count))
    total_failed=$((total_failed + diff_count))
}

# =============================================================================
# TEST 2: Syntax Tests
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

    # Parsing tests with recovery
    find syntax_tests/data/parsing/{errors,infiniteLoops,recovery} -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/syntax_parsing_recovery.txt"

    # Parsing tests without recovery
    find syntax_tests/data/parsing/{grammar,other} -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/syntax_parsing_grammar.txt"

    # Printing tests
    find syntax_tests/data/{printer,conversion} -name "*.res" -o -name "*.resi" -o -name "*.ml" -o -name "*.mli" 2>/dev/null | sort > "$TEMP_DIR/syntax_printer.txt"

    # AST mapping tests
    find syntax_tests/data/ast-mapping -name "*.res" -o -name "*.resi" -o -name "*.ml" -o -name "*.mli" 2>/dev/null | sort > "$TEMP_DIR/syntax_ast_mapping.txt"

    # PPX tests
    find syntax_tests/data/ppx/react -name "*.res" -o -name "*.resi" 2>/dev/null | sort > "$TEMP_DIR/syntax_ppx.txt"

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

    # Process parsing tests without recovery
    while read -r file; do
        local expected=$(exp "$file")
        local actual="$TEMP_DIR/syntax/$(echo "$file" | tr '/' '_').txt"

        # Run parser (may exit non-zero for files with syntax errors, which is expected)
        # Capture exit code without triggering set -e
        local exit_code=0
        timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" -print ml "$file" > "$actual" 2>&1 || exit_code=$?

        if [[ $exit_code -eq 124 ]]; then
            # Timeout
            fail_count=$((fail_count + 1))
            failed_files="$failed_files$file (timeout)\n"
            continue
        fi
        # Compare output regardless of parser exit code (files with syntax errors exit non-zero)
        if diff -q "$expected" "$actual" > /dev/null 2>&1; then
            pass_count=$((pass_count + 1))
        else
            fail_count=$((fail_count + 1))
            failed_files="$failed_files$file (output differs)\n"
            diff -u "$expected" "$actual" > "$DIFF_DIR/syntax_$(echo "$file" | tr '/' '_').diff" 2>&1 || true
        fi
    done < "$TEMP_DIR/syntax_parsing_grammar.txt"

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

    # Process AST mapping tests
    while read -r file; do
        local expected=$(exp "$file")
        local actual="$TEMP_DIR/syntax/$(echo "$file" | tr '/' '_').txt"

        if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" -test-ast-conversion -jsx-version 4 "$file" > "$actual" 2>&1; then
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
    done < "$TEMP_DIR/syntax_ast_mapping.txt"

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
# TEST 3: Spice PPX Parity
# =============================================================================
run_spice_ppx_tests() {
    if $SKIP_SPICE_PPX; then
        echo -e "${DIM}Skipping spice PPX parity tests${RESET}"
        return
    fi

    print_header "SPICE PPX PARITY"

    if [[ ! -x "$SPICE_PPX" ]]; then
        echo -e "${YELLOW}Skipping: spice ppx not found at $SPICE_PPX${RESET}"
        echo -e "${DIM}Set SPICE_PPX to override the ppx path.${RESET}"
        return
    fi

    if [[ ! -d "$SPICE_TEST_DIR" ]]; then
        echo -e "${YELLOW}Skipping: spice tests not found at $SPICE_TEST_DIR${RESET}"
        return
    fi

    local pass_count=0
    local diff_count=0
    local ocaml_error_count=0
    local rust_error_count=0
    local failed_files=""

    local files=()
    while IFS= read -r line; do
        files+=("$line")
    done < <(find "$SPICE_TEST_DIR" -name "*.res" -o -name "*.resi" 2>/dev/null | sort)

    local file_count=${#files[@]}
    if [[ $file_count -eq 0 ]]; then
        echo -e "${YELLOW}No spice tests found${RESET}"
        return
    fi

    local file_index=0
    for file in "${files[@]}"; do
        file_index=$((file_index + 1))

        if [[ $((file_index % 20)) -eq 0 ]] && $VERBOSE; then
            echo "  Progress: $file_index / $file_count files..."
        fi

        local safe_name
        safe_name=$(echo "$file" | tr '/' '_')
        local ocaml_out="$TEMP_DIR/spice_ocaml_${safe_name}.ast"
        local rust_out="$TEMP_DIR/spice_rust_${safe_name}.ast"

        local ocaml_exit=0
        timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -ppx "$SPICE_PPX" -bs-ast "$file" -o "$ocaml_out" > /dev/null 2>&1 || ocaml_exit=$?
        if [[ $ocaml_exit -ne 0 ]]; then
            ocaml_error_count=$((ocaml_error_count + 1))
            failed_files="$failed_files$file (OCaml compile error)\n"
            continue
        fi

        if [[ ! -s "$ocaml_out" ]]; then
            local alt="${ocaml_out%.ast}.iast"
            if [[ -s "$alt" ]]; then
                ocaml_out="$alt"
            else
                ocaml_error_count=$((ocaml_error_count + 1))
                failed_files="$failed_files$file (OCaml output missing)\n"
                continue
            fi
        fi

        local rust_exit=0
        timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-ast "$file" -o "$rust_out" > /dev/null 2>&1 || rust_exit=$?
        if [[ $rust_exit -ne 0 ]]; then
            rust_error_count=$((rust_error_count + 1))
            failed_files="$failed_files$file (Rust compile error)\n"
            continue
        fi

        if [[ ! -s "$rust_out" ]]; then
            local alt="${rust_out%.ast}.iast"
            if [[ -s "$alt" ]]; then
                rust_out="$alt"
            else
                rust_error_count=$((rust_error_count + 1))
                failed_files="$failed_files$file (Rust output missing)\n"
                continue
            fi
        fi

        if python3 - "$INSPECT_SCRIPT" "$ocaml_out" "$rust_out" <<'PY' > /dev/null 2>&1
import importlib.util
import sys

script_path, a_path, b_path = sys.argv[1], sys.argv[2], sys.argv[3]
spec = importlib.util.spec_from_file_location("inspect_binary_ast", script_path)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

ast_a = mod.BinaryAstFile(a_path)
ast_b = mod.BinaryAstFile(b_path)
root_a, dec_a = ast_a.decode_ast()
root_b, dec_b = ast_b.decode_ast()
diffs = mod.compare_value_trees(root_a, root_b, dec_a, dec_b)
sys.exit(1 if diffs else 0)
PY
        then
            pass_count=$((pass_count + 1))
        else
            diff_count=$((diff_count + 1))
            failed_files="$failed_files$file (AST differs)\n"
            python3 "$INSPECT_SCRIPT" compare "$ocaml_out" "$rust_out" > "$DIFF_DIR/spice_${safe_name}.diff" 2>&1 || true
        fi
    done

    local total=$((pass_count + diff_count + ocaml_error_count + rust_error_count))
    if [[ $total -gt 0 ]]; then
        local pct=$(python3 -c "print(f'{100 * $pass_count / $total:.1f}')")
        echo -e "Passed: ${GREEN}$pass_count${RESET}/$total (${pct}%)"
    else
        echo -e "Passed: ${YELLOW}0/0${RESET} (no files)"
    fi

    if [[ $ocaml_error_count -gt 0 ]]; then
        echo -e "OCaml errors: ${RED}$ocaml_error_count${RESET}"
    fi

    if [[ $rust_error_count -gt 0 ]]; then
        echo -e "Rust errors: ${RED}$rust_error_count${RESET}"
    fi

    if [[ $diff_count -gt 0 ]]; then
        echo -e "Output differs: ${YELLOW}$diff_count${RESET}"
    fi

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

    total_tests=$((total_tests + total))
    total_passed=$((total_passed + pass_count))
    total_failed=$((total_failed + ocaml_error_count + rust_error_count + diff_count))
}

# =============================================================================
# TEST 4: JS Compilation Snapshots
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

        # Create output directory.
        #
        # For project-owned compiler-args runs we compile checked-in `.ast`
        # files from `<project>/lib/bs` with `-bs-package-output ...:src:...`.
        # Pointing `-o` at another temp directory literally named `src`
        # causes some modules (for example `Import.res`) to skip creating the
        # requested output file even though compilation succeeds. Keep the
        # output basename identical to the snapshot, but place it under a
        # neutral per-file directory so the harness measures the emitted JS
        # instead of a package-output path collision.
        local safe_output_dir
        safe_output_dir=$(echo "$res_file" | tr '/:' '__')
        local output_dir="$TEMP_DIR/js/generated/$safe_output_dir"
        mkdir -p "$output_dir"

        # Compile with Rust bsc
        local expected_ext="${expected_file##*.}"
        local output_name="$(basename "${expected_file}")"
        local actual_mjs="$output_dir/$output_name"
        local compile_output="$TEMP_DIR/js/compile_output.txt"

        local project_dir=""
        local compiler_args_json=""
        local -a compiler_args=()

        project_dir=$(find_rescript_project_root "$full_res_file") || project_dir=""
        if [[ -n "$project_dir" ]]; then
            compiler_args_json=$(get_compiler_args_json "$project_dir" "$full_res_file") || compiler_args_json=""
        fi

        if [[ -n "$compiler_args_json" ]]; then
            while IFS= read -r arg; do
                compiler_args+=("$arg")
            done < <(
                printf '%s' "$compiler_args_json" | python3 -c 'import json, os, sys
args = json.load(sys.stdin).get("compiler_args", [])
runtime = os.environ.get("RESCRIPT_RUNTIME")
i = 0
while i < len(args):
    if args[i] == "-runtime-path" and i + 1 < len(args) and runtime:
        print(args[i])
        print(runtime)
        i += 2
    else:
        print(args[i])
        i += 1'
            )
        fi

        # Prefer the owning project's compiler-args so snapshot compilation
        # runs with the same include paths, package output, JSX, and warnings
        # as the checked-in build. Fall back to standalone compilation only
        # when compiler-args metadata is unavailable.
        local compile_ok=false
        if [[ "${#compiler_args[@]}" -gt 0 && -d "$project_dir/lib/bs" ]]; then
            if (
                cd "$project_dir/lib/bs" &&
                timeout "$TIMEOUT_SECONDS" "$RUST_BSC" "${compiler_args[@]}" -o "$actual_mjs"
            ) > "$compile_output" 2>&1; then
                compile_ok=true
            fi
        elif [[ "$expected_ext" == "mjs" ]]; then
            if timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-package-name rescript-tests -bs-module-type esmodule "$res_file" -o "$actual_mjs" > "$compile_output" 2>&1; then
                compile_ok=true
            fi
        else
            if timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -bs-package-name rescript-tests "$res_file" -o "$actual_mjs" > "$compile_output" 2>&1; then
                compile_ok=true
            fi
        fi
        if $compile_ok; then
            # Check if output file was created
            if [[ -f "$actual_mjs" ]]; then
                if diff -q "$expected_file" "$actual_mjs" > /dev/null 2>&1; then
                    pass_count=$((pass_count + 1))
                else
                    diff_count=$((diff_count + 1))
                    failed_files="$failed_files$res_file (output differs)\n"
                    diff -u "$expected_file" "$actual_mjs" > "$DIFF_DIR/js_$(echo "$res_file" | tr '/' '_').diff" 2>&1 || true
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
echo "OCaml bsc:    $OCAML_BSC"
echo "Rust bsc:     $RUST_BSC"
echo "Rust parser:  $RUST_PARSER"
echo "Rust target:  $RUST_TARGET"
echo "OCaml parser: $OCAML_PARSER"
echo "Timeout:      ${TIMEOUT_SECONDS}s per file"
echo ""

check_prerequisites
setup_temp_dir

run_parser_ast_tests
run_syntax_tests
run_spice_ppx_tests
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
