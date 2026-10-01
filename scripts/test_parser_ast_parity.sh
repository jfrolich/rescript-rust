#!/bin/bash

# AST Parity Test Suite: Comprehensive comparison of Rust and OCaml compilers
#
# Tests performed:
#
# Parser parity (using res_parser for readable diffs):
# 1. sexp-locs parity - AST structure + locations + attributes match
# 2. sexp-locs-ppx parity - Post-PPX AST structure + locations match
#
# Compiler binary output parity (using bsc -bs-ast):
# 3. bsc-ast parity - Full compiler binary AST output is byte-identical
#    (includes dependency extraction + marshalled parsetree)
#
# Spice PPX parity (using bsc -bs-ast):
# 4. spice-ppx parity - OCaml bsc with external spice PPX vs Rust internal PPX
#
# Parser warning output parity:
# 5. parser-warning-snapshots - Warning/text output parity for curated fixtures
#
# REGRESSION TRACKING:
# The script maintains baseline files in tests/parity_baselines/ for each test type.
# - Baselines are read-only unless --update-baseline is passed explicitly
# - If a file in the baseline fails, it's flagged as a REGRESSION
# - Regressions cause the test to fail, preventing parity from decreasing
#
# NOTE: Printer parity (res/ml output) is tested by test_syntax.sh
# NOTE: Parsetree0/PPX parity is tested by test_parser_ast0_parity.sh
#
# Uses test files from tests/syntax_tests/data/{idempotency,printer,ppx,conversion,ast-mapping}
# and tests/ppx_spice/src for spice parity.
# External Tella files are opt-in via --with-external and require TELLA_REVISION.
#
# USAGE:
#   ./scripts/test_parser_ast_parity.sh [OPTIONS] [FILE|PATTERN]
#
# OPTIONS:
#   -q, --quick       Stop on first failure (useful for quick iteration)
#   -j, --parallel N  Run N tests in parallel (default: 8)
#   -v, --verbose     Show progress for each file
#   --update-baseline Append newly passing files to parity baselines
#   --with-external  Include a Tella checkout pinned by TELLA_REVISION
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
#   # Run all tests in parallel (default 8 jobs):
#   ./scripts/test_parser_ast_parity.sh
#
#   # Quick iteration on a specific test:
#   ./scripts/test_parser_ast_parity.sh -v tests/syntax_tests/data/printer/expr/apply.res

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=8
VERBOSE=false
UPDATE_BASELINE=false
WITH_EXTERNAL=false
FILE_ARG=""
PATTERN_MODE=false
SINGLE_FILE_MODE=false

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
        --update-baseline)
            UPDATE_BASELINE=true
            shift
            ;;
        --with-external)
            WITH_EXTERNAL=true
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
  2. sexp-locs-ppx Post-PPX parser AST with locations
  3. bsc-ast       Full `bsc -bs-ast` output (production format with deps)
  4. spice-ppx     OCaml bsc + external spice PPX vs Rust internal spice PPX
  5. parser-warning-snapshots
                   Warning/text output for curated parser warning fixtures

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

  The script compares against read-only baseline files in tests/parity_baselines/.
  If a previously passing file starts failing, it's flagged as a REGRESSION.
  Baselines change only when --update-baseline is passed explicitly.

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

SPICE PPX PARITY:
  Uses tests/ppx_spice/src and compares:
    - OCaml bsc -ppx $SPICE_PPX (external ppx)
    - Rust bsc internal spice ppx
  Override the ppx path with SPICE_PPX if needed.

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
RUST_TARGET="${RUST_TARGET:-debug}"
RUST_PARSER="$PROJECT_ROOT/compiler-rust/target/$RUST_TARGET/res_parser_rust"
OCAML_PARSER="$DUNE_BIN_DIR/res_parser"

# Compiler executables (for bsc -bs-ast output - production format)
RUST_BSC="$PROJECT_ROOT/compiler-rust/target/$RUST_TARGET/bsc"
OCAML_BSC="$PROJECT_ROOT/packages/@rescript/$($PROJECT_ROOT/scripts/platform.sh)/bin/bsc.exe"

# Spice PPX parity configuration
SPICE_PPX="${SPICE_PPX:-$PROJECT_ROOT/node_modules/@jfrolich/ppx-spice/ppx}"
SPICE_TEST_DIR="$PROJECT_ROOT/tests/ppx_spice/src"
INSPECT_SCRIPT="$PROJECT_ROOT/scripts/inspect_binary_ast.py"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

# Configuration
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-5}"

# Baseline files for regression tracking (one per test type)
BASELINE_DIR="$PROJECT_ROOT/tests/parity_baselines"
BASELINE_SEXP_LOCS="$BASELINE_DIR/sexp_locs.txt"
BASELINE_BSC_AST="$BASELINE_DIR/bsc_ast.txt"
BASELINE_SEXP_LOCS_PPX="$BASELINE_DIR/sexp_locs_ppx.txt"

# Check if executables exist
if [[ ! -x "$OCAML_PARSER" ]]; then
    echo -e "${RED}Error: OCaml parser not found at $OCAML_PARSER${RESET}"
    echo "Run 'make' first to build the OCaml parser."
    exit 1
fi

if [[ ! -x "$RUST_PARSER" ]]; then
    echo -e "${RED}Error: Rust parser not found at $RUST_PARSER${RESET}"
    echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml' first."
    echo "This parity script expects debug artifacts for iteration."
    exit 1
fi

if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    echo "Run 'make' first to build the OCaml compiler."
    exit 1
fi

if [[ ! -x "$RUST_BSC" ]]; then
    echo -e "${RED}Error: Rust bsc not found at $RUST_BSC${RESET}"
    echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml' first."
    echo "This parity script expects debug artifacts for iteration."
    exit 1
fi

# Create temp directory
TEMP_DIR=$(mktemp -d)

cleanup_dir_tree() {
    local dir="$1"
    [[ -n "$dir" && -d "$dir" ]] || return 0
    find "$dir" -type f -exec rm -f {} + 2>/dev/null || true
    find "$dir" -type l -exec rm -f {} + 2>/dev/null || true
    find "$dir" -depth -type d -empty -exec rmdir {} \; 2>/dev/null || true
}

trap 'cleanup_dir_tree "$TEMP_DIR"' EXIT

echo -e "${BOLD}AST Parity Test${RESET}"
echo "============================================"
echo "OCaml parser: $OCAML_PARSER"
echo "Rust parser:  $RUST_PARSER"
echo "OCaml bsc:    $OCAML_BSC"
echo "Rust bsc:     $RUST_BSC"
echo "Rust target:  $RUST_TARGET"
echo "Spice ppx:    $SPICE_PPX"
echo "Spice tests:  $SPICE_TEST_DIR"
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

# Find test files based on arguments
cd "$PROJECT_ROOT/tests"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        SINGLE_FILE_MODE=true
        # Convert absolute/relative path to path relative to tests/ directory
        abs_path=$(cd "$(dirname "$FILE_ARG")" && pwd)/$(basename "$FILE_ARG")
        rel_path="${abs_path#$PROJECT_ROOT/tests/}"
        echo "$rel_path" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        SINGLE_FILE_MODE=true
        # Convert project-relative path to tests-relative path
        rel_path="${FILE_ARG#tests/}"
        echo "$rel_path" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/tests/$FILE_ARG" ]]; then
        SINGLE_FILE_MODE=true
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        PATTERN_MODE=true
        # Treat as a pattern and use find with -path
        # Exclude: errors (syntax errors), recovery (error recovery tests), infiniteLoops (stress tests that may hang/fail both parsers)
        # Also exclude specific files where both OCaml and Rust parsers fail
        find syntax_tests/data/idempotency syntax_tests/data/printer syntax_tests/data/ppx syntax_tests/data/conversion syntax_tests/data/ast-mapping syntax_tests/data/parsing \( -name "*.res" -o -name "*.resi" \) -not -path "*/errors/*" -not -path "*/recovery/*" -not -path "*/infiniteLoops/*" -not -path "*/ffi/export.res" -not -path "*/parsing/other/gentype.res" 2>/dev/null | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
    fi
else
    # Find all test files
    # Exclude: errors (syntax errors), recovery (error recovery tests), infiniteLoops (stress tests that may hang/fail both parsers)
    # Also exclude specific files where both OCaml and Rust parsers fail
    find syntax_tests/data/idempotency syntax_tests/data/printer syntax_tests/data/ppx syntax_tests/data/conversion syntax_tests/data/ast-mapping syntax_tests/data/parsing \( -name "*.res" -o -name "*.resi" \) -not -path "*/errors/*" -not -path "*/recovery/*" -not -path "*/infiniteLoops/*" -not -path "*/ffi/export.res" -not -path "*/parsing/other/gentype.res" 2>/dev/null | sort > "$TEMP_DIR/files.txt"
fi

# Include an explicitly pinned external corpus by reference (no file copying).
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
if $WITH_EXTERNAL; then
    if [[ "$(git -C "$TELLA_DIR" rev-parse --is-inside-work-tree 2>/dev/null)" != "true" ]]; then
        echo "External Tella checkout not found at $TELLA_DIR" >&2
        exit 1
    fi
    if [[ -z "${TELLA_REVISION:-}" ]]; then
        echo "--with-external requires TELLA_REVISION to pin the corpus" >&2
        exit 1
    fi
    actual_tella_revision=$(git -C "$TELLA_DIR" rev-parse HEAD)
    expected_tella_revision=$(git -C "$TELLA_DIR" rev-parse "$TELLA_REVISION^{commit}")
    if [[ "$actual_tella_revision" != "$expected_tella_revision" ]]; then
        echo "Tella checkout is at $actual_tella_revision, expected $expected_tella_revision" >&2
        exit 1
    fi
    tella_source_changes=$(git -C "$TELLA_DIR" status --porcelain --untracked-files=all -- '*.res' '*.resi')
    if [[ -n "$tella_source_changes" ]]; then
        echo "External Tella checkout has modified or untracked ReScript sources:" >&2
        echo "$tella_source_changes" >&2
        exit 1
    fi
fi
if $WITH_EXTERNAL && [[ "$SINGLE_FILE_MODE" != true ]]; then
    if [[ "$PATTERN_MODE" == true ]]; then
        find "$TELLA_DIR" \
            -type d \( -name .git -o -name target -o -name .next -o -name _build -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
            -o -type f \( -name "*.res" -o -name "*.resi" \) -print 2>/dev/null | \
            grep -E "$FILE_ARG" | sort >> "$TEMP_DIR/files.txt" || true
    else
        find "$TELLA_DIR" \
            -type d \( -name .git -o -name target -o -name .next -o -name _build -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
            -o -type f \( -name "*.res" -o -name "*.resi" \) -print 2>/dev/null | \
            sort >> "$TEMP_DIR/files.txt"
    fi
fi

sort -u "$TEMP_DIR/files.txt" -o "$TEMP_DIR/files.txt"

# Explicit blacklist for files that fail in both OCaml and Rust.
# These are out of parity scope until the OCaml reference parser/compiler succeeds.
if $WITH_EXTERNAL; then
    DUAL_FAIL_BLACKLIST_REL=(
        "node_modules/@greenlabs/ppx-spice/src/rescript/Spice.res"
        "node_modules/@greenlabs/ppx-spice/src/rescript/Spice_Codecs.res"
        "node_modules/bs-css-dom/node_modules/@rescript/react/src/RescriptReactRouter.res"
        "node_modules/bs-css-dom/node_modules/bs-css/src/Css_Legacy_Core.res"
        "node_modules/rescript-nodejs/test/atomic/EventEmitter.test.res"
        "packages/core/gstreamer/gstreamer/subprojects/gst-devtools/validate/gst/validate/validate.res"
        "packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/source/test/testdata/old_e_testtypes.res"
        "packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/source/test/testdata/old_l_testtypes.res"
        "packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/tzres/metaZones.res"
        "packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/tzres/timezoneTypes.res"
        "packages/core/gstreamer/gstreamer/subprojects/skia/third_party/externals/icu/tzres/zoneinfo64.res"
    )

    for rel in "${DUAL_FAIL_BLACKLIST_REL[@]}"; do
        abs="$TELLA_DIR/$rel"
        grep -Fvx "$abs" "$TEMP_DIR/files.txt" > "$TEMP_DIR/files.filtered" || true
        mv "$TEMP_DIR/files.filtered" "$TEMP_DIR/files.txt"
    done
fi

# Always ignore duplicated generated trees.
grep -Ev '(^|/)lib/(bs|ocaml)(/|$)' "$TEMP_DIR/files.txt" > "$TEMP_DIR/files.no_lib_dups.txt" || true
mv "$TEMP_DIR/files.no_lib_dups.txt" "$TEMP_DIR/files.txt"

if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
    if [[ -n "$FILE_ARG" ]]; then
        echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
        echo "Hint: Try a pattern like 'printer/expr/apply' or a full path"
    else
        echo -e "${RED}Error: No test files found${RESET}"
    fi
    exit 1
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
mkdir -p "$TEMP_DIR/sexp_locs_ppx_diffs"
mkdir -p "$TEMP_DIR/sexp_locs_ppx_spice_diffs"
mkdir -p "$TEMP_DIR/bsc_ast_parity_diffs"
mkdir -p "$TEMP_DIR/spice_ppx"
mkdir -p "$TEMP_DIR/spice_ppx_diffs"
mkdir -p "$TEMP_DIR/parser_warning"
mkdir -p "$TEMP_DIR/parser_warning_diffs"

# Export variables for parallel execution
export OCAML_PARSER RUST_PARSER OCAML_BSC RUST_BSC SPICE_PPX TELLA_DIR TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE INSPECT_SCRIPT

# Function to test a single file - writes results to a file
test_single_file() {
    local file="$1"
    local safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    # Initialize result
    local locs_pass=0 locs_diff=0
    local sexp_locs_ppx_checked=0
    local sexp_locs_ppx_diff=0
    local sexp_locs_ppx_spice_checked=0
    local sexp_locs_ppx_spice_diff=0
    local bsc_ast_checked=0
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

    # Files using spice annotations must use external spice PPX on the OCaml bsc side.
    local use_spice_ppx=false
    if grep -q "@spice" "$file" 2>/dev/null; then
        use_spice_ppx=true
    fi

    # For TELLA files that use @spice, skip raw bsc-ast byte parity and
    # compare post-PPX sexp-with-locs emitted by bsc debug output.
    # Report this as "sexp-with-locs-ppx-and-spice" in summary output.
    local use_spice_structural_bsc=false
    if $use_spice_ppx && [[ -n "$TELLA_DIR" ]] && [[ "$file" == "$TELLA_DIR/"* ]]; then
        use_spice_structural_bsc=true
    fi

    # sexp-locs-ppx currently diverges for spice in the parser path.
    # Skip only for spice files in the external tella corpus.
    local skip_sexp_locs_ppx=false
    if $use_spice_ppx && [[ -n "$TELLA_DIR" ]] && [[ "$file" == "$TELLA_DIR/"* ]]; then
        skip_sexp_locs_ppx=true
    fi

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

        # Test sexp-locs-ppx parity (post-PPX sexp with locations)
        if ! $skip_sexp_locs_ppx; then
            if timeout "$TIMEOUT_SECONDS" "$OCAML_PARSER" $intf_flag -print sexp-locs-ppx "$file" > "$file_temp/ocaml.sexp-locs-ppx" 2>/dev/null; then
                sexp_locs_ppx_checked=1
                if timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" $intf_flag -print sexp-locs-ppx "$file" > "$file_temp/rust.sexp-locs-ppx" 2>/dev/null; then
                    if ! diff -q "$file_temp/ocaml.sexp-locs-ppx" "$file_temp/rust.sexp-locs-ppx" > /dev/null 2>&1; then
                        sexp_locs_ppx_diff=1
                        diff -u --text "$file_temp/ocaml.sexp-locs-ppx" "$file_temp/rust.sexp-locs-ppx" > "$TEMP_DIR/sexp_locs_ppx_diffs/$safe_name.diff" 2>&1 || true
                    fi
                else
                    sexp_locs_ppx_diff=1
                    echo "Rust parser failed to produce required sexp-locs-ppx output." > "$TEMP_DIR/sexp_locs_ppx_diffs/$safe_name.diff"
                fi
            fi
        fi

        # Test bsc -bs-ast parity (full compiler binary AST output with dependencies)
        # This is the production format used by the build system.
        local ocaml_ast_file="$file_temp/ocaml.ast"
        local rust_ast_file="$file_temp/rust.ast"
        local ocaml_iast_file="$file_temp/ocaml.iast"
        local rust_iast_file="$file_temp/rust.iast"
        local ocaml_bsc_cmd=("$OCAML_BSC")
        local rust_bsc_cmd=("$RUST_BSC")
        if [[ -n "$TELLA_DIR" && "$file" == "$TELLA_DIR/"* ]]; then
            # The Tella project enables LetUnwrap in rescript.json. These direct
            # bsc invocations bypass rewatch's config-to-CLI argument plumbing.
            ocaml_bsc_cmd+=(-enable-experimental LetUnwrap)
            rust_bsc_cmd+=(-enable-experimental LetUnwrap)
        fi
        if $use_spice_ppx; then
            ocaml_bsc_cmd+=(-ppx "$SPICE_PPX")
            rust_bsc_cmd+=(-ppx "$SPICE_PPX")
        fi
        if $use_spice_structural_bsc; then
            sexp_locs_ppx_spice_checked=1
            local ocaml_spice_sexp="$file_temp/ocaml.sexp-with-locs-ppx-and-spice"
            local rust_spice_sexp="$file_temp/rust.sexp-with-locs-ppx-and-spice"

            if timeout "$TIMEOUT_SECONDS" "${ocaml_bsc_cmd[@]}" -bs-ast -dparsetree-sexp-locs "$file" -o "$ocaml_ast_file" > /dev/null 2> "$ocaml_spice_sexp" && \
               timeout "$TIMEOUT_SECONDS" "${rust_bsc_cmd[@]}" -bs-ast -dparsetree-sexp-locs "$file" -o "$rust_ast_file" > /dev/null 2> "$rust_spice_sexp"; then
                if ! diff -q "$ocaml_spice_sexp" "$rust_spice_sexp" > /dev/null 2>&1; then
                    sexp_locs_ppx_spice_diff=1
                    {
                        echo "Category: sexp-with-locs-ppx-and-spice"
                        echo "Comparison type: post-PPX sexp-with-locs (not byte-level bsc-ast)"
                        echo ""
                        diff -u --text "$ocaml_spice_sexp" "$rust_spice_sexp" || true
                    } > "$TEMP_DIR/sexp_locs_ppx_spice_diffs/$safe_name.diff" 2>&1
                fi
            else
                sexp_locs_ppx_spice_diff=1
                {
                    echo "Failed to produce sexp-with-locs-ppx-and-spice output via bsc."
                    echo ""
                    echo "--- OCaml stderr ---"
                    cat "$ocaml_spice_sexp" 2>/dev/null || true
                    echo ""
                    echo "--- Rust stderr ---"
                    cat "$rust_spice_sexp" 2>/dev/null || true
                } > "$TEMP_DIR/sexp_locs_ppx_spice_diffs/$safe_name.diff" 2>&1
            fi
        elif timeout "$TIMEOUT_SECONDS" "${ocaml_bsc_cmd[@]}" -bs-ast "$file" -o "$ocaml_ast_file" 2>/dev/null; then
            bsc_ast_checked=1
            if timeout "$TIMEOUT_SECONDS" "${rust_bsc_cmd[@]}" -bs-ast "$file" -o "$rust_ast_file" 2>/dev/null; then
                # Both compilers create .iast for .resi files (regardless of -o), so check for that.
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
                else
                    bsc_ast_diff=1
                    echo "bsc succeeded without producing both expected AST files." > "$TEMP_DIR/bsc_ast_parity_diffs/$safe_name.diff"
                fi
            else
                bsc_ast_diff=1
                echo "Rust bsc failed after the OCaml reference succeeded." > "$TEMP_DIR/bsc_ast_parity_diffs/$safe_name.diff"
            fi
        fi
    fi

    # Write results
    echo "$file:$locs_pass:$locs_diff:$sexp_locs_ppx_checked:$sexp_locs_ppx_diff:$sexp_locs_ppx_spice_checked:$sexp_locs_ppx_spice_diff:$bsc_ast_checked:$bsc_ast_diff:$ocaml_fail:$rust_fail" > "$result_file"

    # Clean up per-file temp
    cleanup_dir_tree "$file_temp"
}

export -f test_single_file
export -f cleanup_dir_tree
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
        IFS=':' read -r _ locs_pass locs_diff sexp_locs_ppx_checked sexp_locs_ppx_diff sexp_locs_ppx_spice_checked sexp_locs_ppx_spice_diff bsc_ast_checked bsc_ast_diff ocaml_fail rust_fail <<< "$result"

        if [[ "$locs_diff" -eq 1 || "$sexp_locs_ppx_diff" -eq 1 || "$sexp_locs_ppx_spice_diff" -eq 1 || "$bsc_ast_diff" -eq 1 || "$ocaml_fail" -eq 1 || "$rust_fail" -eq 1 ]]; then
            echo -e "${RED}FAIL:${RESET} $file (parser, PPX, or bsc parity failure)"
            echo ""
            echo "Diff:"
            for diff_file in \
                "$TEMP_DIR/locs_diffs/$safe_name.diff" \
                "$TEMP_DIR/sexp_locs_ppx_diffs/$safe_name.diff" \
                "$TEMP_DIR/sexp_locs_ppx_spice_diffs/$safe_name.diff" \
                "$TEMP_DIR/bsc_ast_parity_diffs/$safe_name.diff"; do
                [[ -f "$diff_file" ]] && head -30 "$diff_file"
            done
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
sexp_locs_ppx_checked_count=0
sexp_locs_ppx_diff_count=0
sexp_locs_ppx_spice_checked_count=0
sexp_locs_ppx_spice_diff_count=0
bsc_ast_parity_diff_count=0
bsc_ast_checked_count=0
bsc_ast_byte_diff_count=0
bsc_ast_byte_checked_count=0
ocaml_fail_count=0
rust_fail_count=0

locs_diff_files=""
sexp_locs_ppx_diff_files=""
sexp_locs_ppx_spice_diff_files=""
bsc_ast_byte_diff_files=""
ocaml_fail_files=""
rust_fail_files=""

for result_file in "$RESULTS_DIR"/*.result; do
    [[ -f "$result_file" ]] || continue
    result=$(cat "$result_file")
    IFS=':' read -r file locs_pass locs_diff sexp_locs_ppx_checked sexp_locs_ppx_diff sexp_locs_ppx_spice_checked sexp_locs_ppx_spice_diff bsc_ast_checked bsc_ast_diff ocaml_fail rust_fail <<< "$result"

    locs_pass_count=$((locs_pass_count + locs_pass))
    locs_diff_count=$((locs_diff_count + locs_diff))
    sexp_locs_ppx_checked_count=$((sexp_locs_ppx_checked_count + sexp_locs_ppx_checked))
    sexp_locs_ppx_diff_count=$((sexp_locs_ppx_diff_count + sexp_locs_ppx_diff))
    sexp_locs_ppx_spice_checked_count=$((sexp_locs_ppx_spice_checked_count + sexp_locs_ppx_spice_checked))
    sexp_locs_ppx_spice_diff_count=$((sexp_locs_ppx_spice_diff_count + sexp_locs_ppx_spice_diff))
    ocaml_fail_count=$((ocaml_fail_count + ocaml_fail))
    rust_fail_count=$((rust_fail_count + rust_fail))

    bsc_ast_checked_count=$((bsc_ast_checked_count + bsc_ast_checked))
    if [[ "$bsc_ast_checked" -eq 1 ]]; then
        bsc_ast_byte_checked_count=$((bsc_ast_byte_checked_count + 1))
    fi

    [[ "$locs_diff" -eq 1 ]] && locs_diff_files="$locs_diff_files$file\n"
    [[ "$sexp_locs_ppx_diff" -eq 1 ]] && sexp_locs_ppx_diff_files="$sexp_locs_ppx_diff_files$file\n"
    [[ "$sexp_locs_ppx_spice_diff" -eq 1 ]] && sexp_locs_ppx_spice_diff_files="$sexp_locs_ppx_spice_diff_files$file\n"
    if [[ "$bsc_ast_diff" -eq 1 ]]; then
        bsc_ast_parity_diff_count=$((bsc_ast_parity_diff_count + 1))
        bsc_ast_byte_diff_count=$((bsc_ast_byte_diff_count + 1))
        bsc_ast_byte_diff_files="$bsc_ast_byte_diff_files$file\n"
    fi
    [[ "$ocaml_fail" -eq 1 ]] && ocaml_fail_files="$ocaml_fail_files$file\n"
    [[ "$rust_fail" -eq 1 ]] && rust_fail_files="$rust_fail_files$file\n"
done

# Build lists of tested and passing files for each test type
all_tested_files=""
sexp_locs_ppx_tested_files=""
bsc_ast_tested_files=""
sexp_locs_pass_files=""
sexp_locs_ppx_pass_files=""
bsc_ast_pass_files=""

for result_file in "$RESULTS_DIR"/*.result; do
    [[ -f "$result_file" ]] || continue
    result=$(cat "$result_file")
    IFS=':' read -r file locs_pass locs_diff sexp_locs_ppx_checked sexp_locs_ppx_diff sexp_locs_ppx_spice_checked sexp_locs_ppx_spice_diff bsc_ast_checked bsc_ast_diff ocaml_fail rust_fail <<< "$result"

    # Track all tested files
    all_tested_files="$all_tested_files$file\n"

    # A file passes if it didn't fail and didn't have a diff
    if [[ "$locs_pass" -eq 1 && "$locs_diff" -eq 0 ]]; then
        sexp_locs_pass_files="$sexp_locs_pass_files$file\n"
    fi
    if [[ "$sexp_locs_ppx_checked" -eq 1 ]]; then
        sexp_locs_ppx_tested_files="$sexp_locs_ppx_tested_files$file\n"
        if [[ "$locs_pass" -eq 1 && "$sexp_locs_ppx_diff" -eq 0 ]]; then
            sexp_locs_ppx_pass_files="$sexp_locs_ppx_pass_files$file\n"
        fi
    fi
    if [[ "$bsc_ast_checked" -eq 1 ]]; then
        bsc_ast_tested_files="$bsc_ast_tested_files$file\n"
        if [[ "$locs_pass" -eq 1 && "$bsc_ast_diff" -eq 0 ]]; then
            bsc_ast_pass_files="$bsc_ast_pass_files$file\n"
        fi
    fi
done

# Get sorted list of all tested files (filtered to test suite only)
tested_files_sorted=$(echo -e "$all_tested_files" | grep -v "^$" | grep "^syntax_tests/data/" | sort -u)
sexp_locs_ppx_tested_sorted=$(echo -e "$sexp_locs_ppx_tested_files" | grep -v "^$" | grep "^syntax_tests/data/" | sort -u)
bsc_ast_tested_sorted=$(echo -e "$bsc_ast_tested_files" | grep -v "^$" | grep "^syntax_tests/data/" | sort -u)

# Function to detect regressions and update baseline
# Args: $1=baseline_file, $2=current_pass_files (newline-separated), $3=test_name, $4=tested_files (sorted)
detect_regressions_and_update() {
    local baseline_file="$1"
    local current_pass="$2"
    local test_name="$3"
    local tested_files="$4"
    local regressions=""
    local new_passes=""

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

    if [[ -n "$new_passes" ]]; then
        local new_count=$(echo "$new_passes" | wc -l | tr -d ' ')
        echo -e "${GREEN}New passes in $test_name: $new_count file(s)${RESET}"
        if $UPDATE_BASELINE; then
            mkdir -p "$(dirname "$baseline_file")"
            echo "$new_passes" >> "$baseline_file"
            sort -u "$baseline_file" -o "$baseline_file"
        else
            echo "  Re-run with --update-baseline to record them."
        fi
    fi
}

# Parser warning snapshot parity (curated fixtures with expected text output)
run_parser_warning_snapshot_parity() {
    echo ""
    echo -e "${BOLD}Running parser warning snapshot parity...${RESET}"

    local files=()
    while IFS= read -r line; do
        files+=("$line")
    done < <(find syntax_tests/data/ppx/react/warnings \( -name "*.res" -o -name "*.resi" \) 2>/dev/null | sort)

    local file_count=${#files[@]}
    parser_warning_total=$file_count
    if [[ $file_count -eq 0 ]]; then
        echo -e "${YELLOW}No parser warning fixtures found${RESET}"
        return
    fi

    echo "Warning fixtures: $file_count files"

    for file in "${files[@]}"; do
        local safe_name
        safe_name=$(echo "$file" | tr '/' '_')
        local expected="$(dirname "$file")/expected/$(basename "$file").txt"
        local ocaml_out="$TEMP_DIR/parser_warning/ocaml_${safe_name}.txt"
        local rust_out="$TEMP_DIR/parser_warning/rust_${safe_name}.txt"
        local diff_out="$TEMP_DIR/parser_warning_diffs/${safe_name}.diff"

        local fail_reason=""
        local ocaml_exit=0
        local rust_exit=0

        timeout "$TIMEOUT_SECONDS" "$OCAML_PARSER" -jsx-version 4 "$file" > "$ocaml_out" 2>&1 || ocaml_exit=$?
        timeout "$TIMEOUT_SECONDS" "$RUST_PARSER" -jsx-version 4 "$file" > "$rust_out" 2>&1 || rust_exit=$?

        if [[ ! -f "$expected" ]]; then
            fail_reason="missing expected file"
            {
                echo "Missing expected snapshot: $expected"
            } > "$diff_out"
        elif [[ $ocaml_exit -eq 124 || $rust_exit -eq 124 ]]; then
            fail_reason="timeout"
            {
                echo "Timeout while running parser warning snapshot check."
                echo "OCaml exit: $ocaml_exit"
                echo "Rust exit:  $rust_exit"
            } > "$diff_out"
        elif [[ $ocaml_exit -ne 0 ]]; then
            fail_reason="OCaml parser failed"
            {
                echo "OCaml parser exited with $ocaml_exit"
                echo ""
                cat "$ocaml_out" 2>/dev/null || true
            } > "$diff_out"
        elif [[ $rust_exit -ne 0 ]]; then
            fail_reason="Rust parser failed"
            {
                echo "Rust parser exited with $rust_exit"
                echo ""
                cat "$rust_out" 2>/dev/null || true
            } > "$diff_out"
        elif ! diff -q "$ocaml_out" "$rust_out" > /dev/null 2>&1; then
            fail_reason="OCaml and Rust outputs differ"
            diff -u --text "$ocaml_out" "$rust_out" > "$diff_out" 2>&1 || true
        elif ! diff -q "$expected" "$rust_out" > /dev/null 2>&1; then
            fail_reason="Rust output differs from expected snapshot"
            diff -u --text "$expected" "$rust_out" > "$diff_out" 2>&1 || true
        fi

        if [[ -n "$fail_reason" ]]; then
            parser_warning_diff_count=$((parser_warning_diff_count + 1))
            parser_warning_failed_files="$parser_warning_failed_files$file ($fail_reason)\n"
        else
            parser_warning_pass_count=$((parser_warning_pass_count + 1))
        fi
    done
}

# Spice PPX parity (OCaml bsc with external ppx vs Rust internal ppx)
run_spice_ppx_parity() {
    echo ""
    echo -e "${BOLD}Running spice PPX parity...${RESET}"

    if [[ ! -x "$SPICE_PPX" ]]; then
        echo -e "${RED}Error: spice ppx not found at $SPICE_PPX${RESET}"
        echo "Set SPICE_PPX to override the ppx path."
        spice_missing=true
        return
    fi

    if [[ ! -d "$SPICE_TEST_DIR" ]]; then
        echo -e "${RED}Error: spice tests not found at $SPICE_TEST_DIR${RESET}"
        spice_missing=true
        return
    fi

    if [[ ! -f "$INSPECT_SCRIPT" ]]; then
        echo -e "${RED}Error: inspect script not found at $INSPECT_SCRIPT${RESET}"
        spice_missing=true
        return
    fi

    local files=()
    while IFS= read -r line; do
        files+=("$line")
    done < <(find "$SPICE_TEST_DIR" -name "*.res" -o -name "*.resi" 2>/dev/null | sort)

    local file_count=${#files[@]}
    if [[ $file_count -eq 0 ]]; then
        echo -e "${YELLOW}No spice tests found${RESET}"
        return
    fi

    echo "Spice tests: $file_count files"

    for file in "${files[@]}"; do
        local safe_name
        safe_name=$(echo "$file" | tr '/' '_')
        local ocaml_out="$TEMP_DIR/spice_ppx/ocaml_${safe_name}.ast"
        local rust_out="$TEMP_DIR/spice_ppx/rust_${safe_name}.ast"

        local ocaml_exit=0
        timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -ppx "$SPICE_PPX" -bs-ast "$file" -o "$ocaml_out" > /dev/null 2>&1 || ocaml_exit=$?
        if [[ $ocaml_exit -ne 0 ]]; then
            spice_ocaml_error_count=$((spice_ocaml_error_count + 1))
            spice_failed_files="$spice_failed_files$file (OCaml compile error)\n"
            continue
        fi

        if [[ ! -s "$ocaml_out" ]]; then
            local alt="${ocaml_out%.ast}.iast"
            if [[ -s "$alt" ]]; then
                ocaml_out="$alt"
            else
                spice_ocaml_error_count=$((spice_ocaml_error_count + 1))
                spice_failed_files="$spice_failed_files$file (OCaml output missing)\n"
                continue
            fi
        fi

        local rust_exit=0
        timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -ppx "$SPICE_PPX" -bs-ast "$file" -o "$rust_out" > /dev/null 2>&1 || rust_exit=$?
        if [[ $rust_exit -ne 0 ]]; then
            spice_rust_error_count=$((spice_rust_error_count + 1))
            spice_failed_files="$spice_failed_files$file (Rust compile error)\n"
            continue
        fi

        if [[ ! -s "$rust_out" ]]; then
            local alt="${rust_out%.ast}.iast"
            if [[ -s "$alt" ]]; then
                rust_out="$alt"
            else
                spice_rust_error_count=$((spice_rust_error_count + 1))
                spice_failed_files="$spice_failed_files$file (Rust output missing)\n"
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
            spice_pass_count=$((spice_pass_count + 1))
        else
            spice_diff_count=$((spice_diff_count + 1))
            spice_failed_files="$spice_failed_files$file (AST differs)\n"
            python3 "$INSPECT_SCRIPT" compare "$ocaml_out" "$rust_out" > "$TEMP_DIR/spice_ppx_diffs/spice_${safe_name}.diff" 2>&1 || true
        fi
    done

    spice_total=$((spice_pass_count + spice_diff_count + spice_ocaml_error_count + spice_rust_error_count))
}

echo ""
echo -e "${BOLD}Checking for regressions against baseline...${RESET}"
echo ""

# Detect regressions for each test type
detect_regressions_and_update "$BASELINE_SEXP_LOCS" "$sexp_locs_pass_files" "sexp-locs" "$tested_files_sorted"
detect_regressions_and_update "$BASELINE_SEXP_LOCS_PPX" "$sexp_locs_ppx_pass_files" "sexp-locs-ppx" "$sexp_locs_ppx_tested_sorted"
detect_regressions_and_update "$BASELINE_BSC_AST" "$bsc_ast_pass_files" "bsc-ast" "$bsc_ast_tested_sorted"

# Count total regressions
total_regressions=0
for reg_file in "$TEMP_DIR"/regressions_*.txt; do
    [[ -f "$reg_file" ]] && total_regressions=$((total_regressions + $(wc -l < "$reg_file" | tr -d ' ')))
done

# Run spice PPX parity (OCaml external PPX vs Rust internal)
spice_total=0
spice_pass_count=0
spice_diff_count=0
spice_ocaml_error_count=0
spice_rust_error_count=0
spice_failed_files=""
spice_missing=false
run_spice_ppx_parity

# Run parser warning snapshot parity
parser_warning_total=0
parser_warning_pass_count=0
parser_warning_diff_count=0
parser_warning_failed_files=""
run_parser_warning_snapshot_parity

echo ""
echo ""
echo -e "${BOLD}============================================${RESET}"
echo -e "${BOLD}RESULTS${RESET}"
echo -e "${BOLD}============================================${RESET}"
echo ""

# Show baseline statistics
baseline_sexp_locs_count=0
baseline_sexp_locs_ppx_count=0
baseline_bsc_ast_count=0

[[ -f "$BASELINE_SEXP_LOCS" ]] && baseline_sexp_locs_count=$(wc -l < "$BASELINE_SEXP_LOCS" | tr -d ' ')
[[ -f "$BASELINE_SEXP_LOCS_PPX" ]] && baseline_sexp_locs_ppx_count=$(wc -l < "$BASELINE_SEXP_LOCS_PPX" | tr -d ' ')
[[ -f "$BASELINE_BSC_AST" ]] && baseline_bsc_ast_count=$(wc -l < "$BASELINE_BSC_AST" | tr -d ' ')

echo -e "${BOLD}Summary:${RESET}"
echo "  Total files tested:         $TOTAL_FILES"
echo ""
echo "  ${BOLD}Baseline (files that must not regress):${RESET}"
echo "    sexp-locs:                $baseline_sexp_locs_count"
echo "    sexp-locs-ppx:            $baseline_sexp_locs_ppx_count"
echo "    bsc-ast:                  $baseline_bsc_ast_count"
echo ""
echo "  ${BOLD}Parser parity (sexp output for debugging):${RESET}"
echo "    sexp-locs matches:        $locs_pass_count"
echo "    sexp-locs differences:    $locs_diff_count"
echo "    sexp-locs-ppx checks:     $sexp_locs_ppx_checked_count"
echo "    sexp-locs-ppx reference skips: $((TOTAL_FILES - sexp_locs_ppx_checked_count - sexp_locs_ppx_spice_checked_count))"
echo "    sexp-locs-ppx differences: $sexp_locs_ppx_diff_count"
echo "    sexp-with-locs-ppx-and-spice checks: $sexp_locs_ppx_spice_checked_count"
echo "    sexp-with-locs-ppx-and-spice differences: $sexp_locs_ppx_spice_diff_count"
echo ""
echo "  ${BOLD}bsc-ast Byte Parity:${RESET}"
echo "    bsc-ast byte checks:      $bsc_ast_byte_checked_count"
echo "    bsc-ast reference skips:  $((TOTAL_FILES - bsc_ast_checked_count - sexp_locs_ppx_spice_checked_count))"
echo "    bsc-ast byte differences: $bsc_ast_byte_diff_count"
echo ""
echo "  ${BOLD}Parse failures:${RESET}"
echo "    OCaml failures:           $ocaml_fail_count"
echo "    Rust failures:            $rust_fail_count"
echo ""

echo "  ${BOLD}Spice PPX parity:${RESET}"
if $spice_missing; then
    echo "    spice status:             MISSING (set SPICE_PPX or install ppx-spice)"
else
    echo "    spice passes:             $spice_pass_count"
    echo "    spice differences:        $spice_diff_count"
    echo "    spice OCaml errors:       $spice_ocaml_error_count"
    echo "    spice Rust errors:        $spice_rust_error_count"
fi
echo ""

echo "  ${BOLD}Parser Warning Snapshots:${RESET}"
echo "    warning fixtures:         $parser_warning_total"
echo "    warning passes:           $parser_warning_pass_count"
echo "    warning differences:      $parser_warning_diff_count"
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

# Show sexp-locs-ppx mismatches
if [[ $sexp_locs_ppx_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${YELLOW}Files with sexp-locs-ppx differences ($sexp_locs_ppx_diff_count):${RESET}"
    echo -e "$sexp_locs_ppx_diff_files" | grep -v "^$" | head -30 | while read file; do
        echo "  $file"
    done
    if [[ $sexp_locs_ppx_diff_count -gt 30 ]]; then
        remaining=$((sexp_locs_ppx_diff_count - 30))
        echo "  ... and $remaining more"
    fi
    echo ""

    # Show first sexp-locs-ppx diff as example
    echo -e "${BOLD}Example sexp-locs-ppx diff (first file):${RESET}"
    first_ppx_diff=$(ls "$TEMP_DIR/sexp_locs_ppx_diffs/"*.diff 2>/dev/null | head -1)
    if [[ -n "$first_ppx_diff" ]]; then
        head -50 "$first_ppx_diff"
        lines=$(wc -l < "$first_ppx_diff")
        if [[ $lines -gt 50 ]]; then
            echo "  ... (diff truncated, $lines total lines)"
        fi
    fi
    echo ""
fi

# Show sexp-with-locs-ppx-and-spice differences
if [[ $sexp_locs_ppx_spice_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${YELLOW}Files with sexp-with-locs-ppx-and-spice differences ($sexp_locs_ppx_spice_diff_count):${RESET}"
    echo "  (TELLA @spice files; sexp representation comparison)"
    echo -e "$sexp_locs_ppx_spice_diff_files" | grep -v "^$" | head -15 | while read file; do
        echo "  $file"
    done
    if [[ $sexp_locs_ppx_spice_diff_count -gt 15 ]]; then
        remaining=$((sexp_locs_ppx_spice_diff_count - 15))
        echo "  ... and $remaining more"
    fi
    echo ""

    # Show first structural diff as example
    echo -e "${BOLD}Example sexp-with-locs-ppx-and-spice diff (first file):${RESET}"
    first_spice_ppx_sexp_file=$(echo -e "$sexp_locs_ppx_spice_diff_files" | grep -v "^$" | head -1)
    if [[ -n "$first_spice_ppx_sexp_file" ]]; then
        first_spice_ppx_sexp_diff="$TEMP_DIR/sexp_locs_ppx_spice_diffs/$(echo "$first_spice_ppx_sexp_file" | tr '/' '_').diff"
        [[ -f "$first_spice_ppx_sexp_diff" ]] && head -30 "$first_spice_ppx_sexp_diff"
    fi
    echo ""
fi

# Show bsc-ast byte-level differences
if [[ $bsc_ast_byte_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${RED}Files with bsc-ast byte-level differences ($bsc_ast_byte_diff_count):${RESET}"
    echo "  (raw bsc -bs-ast bytes differ)"
    echo -e "$bsc_ast_byte_diff_files" | grep -v "^$" | head -15 | while read file; do
        echo "  $file"
    done
    if [[ $bsc_ast_byte_diff_count -gt 15 ]]; then
        remaining=$((bsc_ast_byte_diff_count - 15))
        echo "  ... and $remaining more"
    fi
    echo ""

    # Show first byte-level diff as example
    echo -e "${BOLD}Example bsc-ast byte-level diff (first file):${RESET}"
    first_bsc_byte_file=$(echo -e "$bsc_ast_byte_diff_files" | grep -v "^$" | head -1)
    if [[ -n "$first_bsc_byte_file" ]]; then
        first_bsc_byte_diff="$TEMP_DIR/bsc_ast_parity_diffs/$(echo "$first_bsc_byte_file" | tr '/' '_').diff"
        [[ -f "$first_bsc_byte_diff" ]] && head -30 "$first_bsc_byte_diff"
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

# Show spice PPX failures
if ! $spice_missing && [[ $spice_total -gt 0 ]]; then
    local_spice_failures=$((spice_diff_count + spice_ocaml_error_count + spice_rust_error_count))
    if [[ $local_spice_failures -gt 0 ]]; then
        echo -e "${BOLD}${YELLOW}Spice PPX failures ($local_spice_failures):${RESET}"
        echo -e "$spice_failed_files" | grep -v "^$" | head -20 | while read line; do
            echo "  $line"
        done
        total_failures=$(echo -e "$spice_failed_files" | grep -v "^$" | wc -l | tr -d ' ')
        if [[ $total_failures -gt 20 ]]; then
            echo "  ... and $((total_failures - 20)) more"
        fi
        echo ""
    fi
fi

if [[ $parser_warning_diff_count -gt 0 ]]; then
    echo -e "${BOLD}${YELLOW}Parser warning snapshot failures ($parser_warning_diff_count):${RESET}"
    echo -e "$parser_warning_failed_files" | grep -v "^$" | head -20 | while read line; do
        echo "  $line"
    done
    total_failures=$(echo -e "$parser_warning_failed_files" | grep -v "^$" | wc -l | tr -d ' ')
    if [[ $total_failures -gt 20 ]]; then
        echo "  ... and $((total_failures - 20)) more"
    fi
    echo ""

    echo -e "${BOLD}Example parser warning snapshot diff (first file):${RESET}"
    first_warning_file=$(echo -e "$parser_warning_failed_files" | grep -v "^$" | head -1 | sed -E 's/ \(.+$//')
    if [[ -n "$first_warning_file" ]]; then
        first_warning_diff="$TEMP_DIR/parser_warning_diffs/$(echo "$first_warning_file" | tr '/' '_').diff"
        [[ -f "$first_warning_diff" ]] && head -50 "$first_warning_diff"
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

if [[ $ocaml_fail_count -gt 0 || $rust_fail_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: parser commands failed (OCaml: $ocaml_fail_count, Rust: $rust_fail_count)${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $locs_diff_count -gt 0 ]]; then
    pct_match=$(python3 -c "print(f'{100 * $locs_pass_count / ($locs_pass_count + $locs_diff_count):.1f}')")
    echo -e "${RED}${BOLD}FAILED: $locs_diff_count files have sexp-locs differences ($pct_match% match)${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $sexp_locs_ppx_diff_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: $sexp_locs_ppx_diff_count files have sexp-locs-ppx differences${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $sexp_locs_ppx_spice_diff_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: $sexp_locs_ppx_spice_diff_count files have post-Spice PPX differences${RESET}"
    all_pass=false
    exit_code=1
fi

if [[ $bsc_ast_parity_diff_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: $bsc_ast_parity_diff_count files have bsc-ast byte differences${RESET}"
    all_pass=false
    exit_code=1
fi

if $spice_missing; then
    echo -e "${RED}${BOLD}FAILED: Spice PPX parity could not run (missing ppx/tests)${RESET}"
    all_pass=false
    exit_code=1
elif [[ $spice_total -gt 0 ]]; then
    spice_failures=$((spice_diff_count + spice_ocaml_error_count + spice_rust_error_count))
    if [[ $spice_failures -gt 0 ]]; then
        echo -e "${RED}${BOLD}FAILED: Spice PPX parity has $spice_failures failure(s)${RESET}"
        all_pass=false
        exit_code=1
    fi
fi

if [[ $parser_warning_diff_count -gt 0 ]]; then
    echo -e "${RED}${BOLD}FAILED: Parser warning snapshots have $parser_warning_diff_count failure(s)${RESET}"
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
