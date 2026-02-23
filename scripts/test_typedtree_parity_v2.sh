#!/bin/bash

# Typed Tree Parity Test Suite: Compare typed tree output between OCaml and Rust compilers
#
# Tests performed:
# 1. typed-sexp parity - Typed tree structure matches between OCaml and Rust
# 2. error parity - When both compilers fail, error output matches
#
# Sources tested:
# 1. tests/tests/src/       - Main test project (built with rewatch, compiler-args)
# 2. syntax_tests/data/     - Parser test files (standalone compilation, skip if both fail)
#    Includes: idempotency, printer, ppx, conversion, ast-mapping, parsing
#    Excludes: errors, recovery, infiniteLoops
# 3. ~/dev/tella-fusion     - External corpus (built with rewatch, override with TELLA_DIR)
#
# Files that don't type-check with both compilers are tracked separately.
#
# USAGE:
#   ./scripts/test_typedtree_parity_v2.sh [OPTIONS] [FILE|PATTERN]
#
# OPTIONS:
#   -q, --quick       Stop on first failure (useful for quick iteration)
#   -j, --parallel N  Run N tests in parallel (default: 16)
#   -v, --verbose     Show progress for each file
#   --no-build        Skip the initial rewatch build (assume already built)
#   --with-locs       Use -dtyped-sexp-locs (with locations) instead of -dtyped-sexp
#   --no-cache        Disable OCaml sexp caching (force fresh compilation)
#   -h, --help        Show this help message
#
# EXAMPLES:
#   # Test a single file (fastest for iteration):
#   ./scripts/test_typedtree_parity_v2.sh tests/tests/src/a.res
#
#   # Test files matching a pattern:
#   ./scripts/test_typedtree_parity_v2.sh "Core_Array"
#
#   # Run all tests, stop on first failure:
#   ./scripts/test_typedtree_parity_v2.sh --quick
#
#   # Run all tests in parallel (default 16 jobs):
#   ./scripts/test_typedtree_parity_v2.sh

set -e

# Parse command line arguments
QUICK_MODE=false
PARALLEL_JOBS=16
VERBOSE=false
FILE_ARG=""
SKIP_BUILD=false
WITH_LOCS=false
NO_CACHE=false

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
        --no-cache)
            NO_CACHE=true
            shift
            ;;
        -h|--help)
            head -40 "$0" | tail -35
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
RESCRIPT_CLI="$PROJECT_ROOT/packages/@rescript/darwin-arm64/bin/rescript.exe"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
GENERATED_OUTPUT_SCOPE="tests/tests/src"

# External corpus
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"

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

# OCaml sexp cache
CACHE_DIR="$PROJECT_ROOT/.cache/parity"
if [[ "$NO_CACHE" != "true" ]]; then
    mkdir -p "$CACHE_DIR"
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

echo -e "${BOLD}Typed Tree Parity Test${RESET}"
echo "============================================"
echo "OCaml bsc: $OCAML_BSC"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo "Rust bsc:  $RUST_BSC"
else
    echo "Rust bsc:  (not available)"
fi
echo "Sexp flag: $SEXP_FLAG"
echo "Timeout: ${TIMEOUT_SECONDS}s"
echo "Parallel jobs: $PARALLEL_JOBS"
if [[ "$NO_CACHE" == "true" ]]; then
    echo "OCaml cache: disabled"
else
    echo "OCaml cache: $CACHE_DIR"
fi
if [[ -d "$TELLA_DIR" ]]; then
    echo "Tella dir: $TELLA_DIR"
else
    echo "Tella dir: (not found)"
fi
echo ""

# Step 1: Build with rewatch to ensure all dependencies are compiled
if [[ "$SKIP_BUILD" != "true" ]]; then
    echo -e "${BOLD}Step 1: Building test projects with rewatch...${RESET}"

    # Build tests/tests
    echo "  Building tests/tests..."
    cd "$TEST_PROJECT"
    RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" clean 2>/dev/null || true
    if ! RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build 2>&1 | tail -5; then
        echo -e "${YELLOW}Warning: Some test files may have failed to build${RESET}"
    fi
    cd "$PROJECT_ROOT"

    # Build tella-fusion sub-projects if present
    TELLA_AVAILABLE=false
    TELLA_PROJECTS=""
    if [[ -d "$TELLA_DIR" ]]; then
        echo "  Finding tella-fusion sub-projects..."
        # Find rescript.json files with actual sources (skip empty root configs, skip node_modules)
        while IFS= read -r cfg; do
            proj_dir=$(dirname "$cfg")
            has_sources=$(jq -r 'if (.sources | length) > 0 then "1" else "0" end' "$cfg" 2>/dev/null) || has_sources=0
            if [[ "$has_sources" == "1" ]]; then
                echo "    Building $proj_dir..."
                cd "$proj_dir"
                if timeout 300 env RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build 2>&1 | tail -3; then
                    TELLA_PROJECTS="${TELLA_PROJECTS}${proj_dir}"$'\n'
                    TELLA_AVAILABLE=true
                else
                    echo -e "${YELLOW}    Warning: build failed for $proj_dir${RESET}"
                fi
                cd "$PROJECT_ROOT"
            fi
        done < <(find "$TELLA_DIR" -name "rescript.json" -not -path "*/node_modules/*" 2>/dev/null | sort)
        if [[ "$TELLA_AVAILABLE" != "true" ]]; then
            echo -e "${YELLOW}Warning: No tella-fusion sub-projects built successfully${RESET}"
        fi
    fi
    echo ""
else
    # When skipping build, detect pre-built tella sub-projects (including node_modules deps)
    TELLA_AVAILABLE=false
    TELLA_PROJECTS=""
    if [[ -d "$TELLA_DIR" ]]; then
        # Find rescript.json and bsconfig.json (older packages use bsconfig.json)
        while IFS= read -r cfg; do
            proj_dir=$(dirname "$cfg")
            if [[ -d "$proj_dir/lib/ocaml" ]]; then
                has_sources=$(jq -r 'if (.sources | length) > 0 then "1" else "0" end' "$cfg" 2>/dev/null) || has_sources=0
                if [[ "$has_sources" == "1" ]]; then
                    TELLA_PROJECTS="${TELLA_PROJECTS}${proj_dir}"$'\n'
                    TELLA_AVAILABLE=true
                fi
            fi
        done < <(find "$TELLA_DIR" \( -name "rescript.json" -o -name "bsconfig.json" \) 2>/dev/null | sort -u)
    fi
fi

# Pre-compute compiler args per project (avoids per-file subprocess calls)
TEST_BASE_ARGS=""
if [[ -d "$TEST_PROJECT/lib/bs" ]]; then
    TEST_BASE_ARGS=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args src/a.res 2>/dev/null \
        | jq -r '.compiler_args[:-1] | join(" ")' 2>/dev/null) || TEST_BASE_ARGS=""
fi

# Pre-compute tella project args (stored in files keyed by project path hash)
TELLA_ARGS_DIR="$TEMP_DIR/tella_args"
mkdir -p "$TELLA_ARGS_DIR"
if [[ "$TELLA_AVAILABLE" == "true" ]]; then
    while IFS= read -r proj; do
        [[ -z "$proj" ]] && continue
        # Find any .res file to get base args
        first_file=$(find "$proj/src" -name "*.res" -type f 2>/dev/null | head -1)
        if [[ -n "$first_file" ]]; then
            rel_path="${first_file#$proj/}"
            tella_args=$(cd "$proj" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null \
                | jq -r '.compiler_args[:-1] | join(" ")' 2>/dev/null) || tella_args=""
            if [[ -n "$tella_args" ]]; then
                safe_proj=$(echo "$proj" | tr '/' '_')
                echo "$tella_args" > "$TELLA_ARGS_DIR/$safe_proj"
            fi
        fi
    done <<< "$TELLA_PROJECTS"
fi

# Find test files based on arguments
cd "$PROJECT_ROOT"

if [[ -n "$FILE_ARG" ]]; then
    # Check if it's an absolute or relative path to a single file
    if [[ -f "$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    elif [[ -f "$PROJECT_ROOT/$FILE_ARG" ]]; then
        echo "$FILE_ARG" > "$TEMP_DIR/files.txt"
    else
        # Treat as a pattern - search across all source groups
        {
            find tests/tests/src -name "*.res" 2>/dev/null
            find tests/syntax_tests/data/idempotency tests/syntax_tests/data/printer \
                tests/syntax_tests/data/ppx tests/syntax_tests/data/conversion \
                tests/syntax_tests/data/ast-mapping tests/syntax_tests/data/parsing \
                \( -name "*.res" -o -name "*.resi" \) \
                -not -path "*/errors/*" -not -path "*/recovery/*" \
                -not -path "*/infiniteLoops/*" 2>/dev/null || true
            if [[ "$TELLA_AVAILABLE" == "true" ]]; then
                find "$TELLA_DIR" \
                    -type d \( -name .git -o -name target -o -name .next -o -name _build \
                    -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
                    -o -type f \( -name "*.res" -o -name "*.resi" \) -print 2>/dev/null || true
            fi
        } | grep -E "$FILE_ARG" | sort > "$TEMP_DIR/files.txt" || true
        if [[ ! -s "$TEMP_DIR/files.txt" ]]; then
            echo -e "${RED}Error: No files found matching '$FILE_ARG'${RESET}"
            echo "Hint: Try a pattern like 'Core_Array' or a full path"
            exit 1
        fi
    fi
else
    # Find all test files from all source groups
    {
        # Group 1: tests/tests/src (project-based)
        find tests/tests/src -name "*.res" -type f 2>/dev/null

        # Group 2: syntax_tests/data (standalone compilation)
        find tests/syntax_tests/data/idempotency tests/syntax_tests/data/printer \
            tests/syntax_tests/data/ppx tests/syntax_tests/data/conversion \
            tests/syntax_tests/data/ast-mapping tests/syntax_tests/data/parsing \
            \( -name "*.res" -o -name "*.resi" \) \
            -not -path "*/errors/*" -not -path "*/recovery/*" \
            -not -path "*/infiniteLoops/*" 2>/dev/null || true

        # Group 3: tella-fusion (project-based, if available)
        if [[ "$TELLA_AVAILABLE" == "true" ]]; then
            find "$TELLA_DIR" \
                -type d \( -name .git -o -name target -o -name .next -o -name _build \
                -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
                -o -type f \( -name "*.res" -o -name "*.resi" \) -print 2>/dev/null || true
        fi
    } | sort -u > "$TEMP_DIR/files.txt"
fi

# Filter out lib/bs and lib/ocaml duplicates
grep -Ev '(^|/)lib/(bs|ocaml)(/|$)' "$TEMP_DIR/files.txt" > "$TEMP_DIR/files.filtered.txt" || true
mv "$TEMP_DIR/files.filtered.txt" "$TEMP_DIR/files.txt"

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
export OCAML_BSC RUST_BSC RESCRIPT_CLI TIMEOUT_SECONDS TEMP_DIR QUICK_MODE VERBOSE RUST_AVAILABLE PROJECT_ROOT RESULTS_DIR TEST_PROJECT TELLA_DIR TELLA_AVAILABLE TELLA_PROJECTS SEXP_FLAG
export NO_CACHE CACHE_DIR TEST_BASE_ARGS TELLA_ARGS_DIR

# Function to test a single file - writes results to a file
test_single_file() {
    local file="$1"
    local safe_name=$(echo "$file" | tr '/' '_')
    local result_file="$RESULTS_DIR/$safe_name.result"

    # Initialize result
    local ocaml_pass=0 rust_pass=0 parity_pass=0
    local ocaml_fail=0 rust_fail=0 parity_fail=0
    local error_parity_pass=0 error_parity_fail=0
    local rust_only_pass=0 ocaml_only_pass=0

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

    # Determine source group and project root
    local project_root=""
    local source_group="standalone"
    if [[ "$full_file_path" == "$TEST_PROJECT/"* ]]; then
        project_root="$TEST_PROJECT"
        source_group="tests"
    elif [[ "$TELLA_AVAILABLE" == "true" && -n "$TELLA_DIR" && "$full_file_path" == "$TELLA_DIR/"* ]]; then
        source_group="tella"
        # Find the best matching sub-project root (longest prefix match)
        while IFS= read -r proj; do
            [[ -z "$proj" ]] && continue
            if [[ "$full_file_path" == "$proj/"* ]]; then
                if [[ -z "$project_root" || "${#proj}" -gt "${#project_root}" ]]; then
                    project_root="$proj"
                fi
            fi
        done <<< "$TELLA_PROJECTS"
    fi

    # Compute cache key for OCaml sexp
    local cache_key="" cache_file=""
    if [[ "$NO_CACHE" != "true" ]]; then
        local hash_source=""
        if [[ -n "$project_root" ]]; then
            # For project files, hash the .ast file (lives flat in lib/ocaml/)
            local basename="${full_file_path##*/}"
            local ext="${basename##*.}"
            local ast_file
            if [[ "$ext" == "resi" ]]; then
                ast_file="$project_root/lib/ocaml/${basename%.resi}.iast"
            else
                ast_file="$project_root/lib/ocaml/${basename%.res}.ast"
            fi
            if [[ -f "$ast_file" ]]; then
                hash_source="$ast_file"
            fi
        else
            # For standalone files, hash the source file
            hash_source="$full_file_path"
        fi
        if [[ -n "$hash_source" && -f "$hash_source" ]]; then
            # Include sexp flag in cache key so -dtyped-sexp and -dtyped-sexp-locs don't collide
            cache_key=$(cat "$hash_source" | md5 -q 2>/dev/null) || cache_key=""
            if [[ -n "$cache_key" ]]; then
                cache_file="$CACHE_DIR/${SEXP_FLAG#-d}_${cache_key}.sexp"
            fi
        fi
    fi

    # Check OCaml cache
    local ocaml_cached=false
    if [[ -n "$cache_file" && -f "$cache_file" ]]; then
        cp "$cache_file" "$file_temp/ocaml.sexp"
        ocaml_cached=true
        # No raw_stderr available from cache — create empty placeholder
        touch "$file_temp/ocaml.raw_stderr"
    fi

    if [[ -n "$project_root" ]]; then
        # Project-based compilation: use cached base args
        local base_args=""
        if [[ "$source_group" == "tests" ]]; then
            base_args="$TEST_BASE_ARGS"
        elif [[ "$source_group" == "tella" ]]; then
            local safe_proj=$(echo "$project_root" | tr '/' '_')
            if [[ -f "$TELLA_ARGS_DIR/$safe_proj" ]]; then
                base_args=$(cat "$TELLA_ARGS_DIR/$safe_proj")
            fi
        fi

        if [[ -n "$base_args" ]]; then
            # Derive .ast path from source path
            local rel_path="${full_file_path#$project_root/}"
            local ext="${rel_path##*.}"
            local ast_arg
            if [[ "$ext" == "resi" ]]; then
                ast_arg="${rel_path%.resi}.iast"
            else
                ast_arg="${rel_path%.res}.ast"
            fi
            local args="$base_args $ast_arg"

            cd "$project_root/lib/bs"
            if [[ "$ocaml_cached" != "true" ]]; then
                if [[ "$RUST_AVAILABLE" == "true" ]]; then
                    # Run OCaml and Rust in parallel
                    timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $args 2> "$file_temp/ocaml.sexp" 1>/dev/null &
                    local ocaml_pid=$!
                    timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $args 2> "$file_temp/rust.sexp" 1>/dev/null || true
                    wait $ocaml_pid 2>/dev/null || true
                else
                    timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $args 2> "$file_temp/ocaml.sexp" 1>/dev/null || true
                fi
            else
                # OCaml cached, only run Rust
                if [[ "$RUST_AVAILABLE" == "true" ]]; then
                    timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $args 2> "$file_temp/rust.sexp" 1>/dev/null || true
                fi
            fi
            cd "$PROJECT_ROOT"
        else
            # Fallback: call compiler-args per file (shouldn't normally happen)
            local rel_path="${full_file_path#$project_root/}"
            local compiler_args_json
            compiler_args_json=$(cd "$project_root" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null) || true

            if [[ -z "$compiler_args_json" ]]; then
                local include_flags=""
                if [[ -d "$project_root/lib/ocaml" ]]; then
                    include_flags="-I $project_root/lib/ocaml"
                fi
                if [[ "$ocaml_cached" != "true" ]]; then
                    timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $include_flags -o "$file_temp/ocaml_fallback.js" "$full_file_path" 2> "$file_temp/ocaml.sexp" 1>/dev/null || true
                fi
                if [[ "$RUST_AVAILABLE" == "true" ]]; then
                    timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $include_flags -o "$file_temp/rust_fallback.js" "$full_file_path" 2> "$file_temp/rust.sexp" 1>/dev/null || true
                fi
            else
                local args
                args=$(echo "$compiler_args_json" | jq -r '.compiler_args | join(" ")' 2>/dev/null) || args=""

                if [[ -n "$args" ]]; then
                    cd "$project_root/lib/bs"
                    if [[ "$ocaml_cached" != "true" ]]; then
                        timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $args 2> "$file_temp/ocaml.sexp" 1>/dev/null || true
                    fi
                    if [[ "$RUST_AVAILABLE" == "true" ]]; then
                        timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $args 2> "$file_temp/rust.sexp" 1>/dev/null || true
                    fi
                    cd "$PROJECT_ROOT"
                fi
            fi
        fi
    else
        # Standalone compilation (syntax_tests files)
        # Use tests/tests lib/ocaml for include paths (provides stdlib, Belt, React, etc.)
        local include_flags=""
        if [[ -d "$TEST_PROJECT/lib/ocaml" ]]; then
            include_flags="-I $TEST_PROJECT/lib/ocaml"
        fi
        if [[ "$ocaml_cached" != "true" ]]; then
            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                # Run OCaml and Rust in parallel
                timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $include_flags -o "$file_temp/ocaml_standalone.js" "$full_file_path" 2> "$file_temp/ocaml.sexp" 1>/dev/null &
                local ocaml_pid=$!
                timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $include_flags -o "$file_temp/rust_standalone.js" "$full_file_path" 2> "$file_temp/rust.sexp" 1>/dev/null || true
                wait $ocaml_pid 2>/dev/null || true
            else
                timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" $SEXP_FLAG $include_flags -o "$file_temp/ocaml_standalone.js" "$full_file_path" 2> "$file_temp/ocaml.sexp" 1>/dev/null || true
            fi
        else
            # OCaml cached, only run Rust
            if [[ "$RUST_AVAILABLE" == "true" ]]; then
                timeout "$TIMEOUT_SECONDS" "$RUST_BSC" $SEXP_FLAG $include_flags -o "$file_temp/rust_standalone.js" "$full_file_path" 2> "$file_temp/rust.sexp" 1>/dev/null || true
            fi
        fi
    fi

    # Save raw stderr before stripping (for error comparison)
    if [[ "$ocaml_cached" != "true" ]]; then
        [[ -f "$file_temp/ocaml.sexp" ]] && cp "$file_temp/ocaml.sexp" "$file_temp/ocaml.raw_stderr"
    fi
    [[ -f "$file_temp/rust.sexp" ]] && cp "$file_temp/rust.sexp" "$file_temp/rust.raw_stderr"

    # Strip warning messages from sexp output (OCaml emits warnings to stderr mixed with sexp)
    # Warnings appear before "(structure"/"(signature" and after the sexp closing ")"
    # The sexp itself never contains blank lines, so delete from first blank line to end
    if [[ "$ocaml_cached" != "true" && -f "$file_temp/ocaml.sexp" ]]; then
        LC_ALL=C sed -E -n '/^\(structure|^\(signature/,$p' "$file_temp/ocaml.sexp" | LC_ALL=C sed '/^$/,$d' > "$file_temp/ocaml_clean.sexp"
        mv "$file_temp/ocaml_clean.sexp" "$file_temp/ocaml.sexp"
        # Store cleaned output in cache
        if [[ -n "$cache_file" && -s "$file_temp/ocaml.sexp" ]]; then
            cp "$file_temp/ocaml.sexp" "$cache_file"
        fi
    fi
    if [[ -f "$file_temp/rust.sexp" ]]; then
        LC_ALL=C sed -E -n '/^\(structure|^\(signature/,$p' "$file_temp/rust.sexp" | LC_ALL=C sed '/^$/,$d' > "$file_temp/rust_clean.sexp"
        mv "$file_temp/rust_clean.sexp" "$file_temp/rust.sexp"
    fi

    # Determine pass/fail based on whether sexp output was actually produced,
    # not exit code (compilers exit non-zero for warnings but still produce sexp)
    if [[ -s "$file_temp/ocaml.sexp" ]]; then
        ocaml_pass=1
        ocaml_fail=0
    else
        ocaml_pass=0
        ocaml_fail=1
    fi
    if [[ -s "$file_temp/rust.sexp" ]]; then
        rust_pass=1
        rust_fail=0
    else
        rust_pass=0
        rust_fail=1
    fi

    if [[ "$RUST_AVAILABLE" == "true" ]]; then
        if [[ "$ocaml_pass" -eq 1 && "$rust_pass" -eq 1 ]]; then
            # Both succeeded - compare typed tree output
            LC_ALL=C tr -cd '[:print:]\n' < "$file_temp/ocaml.sexp" > "$file_temp/ocaml_text.sexp" 2>/dev/null || cp "$file_temp/ocaml.sexp" "$file_temp/ocaml_text.sexp"
            LC_ALL=C tr -cd '[:print:]\n' < "$file_temp/rust.sexp" > "$file_temp/rust_text.sexp" 2>/dev/null || cp "$file_temp/rust.sexp" "$file_temp/rust_text.sexp"
            if diff -q "$file_temp/ocaml_text.sexp" "$file_temp/rust_text.sexp" > /dev/null 2>&1; then
                parity_pass=1
            else
                parity_fail=1
                diff -u "$file_temp/ocaml_text.sexp" "$file_temp/rust_text.sexp" > "$TEMP_DIR/diffs/$safe_name.diff" 2>&1 || true
            fi
        elif [[ "$ocaml_fail" -eq 1 && "$rust_fail" -eq 1 ]]; then
            # Both failed - compare error output (strip ANSI codes for comparison)
            LC_ALL=C sed 's/\x1b\[[0-9;]*m//g' "$file_temp/ocaml.raw_stderr" > "$file_temp/ocaml.errors" 2>/dev/null || true
            LC_ALL=C sed 's/\x1b\[[0-9;]*m//g' "$file_temp/rust.raw_stderr" > "$file_temp/rust.errors" 2>/dev/null || true
            if diff -q "$file_temp/ocaml.errors" "$file_temp/rust.errors" > /dev/null 2>&1; then
                error_parity_pass=1
            else
                error_parity_fail=1
                diff -u "$file_temp/ocaml.errors" "$file_temp/rust.errors" > "$TEMP_DIR/diffs/$safe_name.error_diff" 2>&1 || true
            fi
        elif [[ "$ocaml_fail" -eq 1 && "$rust_pass" -eq 1 ]]; then
            # OCaml rejects but Rust compiles - Rust is too lenient
            rust_only_pass=1
        elif [[ "$ocaml_pass" -eq 1 && "$rust_fail" -eq 1 ]]; then
            # OCaml compiles but Rust fails - Rust is too strict
            ocaml_only_pass=1
        fi
    fi

    # Write result (include source group for per-group reporting)
    echo "$file:ocaml_pass=$ocaml_pass:ocaml_fail=$ocaml_fail:rust_pass=$rust_pass:rust_fail=$rust_fail:parity_pass=$parity_pass:parity_fail=$parity_fail:error_parity_pass=$error_parity_pass:error_parity_fail=$error_parity_fail:rust_only_pass=$rust_only_pass:ocaml_only_pass=$ocaml_only_pass:group=$source_group" > "$result_file"

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

    # Quick mode - exit on parity failure (skip compile failures from standalone files)
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
echo -e "${BOLD}Step 2: Running typed tree parity tests...${RESET}"
echo ""
if [[ "$PARALLEL_JOBS" -eq 1 ]]; then
    while IFS= read -r file; do
        test_single_file "$file"
    done < "$TEMP_DIR/files.txt"
else
    cat "$TEMP_DIR/files.txt" | xargs -P "$PARALLEL_JOBS" -I {} bash -c 'test_single_file "$@"' _ {}
fi

# Aggregate results using awk (single pass over all result files)
echo ""
echo -e "${BOLD}Results${RESET}"
echo "========"

AGG_FILE="$TEMP_DIR/aggregated.sh"
cat "$RESULTS_DIR"/*.result 2>/dev/null | awk -F: '
{
    file = $1
    # Parse key=value pairs
    delete v
    for (i = 2; i <= NF; i++) {
        n = split($i, kv, "=")
        if (n == 2) v[kv[1]] = kv[2]
    }
    group = v["group"]

    # Global counters
    G["OCAML_PASS"] += v["ocaml_pass"]
    G["OCAML_FAIL"] += v["ocaml_fail"]
    G["RUST_PASS"] += v["rust_pass"]
    G["RUST_FAIL"] += v["rust_fail"]
    G["PARITY_PASS"] += v["parity_pass"]
    G["PARITY_FAIL"] += v["parity_fail"]
    G["ERROR_PARITY_PASS"] += v["error_parity_pass"]
    G["ERROR_PARITY_FAIL"] += v["error_parity_fail"]
    G["RUST_ONLY_PASS"] += v["rust_only_pass"]
    G["OCAML_ONLY_PASS"] += v["ocaml_only_pass"]
    if (v["ocaml_fail"] == 1 && v["rust_fail"] == 1 && v["error_parity_pass"] == 0 && v["error_parity_fail"] == 0)
        G["BOTH_SKIP"]++

    # Failure lists
    if (v["parity_fail"] == 1) parity_failures = parity_failures "  " file "\n"
    if (v["error_parity_fail"] == 1) err_parity_failures = err_parity_failures "  " file "\n"
    if (v["rust_only_pass"] == 1) rust_only_files = rust_only_files "  " file "\n"
    if (v["ocaml_only_pass"] == 1) ocaml_only_files = ocaml_only_files "  " file "\n"

    # Per-group prefix
    if (group == "tests") p = "TESTS_"
    else if (group == "standalone") p = "SYNTAX_"
    else if (group == "tella") p = "TELLA_"
    else p = "SYNTAX_"

    GRP[p "OCAML_PASS"] += v["ocaml_pass"]
    GRP[p "OCAML_FAIL"] += v["ocaml_fail"]
    GRP[p "RUST_PASS"] += v["rust_pass"]
    GRP[p "RUST_FAIL"] += v["rust_fail"]
    GRP[p "PARITY_PASS"] += v["parity_pass"]
    GRP[p "PARITY_FAIL"] += v["parity_fail"]
    GRP[p "ERROR_PARITY_PASS"] += v["error_parity_pass"]
    GRP[p "ERROR_PARITY_FAIL"] += v["error_parity_fail"]
    GRP[p "RUST_ONLY_PASS"] += v["rust_only_pass"]
    GRP[p "OCAML_ONLY_PASS"] += v["ocaml_only_pass"]
    if (p == "SYNTAX_" && v["ocaml_fail"] == 1 && v["rust_fail"] == 1 && v["error_parity_pass"] == 0 && v["error_parity_fail"] == 0)
        GRP["SYNTAX_BOTH_SKIP"]++
}
END {
    # Output shell variable assignments
    for (k in G) printf "%s=%d\n", k, G[k]+0
    for (k in GRP) printf "%s=%d\n", k, GRP[k]+0

    # Output failure lists (use printf to preserve \n)
    printf "PARITY_FAILURES=\"%s\"\n", parity_failures
    printf "ERROR_PARITY_FAILURES=\"%s\"\n", err_parity_failures
    printf "RUST_ONLY_PASS_FILES=\"%s\"\n", rust_only_files
    printf "OCAML_ONLY_PASS_FILES=\"%s\"\n", ocaml_only_files
}
' > "$AGG_FILE"

# Initialize all variables with defaults before sourcing
OCAML_PASS=0 OCAML_FAIL=0
RUST_PASS=0 RUST_FAIL=0
PARITY_PASS=0 PARITY_FAIL=0
ERROR_PARITY_PASS=0 ERROR_PARITY_FAIL=0
RUST_ONLY_PASS=0 OCAML_ONLY_PASS=0
BOTH_SKIP=0
PARITY_FAILURES="" ERROR_PARITY_FAILURES=""
RUST_ONLY_PASS_FILES="" OCAML_ONLY_PASS_FILES=""
TESTS_PARITY_PASS=0 TESTS_PARITY_FAIL=0
TESTS_ERROR_PARITY_PASS=0 TESTS_ERROR_PARITY_FAIL=0
TESTS_RUST_ONLY_PASS=0 TESTS_OCAML_ONLY_PASS=0
TESTS_OCAML_PASS=0 TESTS_OCAML_FAIL=0
TESTS_RUST_PASS=0 TESTS_RUST_FAIL=0
SYNTAX_PARITY_PASS=0 SYNTAX_PARITY_FAIL=0
SYNTAX_ERROR_PARITY_PASS=0 SYNTAX_ERROR_PARITY_FAIL=0
SYNTAX_RUST_ONLY_PASS=0 SYNTAX_OCAML_ONLY_PASS=0
SYNTAX_OCAML_PASS=0 SYNTAX_OCAML_FAIL=0
SYNTAX_RUST_PASS=0 SYNTAX_RUST_FAIL=0
SYNTAX_BOTH_SKIP=0
TELLA_PARITY_PASS=0 TELLA_PARITY_FAIL=0
TELLA_ERROR_PARITY_PASS=0 TELLA_ERROR_PARITY_FAIL=0
TELLA_RUST_ONLY_PASS=0 TELLA_OCAML_ONLY_PASS=0
TELLA_OCAML_PASS=0 TELLA_OCAML_FAIL=0
TELLA_RUST_PASS=0 TELLA_RUST_FAIL=0

# Source the aggregated results
source "$AGG_FILE"

BOTH_TYPED=$((PARITY_PASS + PARITY_FAIL))
BOTH_ERRORED=$((ERROR_PARITY_PASS + ERROR_PARITY_FAIL))

# Helper to compute percentage (integer)
pct() { if [[ "$2" -gt 0 ]]; then echo "$((100 * $1 / $2))"; else echo "-"; fi; }

# Display per-group breakdown
display_group() {
    local label="$1" total="$2"
    local g_ocaml_pass="$3" g_ocaml_fail="$4"
    local g_rust_pass="$5" g_rust_fail="$6"
    local g_parity_pass="$7" g_parity_fail="$8"
    local g_err_pass="$9" g_err_fail="${10}"
    local g_rust_only="${11}" g_ocaml_only="${12}"
    [[ "$total" -gt 0 ]] || return 0

    local g_both_typed=$((g_parity_pass + g_parity_fail))
    local g_both_errored=$((g_err_pass + g_err_fail))
    local typed_pct=$(pct "$g_parity_pass" "$g_both_typed")
    local err_pct=$(pct "$g_err_pass" "$g_both_errored")

    echo -e "${BOLD}$label ($total files):${RESET}"
    echo -e "  OCaml type-check: ${GREEN}$g_ocaml_pass${RESET}   OCaml error: ${RED}$g_ocaml_fail${RESET}"
    echo -e "  Rust  type-check: ${GREEN}$g_rust_pass${RESET}   Rust  error: ${RED}$g_rust_fail${RESET}"
    if [[ "$g_both_typed" -gt 0 ]]; then
        echo -e "  Typecheck parity: ${GREEN}$g_parity_pass${RESET}/$g_both_typed (${typed_pct}%)"
    fi
    if [[ "$g_both_errored" -gt 0 ]]; then
        echo -e "  Error parity:     ${GREEN}$g_err_pass${RESET}/$g_both_errored (${err_pct}%)"
    fi
    if [[ "$g_rust_only" -gt 0 ]]; then
        echo -e "  ${YELLOW}Rust-only pass (OCaml rejects): $g_rust_only${RESET}"
    fi
    if [[ "$g_ocaml_only" -gt 0 ]]; then
        echo -e "  ${YELLOW}OCaml-only pass (Rust rejects): $g_ocaml_only${RESET}"
    fi
}

# Per-group sections
TESTS_TOTAL=$((TESTS_OCAML_PASS + TESTS_OCAML_FAIL))
display_group "tests/tests/src" "$TESTS_TOTAL" \
    "$TESTS_OCAML_PASS" "$TESTS_OCAML_FAIL" \
    "$TESTS_RUST_PASS" "$TESTS_RUST_FAIL" \
    "$TESTS_PARITY_PASS" "$TESTS_PARITY_FAIL" \
    "$TESTS_ERROR_PARITY_PASS" "$TESTS_ERROR_PARITY_FAIL" \
    "$TESTS_RUST_ONLY_PASS" "$TESTS_OCAML_ONLY_PASS"

SYNTAX_TOTAL=$((SYNTAX_OCAML_PASS + SYNTAX_OCAML_FAIL))
display_group "syntax_tests" "$SYNTAX_TOTAL" \
    "$SYNTAX_OCAML_PASS" "$SYNTAX_OCAML_FAIL" \
    "$SYNTAX_RUST_PASS" "$SYNTAX_RUST_FAIL" \
    "$SYNTAX_PARITY_PASS" "$SYNTAX_PARITY_FAIL" \
    "$SYNTAX_ERROR_PARITY_PASS" "$SYNTAX_ERROR_PARITY_FAIL" \
    "$SYNTAX_RUST_ONLY_PASS" "$SYNTAX_OCAML_ONLY_PASS"

TELLA_TOTAL=$((TELLA_OCAML_PASS + TELLA_OCAML_FAIL))
display_group "tella-fusion" "$TELLA_TOTAL" \
    "$TELLA_OCAML_PASS" "$TELLA_OCAML_FAIL" \
    "$TELLA_RUST_PASS" "$TELLA_RUST_FAIL" \
    "$TELLA_PARITY_PASS" "$TELLA_PARITY_FAIL" \
    "$TELLA_ERROR_PARITY_PASS" "$TELLA_ERROR_PARITY_FAIL" \
    "$TELLA_RUST_ONLY_PASS" "$TELLA_OCAML_ONLY_PASS"

echo ""

# Overall summary
echo "============================================"
echo -e "${BOLD}Overall ($TOTAL_FILES files):${RESET}"
if [[ "$RUST_AVAILABLE" == "true" ]]; then
    echo -e "  OCaml type-check: ${GREEN}$OCAML_PASS${RESET}   OCaml error: ${RED}$OCAML_FAIL${RESET}"
    echo -e "  Rust  type-check: ${GREEN}$RUST_PASS${RESET}   Rust  error: ${RED}$RUST_FAIL${RESET}"
    if [[ "$BOTH_TYPED" -gt 0 ]]; then
        TYPED_PCT=$(pct "$PARITY_PASS" "$BOTH_TYPED")
        echo -e "  Typecheck parity: ${GREEN}$PARITY_PASS${RESET}/$BOTH_TYPED (${TYPED_PCT}%)"
    fi
    if [[ "$BOTH_ERRORED" -gt 0 ]]; then
        ERR_PCT=$(pct "$ERROR_PARITY_PASS" "$BOTH_ERRORED")
        echo -e "  Error parity:     ${GREEN}$ERROR_PARITY_PASS${RESET}/$BOTH_ERRORED (${ERR_PCT}%)"
    fi
    if [[ "$RUST_ONLY_PASS" -gt 0 ]]; then
        echo -e "  ${YELLOW}Rust-only pass (OCaml rejects): $RUST_ONLY_PASS${RESET}"
    fi
    if [[ "$OCAML_ONLY_PASS" -gt 0 ]]; then
        echo -e "  ${YELLOW}OCaml-only pass (Rust rejects): $OCAML_ONLY_PASS${RESET}"
    fi
    echo "============================================"
    if [[ "$PARITY_FAIL" -eq 0 && "$ERROR_PARITY_FAIL" -eq 0 && "$RUST_ONLY_PASS" -eq 0 && "$OCAML_ONLY_PASS" -eq 0 ]]; then
        echo -e "${GREEN}${BOLD}SUCCESS: Full parity across all files!${RESET}"
    fi
else
    echo -e "  OCaml type-check: ${GREEN}$OCAML_PASS${RESET}   OCaml error: ${RED}$OCAML_FAIL${RESET}"
fi
echo ""

# Show failure file lists (compact)
if [[ "$RUST_AVAILABLE" == "true" && "$PARITY_FAIL" -gt 0 && -n "$PARITY_FAILURES" ]]; then
    echo -e "${YELLOW}Typecheck parity failures ($PARITY_FAIL):${RESET}"
    echo -e "$PARITY_FAILURES"
fi

if [[ "$RUST_AVAILABLE" == "true" && "$ERROR_PARITY_FAIL" -gt 0 && -n "$ERROR_PARITY_FAILURES" ]]; then
    echo -e "${YELLOW}Error parity failures ($ERROR_PARITY_FAIL):${RESET}"
    echo -e "$ERROR_PARITY_FAILURES"
fi

if [[ "$RUST_AVAILABLE" == "true" && "$RUST_ONLY_PASS" -gt 0 && "$RUST_ONLY_PASS" -le 100 && -n "$RUST_ONLY_PASS_FILES" ]]; then
    echo -e "${YELLOW}Rust-only pass files ($RUST_ONLY_PASS):${RESET}"
    echo -e "$RUST_ONLY_PASS_FILES"
fi

if [[ "$RUST_AVAILABLE" == "true" && "$OCAML_ONLY_PASS" -gt 0 && "$OCAML_ONLY_PASS" -le 100 && -n "$OCAML_ONLY_PASS_FILES" ]]; then
    echo -e "${YELLOW}OCaml-only pass files ($OCAML_ONLY_PASS):${RESET}"
    echo -e "$OCAML_ONLY_PASS_FILES"
fi

echo -e "Diffs saved in: $TEMP_DIR/diffs/"
