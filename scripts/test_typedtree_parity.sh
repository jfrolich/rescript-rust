#!/bin/bash

# Typed Tree Parity Test Suite: Compare typed tree output between OCaml and Rust compilers
#
# Both OCaml and Rust sexp are generated via rewatch (single command each):
#   1. `rescript build --dump-typed-sexp`        → OCaml sexp in lib/ocaml/*.sexp
#   2. `rescript build --dump-typed-sexp --rust`  → Rust sexp in lib/ocaml/*.sexp
# Then we compare the two sets of .sexp files.
#
# Sources tested:
# 1. tests/tests/src/       - Main test project
# 2. ~/dev/tella-fusion     - External corpus (override with TELLA_DIR)
#
# USAGE:
#   ./scripts/test_typedtree_parity.sh [OPTIONS] [FILTER]
#
# OPTIONS:
#   --no-build        Skip the build steps (assume sexp files already exist)
#   -h, --help        Show this help message
#
# FILTER:
#   Optional file path or module name pattern to test a single file.
#   Examples:
#     ./scripts/test_typedtree_parity.sh tests/tests/src/a.res
#     ./scripts/test_typedtree_parity.sh a
#     ./scripts/test_typedtree_parity.sh "Core_*"

set -e

SKIP_BUILD=false
FILTER=""

while [[ $# -gt 0 ]]; do
    case $1 in
        --no-build)
            SKIP_BUILD=true
            shift
            ;;
        -h|--help)
            head -24 "$0" | tail -21
            exit 0
            ;;
        -*)
            echo "Unknown option: $1"
            exit 1
            ;;
        *)
            FILTER="$1"
            shift
            ;;
    esac
done

# Normalize filter: if it's a file path, extract module name
if [[ -n "$FILTER" ]]; then
    # Strip directory and extension (e.g. tests/tests/src/a.res -> a)
    FILTER_MODULE=$(basename "$FILTER" | sed 's/\.\(res\|resi\|ml\|mli\)$//')
fi

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)
DUNE_BIN_DIR="$PROJECT_ROOT/_build/install/default/bin"
OCAML_BSC="$DUNE_BIN_DIR/bsc"
RESCRIPT_CLI="$PROJECT_ROOT/rewatch/target/release/rescript"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"

# External corpus (disabled for now — tella builds hang)
# TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
TELLA_DIR=""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

# Check compilers
if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}"
    exit 1
fi
if [[ ! -x "$RESCRIPT_CLI" ]]; then
    echo -e "${RED}Error: rescript CLI not found at $RESCRIPT_CLI${RESET}"
    exit 1
fi

CACHE_DIR="$PROJECT_ROOT/.parity-cache"
mkdir -p "$CACHE_DIR"
TEMP_DIR="$CACHE_DIR"

echo -e "${BOLD}Typed Tree Parity Test${RESET}"
echo "============================================"
echo "OCaml bsc:    $OCAML_BSC"
echo "Rescript CLI: $RESCRIPT_CLI"
if [[ -n "$FILTER_MODULE" ]]; then
    echo "Filter:       $FILTER_MODULE"
fi

# Build and generate sexp for a project
# Args: project_dir label [extra_env...]
build_project_sexp() {
    local project_dir="$1"
    local label="$2"
    shift 2
    local env_vars=("$@")

    local ocaml_dir="$TEMP_DIR/$label/ocaml"
    local rust_dir="$TEMP_DIR/$label/rust"
    mkdir -p "$ocaml_dir" "$rust_dir"

    cd "$project_dir"

    # Build filter args for rewatch --filter
    local filter_args=()
    if [[ -n "$FILTER_MODULE" ]]; then
        # Convert glob pattern to regex: * -> .*, escape dots
        local regex="${FILTER_MODULE//./\\.}"
        regex="${regex//\*/.*}"
        filter_args=(--filter "^${regex}\\.")
    fi

    if [[ ${#filter_args[@]} -eq 0 ]]; then
        echo "  [$label] Cleaning..."
        env "${env_vars[@]}" RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" clean 2>/dev/null || true

        echo "  [$label] Normal build (produces .cmi/.cmj)..."
        timeout 120 env "${env_vars[@]}" RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build 2>&1 | tail -3 || true
    elif [[ ! -d "$project_dir/lib/ocaml" ]]; then
        echo "  [$label] Normal build (produces .cmi/.cmj, needed for filtered sexp)..."
        timeout 120 env "${env_vars[@]}" RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build 2>&1 | tail -3 || true
    fi

    echo "  [$label] OCaml sexp generation..."
    timeout 120 env "${env_vars[@]}" RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build --dump-typed-sexp "${filter_args[@]}" 2>&1 | tail -3 || true

    # Save OCaml sexp files
    local count=0
    for f in lib/ocaml/*.sexp; do
        [[ -f "$f" ]] || continue
        cp "$f" "$ocaml_dir/"
        count=$((count + 1))
    done
    echo "  [$label] Saved $count OCaml sexp files"

    echo "  [$label] Rust sexp generation..."
    timeout 120 env "${env_vars[@]}" RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build --dump-typed-sexp --rust "${filter_args[@]}" 2>&1 | tail -3 || true

    # Save Rust sexp files
    count=0
    for f in lib/ocaml/*.sexp; do
        [[ -f "$f" ]] || continue
        cp "$f" "$rust_dir/"
        count=$((count + 1))
    done
    echo "  [$label] Saved $count Rust sexp files"

    cd "$PROJECT_ROOT"
}

# Compare sexp files for a project and output results
# Args: label
compare_project_sexp() {
    local label="$1"
    local ocaml_dir="$TEMP_DIR/$label/ocaml"
    local rust_dir="$TEMP_DIR/$label/rust"
    local diff_dir="$TEMP_DIR/$label/diffs"
    mkdir -p "$diff_dir"

    local total=0 ocaml_pass=0 rust_pass=0 parity_pass=0 parity_fail=0
    local ocaml_only=0 rust_only=0 both_fail=0
    local parity_failures="" ocaml_only_files="" rust_only_files=""

    # Collect all unique sexp filenames from both dirs
    local all_modules="$TEMP_DIR/$label/modules.txt"
    { ls "$ocaml_dir" 2>/dev/null; ls "$rust_dir" 2>/dev/null; } | sort -u > "$all_modules"

    while IFS= read -r sexp_file; do
        [[ -n "$sexp_file" ]] || continue
        local module="${sexp_file%.sexp}"

        # Apply filter if set
        if [[ -n "$FILTER_MODULE" ]]; then
            # shellcheck disable=SC2254
            case "$module" in
                $FILTER_MODULE) ;;  # exact or glob match
                *) continue ;;
            esac
        fi

        total=$((total + 1))

        local ocaml_file="$ocaml_dir/$sexp_file"
        local rust_file="$rust_dir/$sexp_file"

        local ocaml_ok=false rust_ok=false
        [[ -s "$ocaml_file" ]] && ocaml_ok=true
        [[ -s "$rust_file" ]] && rust_ok=true

        if $ocaml_ok; then ocaml_pass=$((ocaml_pass + 1)); fi
        if $rust_ok; then rust_pass=$((rust_pass + 1)); fi

        if $ocaml_ok && $rust_ok; then
            # Both produced sexp — compare
            if cmp -s "$ocaml_file" "$rust_file"; then
                parity_pass=$((parity_pass + 1))
            else
                parity_fail=$((parity_fail + 1))
                parity_failures="${parity_failures}  ${module}\n"
                diff -u "$ocaml_file" "$rust_file" > "$diff_dir/${module}.diff" 2>&1 || true
            fi
        elif $ocaml_ok && ! $rust_ok; then
            ocaml_only=$((ocaml_only + 1))
            ocaml_only_files="${ocaml_only_files}  ${module}\n"
        elif ! $ocaml_ok && $rust_ok; then
            rust_only=$((rust_only + 1))
            rust_only_files="${rust_only_files}  ${module}\n"
        else
            both_fail=$((both_fail + 1))
        fi
    done < "$all_modules"

    # Print results
    local parity_pct="-"
    if [[ "$total" -gt 0 ]]; then
        parity_pct=$((100 * parity_pass / total))
    fi

    echo -e "${BOLD}$label ($total modules):${RESET}"
    echo -e "  OCaml type-check: ${GREEN}$ocaml_pass${RESET}   OCaml error: ${RED}$((total - ocaml_pass))${RESET}"
    echo -e "  Rust  type-check: ${GREEN}$rust_pass${RESET}   Rust  error: ${RED}$((total - rust_pass))${RESET}"
    echo -e "  Typecheck parity: ${GREEN}$parity_pass${RESET}/$total (${parity_pct}%)"
    if [[ "$parity_fail" -gt 0 ]]; then
        echo -e "  Parity failures:  ${RED}$parity_fail${RESET}"
    fi
    if [[ "$rust_only" -gt 0 ]]; then
        echo -e "  ${YELLOW}Rust-only pass (OCaml rejects): $rust_only${RESET}"
    fi
    if [[ "$ocaml_only" -gt 0 ]]; then
        echo -e "  ${YELLOW}OCaml-only pass (Rust rejects): $ocaml_only${RESET}"
    fi
    if [[ "$both_fail" -gt 0 ]]; then
        echo -e "  Both fail: $both_fail"
    fi

    # Store results for overall summary
    echo "total=$total ocaml_pass=$ocaml_pass rust_pass=$rust_pass parity_pass=$parity_pass parity_fail=$parity_fail ocaml_only=$ocaml_only rust_only=$rust_only both_fail=$both_fail" > "$TEMP_DIR/$label/summary.txt"
    echo "$parity_failures" > "$TEMP_DIR/$label/parity_failures.txt"
    echo "$ocaml_only_files" > "$TEMP_DIR/$label/ocaml_only.txt"
    echo "$rust_only_files" > "$TEMP_DIR/$label/rust_only.txt"

    # Show parity failure list
    if [[ "$parity_fail" -gt 0 && "$parity_fail" -le 100 ]]; then
        echo -e "  ${YELLOW}Parity failure modules:${RESET}"
        echo -e "$parity_failures"
    fi

    # In single-file mode, show diffs inline
    if [[ -n "$FILTER_MODULE" && "$parity_fail" -gt 0 ]]; then
        for df in "$diff_dir"/*.diff; do
            [[ -f "$df" ]] || continue
            echo -e "${BOLD}--- Diff: $(basename "$df" .diff) ---${RESET}"
            cat "$df"
            echo ""
        done
    fi
}

# Step 1: Build projects and generate sexp
if [[ "$SKIP_BUILD" != "true" ]]; then
    echo ""
    echo -e "${BOLD}Step 1: Building and generating sexp...${RESET}"

    build_project_sexp "$TEST_PROJECT" "tests"

    # Build tella-fusion if present
    if [[ -d "$TELLA_DIR" ]]; then
        # Find rescript.json files with sources (skip empty root, skip node_modules)
        tella_candidates=()
        while IFS= read -r cfg; do
            proj_dir=$(dirname "$cfg")
            has_sources=$(jq -r 'if (.sources | length) > 0 then "1" else "0" end' "$cfg" 2>/dev/null) || has_sources=0
            if [[ "$has_sources" == "1" ]]; then
                tella_candidates+=("$proj_dir")
            fi
        done < <(find "$TELLA_DIR" -name "rescript.json" -not -path "*/node_modules/*" 2>/dev/null | sort)

        # Only build top-level projects (skip nested sub-packages)
        for proj_dir in "${tella_candidates[@]}"; do
            is_nested=false
            for other in "${tella_candidates[@]}"; do
                if [[ "$proj_dir" != "$other" && "$proj_dir" == "$other/packages/"* ]]; then
                    is_nested=true
                    break
                fi
            done
            if [[ "$is_nested" == "true" ]]; then
                echo "  Skipping $proj_dir (nested, built as dependency)"
                continue
            fi

            # Use a safe label derived from the project path
            safe_label=$(echo "${proj_dir#$TELLA_DIR/}" | tr '/' '_')
            build_project_sexp "$proj_dir" "tella_$safe_label" \
                "RESCRIPT_RUNTIME=$TELLA_DIR/node_modules/@rescript/runtime"
        done
    fi
    echo ""

fi

# Step 2: Compare sexp files
echo -e "${BOLD}Step 2: Comparing sexp files...${RESET}"
echo ""

OVERALL_TOTAL=0
OVERALL_OCAML_PASS=0
OVERALL_RUST_PASS=0
OVERALL_PARITY_PASS=0
OVERALL_PARITY_FAIL=0
OVERALL_OCAML_ONLY=0
OVERALL_RUST_ONLY=0
OVERALL_BOTH_FAIL=0

accumulate_results() {
    local label="$1"
    local summary_file="$TEMP_DIR/$label/summary.txt"
    [[ -f "$summary_file" ]] || return

    local total ocaml_pass rust_pass parity_pass parity_fail ocaml_only rust_only both_fail
    eval "$(cat "$summary_file")"

    OVERALL_TOTAL=$((OVERALL_TOTAL + total))
    OVERALL_OCAML_PASS=$((OVERALL_OCAML_PASS + ocaml_pass))
    OVERALL_RUST_PASS=$((OVERALL_RUST_PASS + rust_pass))
    OVERALL_PARITY_PASS=$((OVERALL_PARITY_PASS + parity_pass))
    OVERALL_PARITY_FAIL=$((OVERALL_PARITY_FAIL + parity_fail))
    OVERALL_OCAML_ONLY=$((OVERALL_OCAML_ONLY + ocaml_only))
    OVERALL_RUST_ONLY=$((OVERALL_RUST_ONLY + rust_only))
    OVERALL_BOTH_FAIL=$((OVERALL_BOTH_FAIL + both_fail))
}

# Compare tests/tests
if [[ -d "$TEMP_DIR/tests/ocaml" ]]; then
    compare_project_sexp "tests"
    accumulate_results "tests"
fi

# Compare tella sub-projects
for label_dir in "$TEMP_DIR"/tella_*/; do
    [[ -d "$label_dir/ocaml" ]] || continue
    label=$(basename "$label_dir")
    compare_project_sexp "$label"
    accumulate_results "$label"
done

# Overall summary
echo ""
echo "============================================"
if [[ "$OVERALL_TOTAL" -gt 0 ]]; then
    OVERALL_PCT=$((100 * OVERALL_PARITY_PASS / OVERALL_TOTAL))
    echo -e "${BOLD}Overall ($OVERALL_TOTAL modules):${RESET}"
    echo -e "  OCaml type-check: ${GREEN}$OVERALL_OCAML_PASS${RESET}   OCaml error: ${RED}$((OVERALL_TOTAL - OVERALL_OCAML_PASS))${RESET}"
    echo -e "  Rust  type-check: ${GREEN}$OVERALL_RUST_PASS${RESET}   Rust  error: ${RED}$((OVERALL_TOTAL - OVERALL_RUST_PASS))${RESET}"
    echo -e "  Typecheck parity: ${GREEN}$OVERALL_PARITY_PASS${RESET}/$OVERALL_TOTAL (${OVERALL_PCT}%)"
    if [[ "$OVERALL_PARITY_FAIL" -gt 0 ]]; then
        echo -e "  Parity failures:  ${RED}$OVERALL_PARITY_FAIL${RESET}"
    fi
    if [[ "$OVERALL_RUST_ONLY" -gt 0 ]]; then
        echo -e "  ${YELLOW}Rust-only pass: $OVERALL_RUST_ONLY${RESET}"
    fi
    if [[ "$OVERALL_OCAML_ONLY" -gt 0 ]]; then
        echo -e "  ${YELLOW}OCaml-only pass: $OVERALL_OCAML_ONLY${RESET}"
    fi
    echo "============================================"
    if [[ "$OVERALL_PARITY_PASS" -eq "$OVERALL_TOTAL" ]]; then
        echo -e "${GREEN}${BOLD}SUCCESS: Full parity across all modules!${RESET}"
    fi
else
    echo "No sexp files found to compare."
fi
echo ""
echo "Diffs saved in: $TEMP_DIR/*/diffs/"
