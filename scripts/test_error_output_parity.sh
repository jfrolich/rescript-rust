#!/bin/bash

# Compare user-facing parser/compiler diagnostics between the OCaml and Rust
# compilers. This is intentionally snapshot-free: OCaml is the oracle, and the
# captured output must match byte-for-byte.

set -euo pipefail

QUICK_MODE=false
VERBOSE=false
RUN_PARSER=true
RUN_COMPILER=true
INCLUDE_SUPER_ERRORS=true
FILE_ARG=""
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10}"

usage() {
    cat <<'EOF'
Compare user-facing parser/compiler diagnostics between the OCaml and Rust
compilers. OCaml is the oracle, and captured output must match byte-for-byte.

USAGE:
  ./scripts/test_error_output_parity.sh [OPTIONS] [FILE|PATTERN]

OPTIONS:
  --release          Use target/release Rust compiler and parser artifacts
  --parser-only       Run parser diagnostics only
  --compiler-only     Run compiler/typechecker diagnostics only
  --no-super-errors   Do not include tests/build_tests/super_errors/fixtures
  -q, --quick         Stop on first mismatch
  -v, --verbose       Print each tested fixture
  -h, --help          Show this help

ENV:
  OCAML_BSC, RUST_BSC, OCAML_PARSER, RUST_PARSER can override binary paths.
  TIMEOUT_SECONDS defaults to 10.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --release)
            RUST_TARGET=release
            shift
            ;;
        --parser-only)
            RUN_PARSER=true
            RUN_COMPILER=false
            shift
            ;;
        --compiler-only)
            RUN_PARSER=false
            RUN_COMPILER=true
            shift
            ;;
        --no-super-errors)
            INCLUDE_SUPER_ERRORS=false
            shift
            ;;
        -q|--quick)
            QUICK_MODE=true
            shift
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        -*)
            echo "Error: unknown option: $1"
            usage
            exit 2
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

RUST_TARGET="${RUST_TARGET:-debug}"
OCAML_BSC="${OCAML_BSC:-$DUNE_BIN_DIR/bsc}"
RUST_BSC="${RUST_BSC:-$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc}"
"$PROJECT_ROOT/scripts/rust_compiler_links.sh" "$RUST_TARGET"
OCAML_PARSER="${OCAML_PARSER:-$DUNE_BIN_DIR/res_parser}"
RUST_PARSER="${RUST_PARSER:-$PROJECT_ROOT/rewatch/target/$RUST_TARGET/res_parser_rust}"

PARSER_MATRIX="$PROJECT_ROOT/tests/syntax_tests/data/parsing/diagnostics_numbers.csv"
COMPILER_CASES_FILE="$PROJECT_ROOT/tests/error_output_parity/compiler/cases.tsv"
COMPILER_FIXTURE_DIR="$PROJECT_ROOT/tests/error_output_parity/compiler/fixtures"
SUPER_ERRORS_DIR="$PROJECT_ROOT/tests/build_tests/super_errors/fixtures"

CACHE_DIR="$PROJECT_ROOT/.parity-cache/error-output"
mkdir -p "$CACHE_DIR/parser" "$CACHE_DIR/compiler" "$CACHE_DIR/diffs"
find "$CACHE_DIR" -type f \( -name '*.out' -o -name '*.stdout' -o -name '*.status' -o -name '*.diff' \) -delete 2>/dev/null || true

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

missing=0
if [[ "$RUN_PARSER" == "true" ]]; then
    for exe in "$OCAML_PARSER" "$RUST_PARSER"; do
        if [[ ! -x "$exe" ]]; then
            echo -e "${RED}Missing parser executable:${RESET} $exe"
            missing=1
        fi
    done
fi
if [[ "$RUN_COMPILER" == "true" ]]; then
    for exe in "$OCAML_BSC" "$RUST_BSC"; do
        if [[ ! -x "$exe" ]]; then
            echo -e "${RED}Missing compiler executable:${RESET} $exe"
            missing=1
        fi
    done
fi
if [[ "$missing" -ne 0 ]]; then
    echo "Build first:"
    echo "  eval \$(opam env --shell=sh) && make lib"
    if [[ "$RUST_TARGET" == "release" ]]; then
        echo "  cargo build --release --manifest-path rewatch/Cargo.toml"
    else
        echo "  cargo build --manifest-path rewatch/Cargo.toml"
    fi
    exit 2
fi

if [[ "$RUN_PARSER" == "true" && ! -f "$PARSER_MATRIX" ]]; then
    echo -e "${RED}Missing parser matrix:${RESET} $PARSER_MATRIX"
    exit 2
fi

cd "$PROJECT_ROOT"

# Compiler cases run from the repository root without -bs-package-output, so
# the default JS output lands in ./src. The package_* cases reach their
# diagnostic only after that write succeeds.
mkdir -p "$PROJECT_ROOT/src"

safe_name() {
    printf '%s' "$1" | tr '/ ' '__' | tr -c 'A-Za-z0-9_.-' '_'
}

run_capture() {
    local output="$1"
    shift
    local status=0
    if timeout "$TIMEOUT_SECONDS" "$@" > "$output" 2>&1; then
        status=0
    else
        status=$?
    fi
    printf '%s\n' "$status" > "$output.status"
}

run_capture_stderr() {
    local output="$1"
    shift
    local status=0
    if timeout "$TIMEOUT_SECONDS" "$@" > "$output.stdout" 2> "$output"; then
        status=0
    else
        status=$?
    fi
    printf '%s\n' "$status" > "$output.status"
}

total=0
pass=0
fail=0
failed_files=""

record_failure() {
    local file="$1"
    local reason="$2"
    fail=$((fail + 1))
    failed_files="$failed_files$file ($reason)\n"
    if [[ "$QUICK_MODE" == "true" ]]; then
        return 1
    fi
    return 0
}

compare_outputs() {
    local kind="$1"
    local label="$2"
    local ocaml_out="$3"
    local rust_out="$4"
    local diff_out="$5"
    local ocaml_status rust_status
    ocaml_status=$(cat "$ocaml_out.status")
    rust_status=$(cat "$rust_out.status")

    total=$((total + 1))
    if [[ "$VERBOSE" == "true" ]]; then
        echo "[$kind] $label"
    fi

    if [[ "$ocaml_status" != "$rust_status" ]]; then
        {
            echo "Exit status differs"
            echo "OCaml: $ocaml_status"
            echo "Rust:  $rust_status"
            echo ""
            echo "--- OCaml output"
            cat "$ocaml_out"
            echo ""
            echo "--- Rust output"
            cat "$rust_out"
        } > "$diff_out"
        record_failure "$label" "exit status differs" || return 1
    elif ! cmp -s "$ocaml_out" "$rust_out"; then
        diff -u --text "$ocaml_out" "$rust_out" > "$diff_out" 2>&1 || true
        record_failure "$label" "output differs" || return 1
    else
        pass=$((pass + 1))
    fi
    return 0
}

prebuild_ocaml_dependency() {
    local source_file="$1"
    shift
    local safe prep_out
    safe=$(safe_name "prebuild_${source_file}")
    prep_out="$CACHE_DIR/compiler/${safe}.out"

    if ! timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" "$@" "$source_file" > "$prep_out.stdout" 2> "$prep_out"; then
        echo -e "${RED}Failed to prepare OCaml dependency:${RESET} $source_file"
        cat "$prep_out"
        return 1
    fi
}

run_parser_cases() {
    echo -e "${BOLD}Parser diagnostics parity${RESET}"
    while IFS=, read -r kind number source_file _expected_file; do
        [[ -z "${kind// }" || "$kind" =~ ^# ]] && continue
        if [[ -n "$FILE_ARG" && "$source_file" != *"$FILE_ARG"* && "$number" != "$FILE_ARG" ]]; then
            continue
        fi

        local safe ocaml_out rust_out diff_out
        safe=$(safe_name "parser_${number}_${source_file}")
        ocaml_out="$CACHE_DIR/parser/ocaml_${safe}.out"
        rust_out="$CACHE_DIR/parser/rust_${safe}.out"
        diff_out="$CACHE_DIR/diffs/${safe}.diff"

        if [[ "$kind" == "warning" ]]; then
            run_capture "$ocaml_out" "$OCAML_PARSER" -jsx-version 4 "$source_file"
            run_capture "$rust_out" "$RUST_PARSER" -jsx-version 4 "$source_file"
        else
            run_capture "$ocaml_out" "$OCAML_PARSER" -jsx-version 4 -recover -print ml "$source_file"
            run_capture "$rust_out" "$RUST_PARSER" -jsx-version 4 -recover -print ml "$source_file"
        fi

        compare_outputs "parser" "$source_file" "$ocaml_out" "$rust_out" "$diff_out" || return 1
    done < "$PARSER_MATRIX"
}

run_compiler_case() {
    local source_file="$1"
    shift
    local flags=("$@")
    local safe ocaml_out rust_out diff_out
    safe=$(safe_name "compiler_${source_file}")
    ocaml_out="$CACHE_DIR/compiler/ocaml_${safe}.out"
    rust_out="$CACHE_DIR/compiler/rust_${safe}.out"
    diff_out="$CACHE_DIR/diffs/${safe}.diff"

    if [[ "$source_file" == "tests/error_output_parity/compiler/cases/gentype_stale_cmti.res" ]]; then
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/Bar.cmi" \
            "$CACHE_DIR/compiler/gentype_stale_cmti.cmti"
    fi

    if [[ "$source_file" == "tests/error_output_parity/compiler/cases/package_script_dependency.res" ]]; then
        prebuild_ocaml_dependency \
            "tests/error_output_parity/compiler/cases/package_script_dependency_dep.res" \
            -w -A -bs-jsx 4 -color never || return 1
    fi

    if [[ "$source_file" == "tests/error_output_parity/compiler/cases/package_missing_ml_dependency.res" ]]; then
        prebuild_ocaml_dependency \
            "tests/error_output_parity/compiler/cases/package_missing_ml_dependency_dep.res" \
            -w -A -bs-jsx 4 -color never \
            -bs-project-root . \
            -bs-package-name dep_pkg \
            -bs-package-output commonjs:.parity-cache/error-output/compiler:.js || return 1
    fi

    if [[ "$source_file" == "tests/error_output_parity/compiler/cases/cmj_not_found.res" ]]; then
        prebuild_ocaml_dependency \
            "tests/error_output_parity/compiler/cases/cmj_not_found_dep.res" \
            -w -A -bs-jsx 4 -color never || return 1
        rm -f tests/error_output_parity/compiler/cases/cmj_not_found_dep.cmj
    fi

    if [[ "$source_file" == "tests/error_output_parity/compiler/cases/js_not_found.res" ]]; then
        prebuild_ocaml_dependency \
            "tests/error_output_parity/compiler/cases/js_not_found_dep.res" \
            -w -A -bs-jsx 4 -color never || return 1
        rm -f tests/error_output_parity/compiler/cases/js_not_found_dep.js
        rm -f tests/error_output_parity/compiler/cases/Js_not_found_dep.js
    fi

    if [[ "$source_file" == ".parity-cache/error-output/compiler/gentype_bad_magic.res" ]]; then
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/gentype_stale_cmti.res" \
            "$CACHE_DIR/compiler/gentype_bad_magic.res"
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/cmi_not_an_interface.cmi" \
            "$CACHE_DIR/compiler/gentype_bad_magic.cmti"
        run_capture "$ocaml_out" "$OCAML_BSC" "${flags[@]}" "$source_file"
        run_capture "$rust_out" "$RUST_BSC" "${flags[@]}" "$source_file"
    elif [[ "$source_file" == ".parity-cache/error-output/compiler/compunit_deprecated_inclusion.res" ]]; then
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/compunit_deprecated_inclusion.res" \
            "$CACHE_DIR/compiler/compunit_deprecated_inclusion.res"
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/compunit_deprecated_inclusion.reference.cmi" \
            "$CACHE_DIR/compiler/compunit_deprecated_inclusion.cmi"
        run_capture_stderr "$ocaml_out" "$OCAML_BSC" "${flags[@]}" "$source_file"
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/compunit_deprecated_inclusion.reference.cmi" \
            "$CACHE_DIR/compiler/compunit_deprecated_inclusion.cmi"
        run_capture_stderr "$rust_out" "$RUST_BSC" "${flags[@]}" "$source_file"
    else
        run_capture_stderr "$ocaml_out" "$OCAML_BSC" "${flags[@]}" "$source_file"
        run_capture_stderr "$rust_out" "$RUST_BSC" "${flags[@]}" "$source_file"
    fi
    compare_outputs "compiler" "$source_file" "$ocaml_out" "$rust_out" "$diff_out"
}

run_compiler_cases() {
    echo -e "${BOLD}Compiler diagnostics parity${RESET}"
    local default_flags=(-w +A -bs-jsx 4 -color never)
    local compiler_cases=0

    if [[ -f "$COMPILER_CASES_FILE" ]]; then
        while IFS=$'\t' read -r source_file flags; do
            [[ -z "${source_file// }" || "$source_file" =~ ^# ]] && continue
            if [[ -n "$FILE_ARG" && "$source_file" != *"$FILE_ARG"* ]]; then
                continue
            fi
            compiler_cases=$((compiler_cases + 1))
            read -r -a extra_flags <<< "${flags:-}"
            if [[ "${#extra_flags[@]}" -eq 0 ]]; then
                run_compiler_case "$source_file" "${default_flags[@]}" || return 1
            else
                run_compiler_case "$source_file" "${extra_flags[@]}" || return 1
            fi
        done < "$COMPILER_CASES_FILE"
    fi

    if [[ -d "$COMPILER_FIXTURE_DIR" ]]; then
        while IFS= read -r source_file; do
            source_file=${source_file#"$PROJECT_ROOT/"}
            if [[ -n "$FILE_ARG" && "$source_file" != *"$FILE_ARG"* ]]; then
                continue
            fi
            compiler_cases=$((compiler_cases + 1))
            run_compiler_case "$source_file" "${default_flags[@]}" || return 1
        done < <(find "$COMPILER_FIXTURE_DIR" -type f \( -name '*.res' -o -name '*.resi' \) | sort)
    fi

    if [[ "$INCLUDE_SUPER_ERRORS" == "true" && -d "$SUPER_ERRORS_DIR" ]]; then
        while IFS= read -r source_file; do
            source_file=${source_file#"$PROJECT_ROOT/"}
            if [[ -n "$FILE_ARG" && "$source_file" != *"$FILE_ARG"* ]]; then
                continue
            fi
            compiler_cases=$((compiler_cases + 1))
            run_compiler_case "$source_file" "${default_flags[@]}" || return 1
        done < <(find "$SUPER_ERRORS_DIR" -type f -name '*.res' | sort)
    fi

    if [[ "$compiler_cases" -eq 0 ]]; then
        echo -e "${YELLOW}No compiler diagnostics fixtures matched.${RESET}"
    fi
}

if [[ "$RUN_PARSER" == "true" ]]; then
    run_parser_cases || true
    if [[ "$QUICK_MODE" == "true" && "$fail" -gt 0 ]]; then
        RUN_COMPILER=false
    fi
fi
if [[ "$RUN_COMPILER" == "true" ]]; then
    run_compiler_cases || true
fi

echo ""
echo -e "${BOLD}Error output parity summary${RESET}"
echo "  total:  $total"
echo -e "  pass:   ${GREEN}$pass${RESET}"
echo -e "  fail:   ${RED}$fail${RESET}"
echo "  cache:  $CACHE_DIR"

if [[ "$fail" -gt 0 ]]; then
    echo ""
    echo -e "${BOLD}${RED}Failures:${RESET}"
    echo -e "$failed_files" | grep -v '^$' | head -30
    first_failed=$(echo -e "$failed_files" | grep -v '^$' | head -1 | sed 's/ (.*$//')
    if [[ -n "$first_failed" ]]; then
        first_diff="$CACHE_DIR/diffs/$(safe_name "compiler_${first_failed}").diff"
        if [[ ! -f "$first_diff" ]]; then
            first_diff="$CACHE_DIR/diffs/$(find "$CACHE_DIR/diffs" -type f -name '*.diff' | sort | head -1 | sed 's#^.*/##')"
        fi
        if [[ -f "$first_diff" ]]; then
            echo ""
            echo -e "${BOLD}First diff:${RESET} $first_diff"
            head -80 "$first_diff"
        fi
    fi
    exit 1
fi

echo -e "${GREEN}SUCCESS: OCaml and Rust diagnostic output match for tested fixtures.${RESET}"
