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
PARITY_JOBS="${PARITY_JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)}"

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
  PARITY_JOBS is how many cases run at once; it defaults to the number of
  CPUs, and 1 runs every case and compares it before starting the next.
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
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/rewatch/target/$RUST_TARGET/rescript}"
"$PROJECT_ROOT/scripts/rust_compiler_shims.sh" "$RUST_TARGET"
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
    printf '%s' "${1//[^A-Za-z0-9_.-]/_}"
}

# Set variable $1 to the safe name of $2, without a subshell: the case loops
# call this a few thousand times.
set_safe_name() {
    printf -v "$1" '%s' "${2//[^A-Za-z0-9_.-]/_}"
}

# With PARITY_JOBS above 1 the cases run in two phases. In the `collect`
# phase the case loops queue each case's OCaml and Rust commands as one task
# instead of running them; the tasks then run PARITY_JOBS at a time, each
# case's two commands one after the other as before. In the `compare` phase
# the same loops compare the captured outputs in order, and a command whose
# output was not captured runs then. Packages and interfaces a case needs are
# still prepared serially, in the collect phase, before any task runs.
PHASE=direct
TASK_FILE=""
pending_task=""

# Queue command $2... (capturing into $1 the way run_capture does when $0 is
# `out`, or as run_capture_stderr when it is `err`) for the current case.
queue_capture() {
    local mode="$1" output="$2"
    shift 2
    local command redirect status_file
    printf -v command '%q ' timeout "$TIMEOUT_SECONDS" "$@"
    if [[ "$mode" == "out" ]]; then
        printf -v redirect '> %q 2>&1' "$output"
    else
        printf -v redirect '> %q 2> %q' "$output.stdout" "$output"
    fi
    printf -v status_file '%q' "$output.status"
    pending_task+="$command$redirect; printf '%s\\n' \$? > $status_file; "
}

# End the current case's task in the collect phase.
flush_task() {
    if [[ -n "$pending_task" ]]; then
        printf '%s\0' "$pending_task" >> "$TASK_FILE"
        pending_task=""
    fi
}

run_capture() {
    local output="$1"
    shift
    if [[ "$PHASE" == "collect" ]]; then
        queue_capture out "$output" "$@"
        return 0
    fi
    if [[ "$PHASE" == "compare" && -f "$output.status" ]]; then
        return 0
    fi
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
    if [[ "$PHASE" == "collect" ]]; then
        queue_capture err "$output" "$@"
        return 0
    fi
    if [[ "$PHASE" == "compare" && -f "$output.status" ]]; then
        return 0
    fi
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
built_packages=" "

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
    if [[ "$PHASE" == "collect" ]]; then
        flush_task
        return 0
    fi
    read -r ocaml_status < "$ocaml_out.status" || true
    read -r rust_status < "$rust_out.status" || true

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

# A case compiled against a fixture package passes `-I <package>/lib/rescript`.
# The OCaml compiler reads that package's compiled files, so build it once
# with the OCaml compiler (`rescript build-reference`); `rescript bsc` compiles
# the package in memory itself.
prebuild_ocaml_packages() {
    local previous="" flag package prep_out
    for flag in "$@"; do
        if [[ "$previous" == "-I" && "$flag" == tests/error_output_parity/*/lib/rescript ]]; then
            package=${flag%/lib/rescript}
            if [[ "$built_packages" != *" $package "* ]]; then
                prep_out="$CACHE_DIR/compiler/$(safe_name "prebuild_${package}").out"
                if ! RESCRIPT_RUNTIME="$PROJECT_ROOT/packages/@rescript/runtime" \
                    "$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" "$package" > "$prep_out" 2>&1; then
                    echo -e "${RED}Failed to build fixture package with OCaml:${RESET} $package"
                    cat "$prep_out"
                    return 1
                fi
                built_packages="$built_packages$package "
            fi
        fi
        previous="$flag"
    done
}

# A case under the cache directory is a copy of the same-named case (and its
# interface) in tests/error_output_parity/compiler/cases. With `-bs-read-cmi`
# the OCaml compiler reads the interface's .cmi, so compile the interface with
# it first; `rescript bsc -bs-read-cmi` types the interface itself.
prepare_cached_case() {
    local source_file="$1"
    shift
    local name interface flag read_cmi=false
    name=$(basename "$source_file" .res)
    cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/$name.res" "$source_file"
    interface="${source_file}i"
    if [[ -f "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/$name.resi" ]]; then
        cp "$PROJECT_ROOT/tests/error_output_parity/compiler/cases/$name.resi" "$interface"
    fi
    for flag in "$@"; do
        [[ "$flag" == "-bs-read-cmi" ]] && read_cmi=true
    done
    if [[ "$read_cmi" == "true" && -f "$interface" ]]; then
        rm -f "${source_file%.res}.cmi"
        if ! timeout "$TIMEOUT_SECONDS" "$OCAML_BSC" -w -A -color never "$interface" \
            > "$CACHE_DIR/compiler/$(safe_name "prebuild_${interface}").out" 2>&1; then
            echo -e "${RED}Failed to compile the interface with OCaml:${RESET} $interface"
            return 1
        fi
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
        set_safe_name safe "parser_${number}_${source_file}"
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

# res_parser prints the JSX warnings raised before a JSX error, then exits
# with the uncaught error (status 2). Each fixture has a known exit status
# (`name:status`), which both parsers must return before their output is
# compared, so a timeout (124), a missing or unexecutable parser (126, 127), a
# signal, or a wrong status shared by both sides fails. At status 2 the last
# stderr line is the error, whose OCaml text (`Fatal error: exception ...`)
# Rust does not imitate; everything before it, the warnings with their
# locations, must match OCaml, and stdout must be empty. At status 0 stderr
# must match exactly.
JSX_PARSER_WARNING_FIXTURES=(
    jsx_warning_then_error.res:2
    jsx_error_then_warning.res:2
    jsx_with_props_payload_warning.res:0
    jsx_signature_warning_then_error.resi:2
    jsx_signature_error_then_warning.resi:2
    jsx_signature_with_props_payload_warning.resi:0
)

run_jsx_parser_warning_cases() {
    echo -e "${BOLD}res_parser JSX warnings before errors${RESET}"
    local entry name expected source_file safe ocaml_out rust_out diff_out ocaml_status rust_status
    for entry in "${JSX_PARSER_WARNING_FIXTURES[@]}"; do
        name=${entry%:*}
        expected=${entry##*:}
        source_file="tests/error_output_parity/compiler/fixtures/$name"
        if [[ -n "$FILE_ARG" && "$source_file" != *"$FILE_ARG"* ]]; then
            continue
        fi
        safe=$(safe_name "jsx_parser_${name}")
        ocaml_out="$CACHE_DIR/parser/ocaml_${safe}.out"
        rust_out="$CACHE_DIR/parser/rust_${safe}.out"
        diff_out="$CACHE_DIR/diffs/${safe}.diff"
        run_capture_stderr "$ocaml_out" "$OCAML_PARSER" -jsx-version 4 "$source_file"
        run_capture_stderr "$rust_out" "$RUST_PARSER" -jsx-version 4 "$source_file"
        ocaml_status=$(cat "$ocaml_out.status")
        rust_status=$(cat "$rust_out.status")
        total=$((total + 1))
        if [[ "$ocaml_status" != "$expected" || "$rust_status" != "$expected" ]]; then
            printf 'Expected exit status %s\nOCaml: %s\nRust:  %s\n' \
                "$expected" "$ocaml_status" "$rust_status" > "$diff_out"
            record_failure "$source_file" \
                "res_parser exit status OCaml $ocaml_status, Rust $rust_status, expected $expected" || return 1
        elif [[ "$expected" == 2 && -s "$rust_out.stdout" ]]; then
            echo "Rust res_parser wrote to stdout at status 2" > "$diff_out"
            record_failure "$source_file" "res_parser stdout not empty" || return 1
        elif [[ "$expected" == 2 ]] && ! diff -u --text <(sed '$d' "$ocaml_out") <(sed '$d' "$rust_out") > "$diff_out" 2>&1; then
            record_failure "$source_file" "res_parser warnings before the error differ" || return 1
        elif [[ "$expected" == 0 ]] && ! diff -u --text "$ocaml_out" "$rust_out" > "$diff_out" 2>&1; then
            record_failure "$source_file" "res_parser stderr differs" || return 1
        else
            rm -f "$diff_out"
            pass=$((pass + 1))
        fi
    done
}

run_compiler_case() {
    local source_file="$1"
    shift
    local flags=("$@")
    local safe ocaml_out rust_out diff_out
    set_safe_name safe "compiler_${source_file}"
    ocaml_out="$CACHE_DIR/compiler/ocaml_${safe}.out"
    rust_out="$CACHE_DIR/compiler/rust_${safe}.out"
    diff_out="$CACHE_DIR/diffs/${safe}.diff"

    prebuild_ocaml_packages "${flags[@]}" || return 1
    if [[ "$source_file" == .parity-cache/error-output/compiler/* &&
          ! ( "$PHASE" == "compare" && -f "$ocaml_out.status" ) ]]; then
        prepare_cached_case "$source_file" "${flags[@]}" || return 1
    fi
    run_capture_stderr "$ocaml_out" "$OCAML_BSC" "${flags[@]}" "$source_file"
    run_capture_stderr "$rust_out" "$RUST_BSC" "${flags[@]}" "$source_file"
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

# Run the queued commands of the parser and compiler cases. The JSX warning
# cases are few and check statuses inline, so they always run directly.
if [[ "$PARITY_JOBS" -gt 1 ]]; then
    TASK_FILE="$CACHE_DIR/tasks"
    : > "$TASK_FILE"
    PHASE=collect
    if [[ "$RUN_PARSER" == "true" ]]; then
        run_parser_cases > /dev/null || true
    fi
    if [[ "$RUN_COMPILER" == "true" ]]; then
        run_compiler_cases > /dev/null || true
    fi
    flush_task
    if [[ -s "$TASK_FILE" ]]; then
        xargs -0 -n 1 -P "$PARITY_JOBS" bash -c < "$TASK_FILE" || true
    fi
    rm -f "$TASK_FILE"
    PHASE=compare
fi

if [[ "$RUN_PARSER" == "true" ]]; then
    run_parser_cases || true
    run_jsx_parser_warning_cases || true
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
