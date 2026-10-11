#!/usr/bin/env bash

# Compare JavaScript emitted by the OCaml and Rust compilers for a focused
# fixture corpus. OCaml is the oracle; generated JS is kept in .parity-cache
# and is not checked in.

set -euo pipefail

QUICK_MODE=false
VERBOSE=false
FILE_ARG=""
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10}"

usage() {
    cat <<'EOF'
Compare OCaml and Rust emitted JavaScript for focused compiling fixtures.

USAGE:
  ./scripts/test_js_output_parity_fixtures.sh [OPTIONS] [FILE|PATTERN]

OPTIONS:
  --release        Use target/release Rust compiler and rewatch artifacts
  -q, --quick       Stop on first mismatch
  -v, --verbose     Print each fixture/mode
  -h, --help        Show this help

Compatibility no-ops accepted when called through test_js_output_parity.sh:
  --skip-parser-ast --skip-syntax --skip-spice-ppx --skip-js

ENV:
  OCAML_BSC, RUST_BSC, TIMEOUT_SECONDS can override defaults.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --release)
            RUST_TARGET=release
            REWATCH_TARGET=release
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
        --skip-parser-ast|--skip-syntax|--skip-spice-ppx)
            shift
            ;;
        --skip-js)
            echo "Skipping JS output fixture parity"
            exit 0
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

script_dir=$(cd "$(dirname "$0")"; pwd -P)
PROJECT_ROOT=$(cd "$script_dir/.."; pwd -P)
RUST_TARGET="${RUST_TARGET:-debug}"
REWATCH_TARGET="${REWATCH_TARGET:-$RUST_TARGET}"
OCAML_BSC="${OCAML_BSC:-$PROJECT_ROOT/packages/@rescript/$("$PROJECT_ROOT/scripts/platform.sh")/bin/bsc.exe}"
RUST_BSC="${RUST_BSC:-$PROJECT_ROOT/rewatch/target/$RUST_TARGET/bsc}"
"$PROJECT_ROOT/scripts/rust_compiler_shims.sh" "$RUST_TARGET"
REWATCH_BIN="${REWATCH_BIN:-$PROJECT_ROOT/rewatch/target/$REWATCH_TARGET/rescript}"
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/packages/@rescript/$("$PROJECT_ROOT/scripts/platform.sh")/bin/rescript.exe}"
RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
RUST_BUILD_FLAG=""
REWATCH_BUILD_FLAG=""
if [[ "$RUST_TARGET" == "release" ]]; then
    RUST_BUILD_FLAG=" --release"
fi
if [[ "$REWATCH_TARGET" == "release" ]]; then
    REWATCH_BUILD_FLAG=" --release"
fi
CASES_FILE="$PROJECT_ROOT/tests/js_output_parity/cases.tsv"
FIXTURE_DIR="$PROJECT_ROOT/tests/js_output_parity/fixtures"
CACHE_REL=".parity-cache/js-output-fixtures"
CACHE_DIR="$PROJECT_ROOT/$CACHE_REL"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

missing=0
for exe in "$OCAML_BSC" "$RUST_BSC" "$REWATCH_BIN" "$RESCRIPT_CLI"; do
    if [[ ! -x "$exe" ]]; then
        echo -e "${RED}Missing compiler executable:${RESET} $exe" >&2
        missing=1
    fi
done
if [[ "$missing" -ne 0 ]]; then
    echo "Build first:"
    echo "  make"
    echo "  cargo build$RUST_BUILD_FLAG --manifest-path rewatch/Cargo.toml"
    echo "  cargo build$REWATCH_BUILD_FLAG --manifest-path rewatch/Cargo.toml"
    exit 2
fi
if [[ ! -d "$RESCRIPT_RUNTIME" ]]; then
    echo -e "${RED}Missing ReScript runtime package:${RESET} $RESCRIPT_RUNTIME" >&2
    exit 2
fi
export RESCRIPT_RUNTIME
if [[ ! -d "$FIXTURE_DIR" ]]; then
    echo -e "${YELLOW}No JS output parity fixtures found:${RESET} $FIXTURE_DIR"
    exit 0
fi

mkdir -p "$CACHE_DIR/diffs" "$CACHE_DIR/ocaml" "$CACHE_DIR/rust" "$CACHE_DIR/logs" "$CACHE_DIR/sources"
find "$CACHE_DIR" -type f \( -name '*.js' -o -name '*.mjs' -o -name '*.log' -o -name '*.diff' -o -name '*.status' -o -name '*.res' -o -name '*.resi' -o -name '*.cmi' -o -name '*.cmj' -o -name '*.cmt' -o -name '*.cmti' -o -name '*.ast' -o -name '*.iast' -o -name 'rescript.json' -o -name 'bsconfig.json' -o -name 'build.ninja' -o -name '.compiler.log' -o -name '.sourcedirs.json' \) -delete 2>/dev/null || true
find "$CACHE_DIR" -depth -type d -empty -delete 2>/dev/null || true
mkdir -p "$CACHE_DIR/diffs" "$CACHE_DIR/ocaml" "$CACHE_DIR/rust" "$CACHE_DIR/logs" "$CACHE_DIR/sources"

cd "$PROJECT_ROOT"

safe_name() {
    printf '%s' "$1" | tr '/: ' '___' | tr -c 'A-Za-z0-9_.-' '_'
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

write_directory_project_config() {
    local project_dir="$1"
    local module_system="$2"
    local suffix="$3"
    local case_flags_raw="$4"
    local mode_flags_raw="$5"
    local extra_config_path="$6"

    python3 - "$project_dir/rescript.json" "$module_system" "$suffix" "$case_flags_raw" "$mode_flags_raw" "$extra_config_path" <<'PY'
import json
import os
import sys

path, module_system, suffix, case_flags, mode_flags, extra_config_path = sys.argv[1:7]
compiler_flags = ["-w -a", "-warn-error -a"]
if mode_flags:
    compiler_flags.append(mode_flags)
if case_flags:
    compiler_flags.append(case_flags)

config = {
    "name": "js-output-parity",
    "sources": [{"dir": "src", "subdirs": False}],
    "package-specs": {
        "module": module_system,
        "in-source": True,
        "suffix": suffix,
    },
    "compiler-flags": compiler_flags,
}

if extra_config_path and os.path.exists(extra_config_path):
    with open(extra_config_path, encoding="utf-8") as handle:
        extra_config = json.load(handle)
    config.update(extra_config)

with open(path, "w", encoding="utf-8") as handle:
    json.dump(config, handle, indent=2)
    handle.write("\n")
PY
}

total=0
pass=0
fail=0
failed_files=""

record_failure() {
    local label="$1"
    local reason="$2"
    fail=$((fail + 1))
    failed_files="$failed_files$label ($reason)\n"
    if [[ "$QUICK_MODE" == "true" ]]; then
        return 1
    fi
    return 0
}

compare_directory_case() {
    local source="$1"
    local case_flags_raw="$2"
    local mode_name="$3"
    local module_system="$4"
    local suffix="$5"
    local mode_flags_raw="$6"
    local source_path="$PROJECT_ROOT/$source"

    total=$((total + 1))
    if [[ "$VERBOSE" == "true" ]]; then
        echo "[$mode_name] $source"
    fi

    local safe source_copy_root ocaml_project_dir rust_project_dir ocaml_source_dir rust_source_dir ocaml_log rust_log diff_out
    local extra_config_path
    safe=$(safe_name "${mode_name}_${source}")
    source_copy_root="$CACHE_DIR/sources/$safe"
    ocaml_project_dir="$source_copy_root/ocaml"
    rust_project_dir="$source_copy_root/rust"
    ocaml_source_dir="$ocaml_project_dir/src"
    rust_source_dir="$rust_project_dir/src"
    ocaml_log="$CACHE_DIR/logs/ocaml_${safe}.log"
    rust_log="$CACHE_DIR/logs/rust_${safe}.log"
    diff_out="$CACHE_DIR/diffs/${safe}.diff"
    extra_config_path="$source_path/rescript.extra.json"

    mkdir -p "$ocaml_source_dir" "$rust_source_dir"

    local -a implementation_files interface_files
    implementation_files=()
    interface_files=()

    local source_file source_base
    while IFS= read -r source_file; do
        source_base=$(basename "$source_file")
        cp "$source_file" "$ocaml_source_dir/$source_base"
        cp "$source_file" "$rust_source_dir/$source_base"
        if [[ "$source_base" == *.resi ]]; then
            interface_files+=("$source_base")
        else
            implementation_files+=("$source_base")
        fi
    done < <(find "$source_path" -maxdepth 1 -type f \( -name '*.res' -o -name '*.resi' \) | sort)

    if [[ "${#implementation_files[@]}" -eq 0 ]]; then
        record_failure "$source [$mode_name]" "missing source" || return 1
        return 0
    fi

    write_directory_project_config "$ocaml_project_dir" "$module_system" "$suffix" "$case_flags_raw" "$mode_flags_raw" "$extra_config_path"
    write_directory_project_config "$rust_project_dir" "$module_system" "$suffix" "$case_flags_raw" "$mode_flags_raw" "$extra_config_path"

    run_capture "$ocaml_log" env RESCRIPT_SUBPROCESS_BUILD=1 RESCRIPT_BSC_EXE="$OCAML_BSC" "$RESCRIPT_CLI" build --no-timing true "$ocaml_project_dir"
    run_capture "$rust_log" env RESCRIPT_BSC_EXE="$RUST_BSC" "$REWATCH_BIN" build --in-process --no-timing true "$rust_project_dir"

    local ocaml_status rust_status
    ocaml_status=$(cat "$ocaml_log.status")
    rust_status=$(cat "$rust_log.status")

    if [[ "$ocaml_status" != "0" || "$rust_status" != "0" ]]; then
        {
            echo "Compile status differs or fixture does not compile"
            echo "OCaml: $ocaml_status"
            echo "Rust:  $rust_status"
            echo ""
            echo "--- OCaml compiler output"
            cat "$ocaml_log"
            echo ""
            echo "--- Rust compiler output"
            cat "$rust_log"
        } > "$diff_out"
        record_failure "$source [$mode_name]" "compile error" || return 1
        return 0
    fi

    local stem ocaml_out rust_out output_diff
    for file in "${implementation_files[@]}"; do
        stem="${file%.res}"
        ocaml_out="$ocaml_source_dir/${stem}${suffix}"
        rust_out="$rust_source_dir/${stem}${suffix}"
        if [[ ! -f "$ocaml_out" || ! -f "$rust_out" ]]; then
            {
                echo "Missing generated output for $file"
                echo "OCaml output: $ocaml_out"
                echo "Rust output:  $rust_out"
                echo ""
                echo "--- OCaml compiler output"
                cat "$ocaml_log"
                echo ""
                echo "--- Rust compiler output"
                cat "$rust_log"
            } > "$diff_out"
            record_failure "$source [$mode_name]" "missing output" || return 1
            return 0
        fi
        if ! cmp -s "$ocaml_out" "$rust_out"; then
            output_diff="$CACHE_DIR/diffs/${safe}_$(safe_name "$file").diff"
            diff -u --text "$ocaml_out" "$rust_out" > "$output_diff" 2>&1 || true
            {
                echo "Output differs for $file"
                echo "See: $output_diff"
                echo ""
                cat "$output_diff"
            } > "$diff_out"
            record_failure "$source [$mode_name]" "output differs" || return 1
            return 0
        fi
    done

    pass=$((pass + 1))
}

compare_case() {
    local source="$1"
    local case_flags_raw="$2"
    local mode_name="$3"
    local module_system="$4"
    local suffix="$5"
    local mode_flags_raw="$6"

    if [[ -n "$FILE_ARG" && "$source" != *"$FILE_ARG"* && "$mode_name" != *"$FILE_ARG"* ]]; then
        return 0
    fi

    local source_path="$PROJECT_ROOT/$source"
    if [[ -d "$source_path" ]]; then
        compare_directory_case "$source" "$case_flags_raw" "$mode_name" "$module_system" "$suffix" "$mode_flags_raw" || return 1
        return 0
    fi
    if [[ ! -f "$source_path" ]]; then
        record_failure "$source [$mode_name]" "missing source" || return 1
        return 0
    fi

    total=$((total + 1))
    if [[ "$VERBOSE" == "true" ]]; then
        echo "[$mode_name] $source"
    fi

    local safe stem source_base interface_base source_copy_root ocaml_source_dir rust_source_dir ocaml_source_copy_rel rust_source_copy_rel ocaml_source_copy rust_source_copy interface_path ocaml_interface_copy_rel rust_interface_copy_rel ocaml_dir rust_dir ocaml_pkg_dir rust_pkg_dir ocaml_log rust_log ocaml_out rust_out diff_out
    safe=$(safe_name "${mode_name}_${source}")
    source_base=$(basename "$source")
    interface_base="${source_base}i"
    stem="${source_base%.res}"
    source_copy_root="$CACHE_DIR/sources/$safe"
    ocaml_source_dir="$source_copy_root/ocaml"
    rust_source_dir="$source_copy_root/rust"
    ocaml_source_copy_rel="$CACHE_REL/sources/$safe/ocaml/$source_base"
    rust_source_copy_rel="$CACHE_REL/sources/$safe/rust/$source_base"
    ocaml_source_copy="$PROJECT_ROOT/$ocaml_source_copy_rel"
    rust_source_copy="$PROJECT_ROOT/$rust_source_copy_rel"
    interface_path="${source_path}i"
    ocaml_interface_copy_rel=""
    rust_interface_copy_rel=""
    ocaml_pkg_dir="$CACHE_REL/ocaml/$safe"
    rust_pkg_dir="$CACHE_REL/rust/$safe"
    ocaml_dir="$PROJECT_ROOT/$ocaml_pkg_dir"
    rust_dir="$PROJECT_ROOT/$rust_pkg_dir"
    mkdir -p "$ocaml_source_dir" "$rust_source_dir" "$ocaml_dir" "$rust_dir"
    cp "$source_path" "$ocaml_source_copy"
    cp "$source_path" "$rust_source_copy"
    if [[ -f "$interface_path" ]]; then
        ocaml_interface_copy_rel="$CACHE_REL/sources/$safe/ocaml/$interface_base"
        rust_interface_copy_rel="$CACHE_REL/sources/$safe/rust/$interface_base"
        cp "$interface_path" "$PROJECT_ROOT/$ocaml_interface_copy_rel"
        cp "$interface_path" "$PROJECT_ROOT/$rust_interface_copy_rel"
    fi
    ocaml_log="$CACHE_DIR/logs/ocaml_${safe}.log"
    rust_log="$CACHE_DIR/logs/rust_${safe}.log"
    ocaml_out="$ocaml_dir/${stem}${suffix}"
    rust_out="$rust_dir/${stem}${suffix}"
    diff_out="$CACHE_DIR/diffs/${safe}.diff"

    local -a base_flags case_flags mode_flags
    case_flags=()
    mode_flags=()
    base_flags=(
        -bs-project-root "$PROJECT_ROOT"
        -bs-package-name js-output-parity
        -w -a
        -warn-error -a
        -bs-package-output "${module_system}:${ocaml_pkg_dir}:${suffix}"
    )
    if [[ -n "$case_flags_raw" ]]; then
        read -r -a case_flags <<< "$case_flags_raw"
    fi
    if [[ -n "$mode_flags_raw" ]]; then
        read -r -a mode_flags <<< "$mode_flags_raw"
    fi

    if [[ -n "$ocaml_interface_copy_rel" ]]; then
        local ocaml_interface_log="$CACHE_DIR/logs/ocaml_${safe}.resi.log"
        run_capture "$ocaml_interface_log" "$OCAML_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$ocaml_interface_copy_rel"
        if [[ "$(cat "$ocaml_interface_log.status")" == "0" ]]; then
            run_capture "$ocaml_log" "$OCAML_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$ocaml_source_copy_rel"
        else
            : > "$ocaml_log"
            cp "$ocaml_interface_log.status" "$ocaml_log.status"
        fi
    else
        run_capture "$ocaml_log" "$OCAML_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$ocaml_source_copy_rel"
    fi

    base_flags=(
        -bs-project-root "$PROJECT_ROOT"
        -bs-package-name js-output-parity
        -w -a
        -warn-error -a
        -bs-package-output "${module_system}:${rust_pkg_dir}:${suffix}"
    )
    if [[ -n "$rust_interface_copy_rel" ]]; then
        local rust_interface_log="$CACHE_DIR/logs/rust_${safe}.resi.log"
        run_capture "$rust_interface_log" "$RUST_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$rust_interface_copy_rel"
        if [[ "$(cat "$rust_interface_log.status")" == "0" ]]; then
            run_capture "$rust_log" "$RUST_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$rust_source_copy_rel"
        else
            : > "$rust_log"
            cp "$rust_interface_log.status" "$rust_log.status"
        fi
    else
        run_capture "$rust_log" "$RUST_BSC" "${base_flags[@]}" "${mode_flags[@]+"${mode_flags[@]}"}" "${case_flags[@]+"${case_flags[@]}"}" "$rust_source_copy_rel"
    fi

    local ocaml_status rust_status
    ocaml_status=$(cat "$ocaml_log.status")
    rust_status=$(cat "$rust_log.status")

    if [[ "$ocaml_status" != "0" || "$rust_status" != "0" ]]; then
        {
            echo "Compile status differs or fixture does not compile"
            echo "OCaml: $ocaml_status"
            echo "Rust:  $rust_status"
            echo ""
            echo "--- OCaml compiler output"
            cat "$ocaml_log"
            echo ""
            echo "--- Rust compiler output"
            cat "$rust_log"
        } > "$diff_out"
        record_failure "$source [$mode_name]" "compile error" || return 1
    elif [[ ! -f "$ocaml_out" || ! -f "$rust_out" ]]; then
        {
            echo "Missing generated output"
            echo "OCaml output: $ocaml_out"
            echo "Rust output:  $rust_out"
            echo ""
            echo "--- Generated files in output and source directories"
            find "$ocaml_dir" "$rust_dir" "$ocaml_source_dir" "$rust_source_dir" -type f | sort
            echo ""
            echo "--- OCaml compiler output"
            cat "$ocaml_log"
            echo ""
            echo "--- Rust compiler output"
            cat "$rust_log"
        } > "$diff_out"
        record_failure "$source [$mode_name]" "missing output" || return 1
    elif ! cmp -s "$ocaml_out" "$rust_out"; then
        diff -u --text "$ocaml_out" "$rust_out" > "$diff_out" 2>&1 || true
        record_failure "$source [$mode_name]" "output differs" || return 1
    else
        pass=$((pass + 1))
    fi
}

run_fixture() {
    local source="$1"
    local case_flags="${2:-}"

    compare_case "$source" "$case_flags" "esmodule" "esmodule" ".mjs" "" || return 1
    compare_case "$source" "$case_flags" "commonjs" "commonjs" ".js" "" || return 1
    compare_case "$source" "$case_flags" "debug" "esmodule" ".mjs" "-bs-g" || return 1
    compare_case "$source" "$case_flags" "noassert" "esmodule" ".mjs" "-noassert -bs-noassertfalse" || return 1
    compare_case "$source" "$case_flags" "unsafe" "esmodule" ".mjs" "-unsafe -bs-no-check-div-by-zero" || return 1
    compare_case "$source" "$case_flags" "noheader" "esmodule" ".mjs" "-bs-no-version-header" || return 1
    compare_case "$source" "$case_flags" "cross-module-opt" "esmodule" ".mjs" "-bs-cross-module-opt" || return 1
    compare_case "$source" "$case_flags" "no-cross-module-opt" "esmodule" ".mjs" "-bs-no-cross-module-opt" || return 1
}

echo -e "${BOLD}JS output fixture parity${RESET}"

if [[ -f "$CASES_FILE" ]]; then
    while IFS=$'\t' read -r source flags _comment; do
        [[ -z "${source// }" || "$source" =~ ^# ]] && continue
        run_fixture "$source" "${flags:-}" || true
        if [[ "$QUICK_MODE" == "true" && "$fail" -gt 0 ]]; then
            break
        fi
    done < "$CASES_FILE"
else
    while IFS= read -r source_path; do
        source="${source_path#$PROJECT_ROOT/}"
        run_fixture "$source" "" || true
        if [[ "$QUICK_MODE" == "true" && "$fail" -gt 0 ]]; then
            break
        fi
    done < <(find "$FIXTURE_DIR" -type f -name '*.res' | sort)
fi

echo ""
echo -e "${BOLD}JS output fixture parity summary${RESET}"
echo "  total:  $total"
echo -e "  pass:   ${GREEN}$pass${RESET}"
echo -e "  fail:   ${RED}$fail${RESET}"
echo "  cache:  $CACHE_DIR"

if [[ "$fail" -gt 0 ]]; then
    echo ""
    echo -e "${BOLD}${RED}Failures:${RESET}"
    echo -e "$failed_files" | grep -v '^$' | sed -n '1,30p'
    first_failed=$(find "$CACHE_DIR/diffs" -type f -name '*.diff' | sort | sed -n '1p')
    if [[ -n "$first_failed" && -f "$first_failed" ]]; then
        echo ""
        echo -e "${BOLD}First diff:${RESET} $first_failed"
        head -120 "$first_failed"
    fi
    exit 1
fi

echo -e "${GREEN}SUCCESS: OCaml and Rust JS outputs match for focused fixtures.${RESET}"
