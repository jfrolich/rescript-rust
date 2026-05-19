#!/bin/bash

# GenType generated-output parity.
#
# This is intentionally one no-argument entrypoint. It always runs the two
# in-repo GenType suites and the local Tella checkout, comparing raw generated
# .gen.ts/.gen.tsx files that correspond to local .res/.resi source artifacts
# from the OCaml compiler against the Rust in-process compiler. Do not add
# normalization or repo-selection options here.

set -uo pipefail

if [[ $# -ne 0 ]]; then
    echo "Usage: $0" >&2
    echo "Runs all GenType output parity suites: react example, stdlib-no-shims, and Tella." >&2
    exit 2
fi

script_dir=$(cd "$(dirname "$0")"; pwd -P)
PROJECT_ROOT=$(cd "$script_dir/.."; pwd -P)
DUNE_BIN_DIR="$PROJECT_ROOT/_build/install/default/bin"
OCAML_BSC="${OCAML_BSC:-$DUNE_BIN_DIR/bsc}"
RUST_TARGET="debug"
REWATCH_TARGET="debug"
RUST_BSC="${RUST_BSC:-$PROJECT_ROOT/compiler-rust/target/$RUST_TARGET/bsc}"
REWATCH_BIN="${REWATCH_BIN:-$PROJECT_ROOT/rewatch/target/$REWATCH_TARGET/rescript}"
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/packages/@rescript/$("$script_dir/platform.sh")/bin/rescript.exe}"
RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
TELLA_DIR="/Users/jake/dev/tella-fusion"
CACHE_DIR="$PROJECT_ROOT/.parity-cache/gentype-output"
export RESCRIPT_RUNTIME

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

total_suites=0
passed_suites=0
failed_suites=0

check_prerequisites() {
    local missing=false

    if [[ ! -x "$OCAML_BSC" ]]; then
        echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}" >&2
        echo "Run 'make' first to build the OCaml compiler." >&2
        missing=true
    fi

    if [[ ! -x "$RUST_BSC" ]]; then
        echo -e "${RED}Error: Rust bsc not found at $RUST_BSC${RESET}" >&2
        echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml' first." >&2
        missing=true
    fi

    if [[ ! -x "$REWATCH_BIN" ]]; then
        echo -e "${RED}Error: rewatch binary not found at $REWATCH_BIN${RESET}" >&2
        echo "Run 'cargo build --manifest-path rewatch/Cargo.toml' first." >&2
        missing=true
    fi

    if [[ ! -x "$RESCRIPT_CLI" ]]; then
        echo -e "${RED}Error: rescript CLI not found at $RESCRIPT_CLI${RESET}" >&2
        echo "Run 'make lib' first to build the packaged ReScript CLI." >&2
        missing=true
    fi

    if [[ ! -d "$RESCRIPT_RUNTIME" ]]; then
        echo -e "${RED}Error: ReScript runtime not found at $RESCRIPT_RUNTIME${RESET}" >&2
        missing=true
    fi

    if [[ ! -d "$TELLA_DIR" ]]; then
        echo -e "${RED}Error: Tella checkout not found at $TELLA_DIR${RESET}" >&2
        echo "This script always includes Tella; clone it at the standard local path before running." >&2
        missing=true
    fi

    if $missing; then
        exit 2
    fi
}

setup_cache() {
    if [[ -z "$PROJECT_ROOT" || "$PROJECT_ROOT" == "/" || "$CACHE_DIR" != "$PROJECT_ROOT/.parity-cache/gentype-output" ]]; then
        echo "Refusing to clean unexpected cache directory: $CACHE_DIR" >&2
        exit 2
    fi
    if [[ -L "$CACHE_DIR" || ( -e "$CACHE_DIR" && ! -d "$CACHE_DIR" ) ]]; then
        echo "Refusing to clean unsafe cache path: $CACHE_DIR" >&2
        exit 2
    fi

    mkdir -p "$CACHE_DIR"
    find "$CACHE_DIR" -mindepth 1 -type f -delete
    find "$CACHE_DIR" -mindepth 1 -depth -type d -empty -delete
    mkdir -p "$CACHE_DIR"
}

print_suite_header() {
    echo ""
    echo -e "${BOLD}$1${RESET}"
    echo "============================================"
}

make_candidates() {
    local project_dir="$1"
    local out_file="$2"

    python3 - "$project_dir" "$out_file" <<'PY'
import os
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
out_file = Path(sys.argv[2])
skip_names = {
    ".git",
    ".hg",
    ".next",
    "_build",
    "dist",
    "lib",
    "node_modules",
    "target",
}
generated_exts = (".gen.ts", ".gen.tsx")
candidates = set()

for dirpath, dirnames, filenames in os.walk(root):
    dirnames[:] = [name for name in dirnames if name not in skip_names]
    current = Path(dirpath)
    for filename in filenames:
        path = current / filename
        if filename.endswith(".res") or filename.endswith(".resi"):
            stem = path.with_suffix("")
            for ext in generated_exts:
                candidates.add(Path(str(stem) + ext).resolve())

with out_file.open("w", encoding="utf-8") as handle:
    for path in sorted(candidates):
        print(path, file=handle)
PY
}

make_restore_candidates() {
    local project_dir="$1"
    local out_file="$2"

    python3 - "$project_dir" "$out_file" <<'PY'
import os
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
out_file = Path(sys.argv[2])
skip_names = {
    ".git",
    ".hg",
    ".next",
    "_build",
    "dist",
    "lib",
    "node_modules",
    "target",
}
generated_exts = (".gen.ts", ".gen.tsx")
js_suffixes = (".js", ".mjs", ".cjs")
candidates = set()

for dirpath, dirnames, filenames in os.walk(root):
    dirnames[:] = [name for name in dirnames if name not in skip_names]
    current = Path(dirpath)
    for filename in filenames:
        path = current / filename
        if filename.endswith(".res") or filename.endswith(".resi"):
            stem = path.with_suffix("")
            for ext in generated_exts:
                candidates.add(Path(str(stem) + ext).resolve())
            for suffix in js_suffixes:
                candidates.add(Path(str(path) + suffix).resolve())
                candidates.add(Path(str(stem) + suffix).resolve())

with out_file.open("w", encoding="utf-8") as handle:
    for path in sorted(candidates):
        print(path, file=handle)
PY
}

remove_candidates() {
    local candidates_file="$1"

    python3 - "$candidates_file" <<'PY'
import os
import sys

removed = 0
with open(sys.argv[1], encoding="utf-8") as candidates:
    for raw in candidates:
        path = raw.rstrip("\n")
        if not path:
            continue
        if os.path.isfile(path) or os.path.islink(path):
            os.unlink(path)
            removed += 1

print(f"Cleared {removed} generated GenType candidates before Rust build")
PY
}

snapshot_candidates() {
    local candidates_file="$1"
    local backup_dir="$2"
    local state_file="$3"

    python3 - "$candidates_file" "$backup_dir" "$state_file" <<'PY'
import hashlib
import os
import shutil
import sys

candidates_file, backup_dir, state_file = sys.argv[1:4]
os.makedirs(backup_dir, exist_ok=True)

with open(candidates_file, encoding="utf-8") as candidates, open(state_file, "w", encoding="utf-8") as state:
    for raw in candidates:
        path = raw.rstrip("\n")
        if not path:
            continue
        key = hashlib.sha1(path.encode("utf-8")).hexdigest()[:16] + "_" + os.path.basename(path)
        backup = os.path.join(backup_dir, key)
        if os.path.isfile(path) or os.path.islink(path):
            shutil.copy2(path, backup)
            print("exists", path, backup, sep="\t", file=state)
        else:
            print("missing", path, backup, sep="\t", file=state)
PY
}

restore_candidates() {
    local state_file="$1"

    python3 - "$state_file" <<'PY'
import os
import shutil
import sys

state_file = sys.argv[1]
if not os.path.exists(state_file):
    raise SystemExit(0)

with open(state_file, encoding="utf-8") as state:
    for raw in state:
        raw = raw.rstrip("\n")
        if not raw:
            continue
        status, path, backup = raw.split("\t", 2)
        if status == "exists":
            os.makedirs(os.path.dirname(path), exist_ok=True)
            shutil.copy2(backup, path)
        elif status == "missing":
            if os.path.isfile(path) or os.path.islink(path):
                os.unlink(path)
PY
}

snapshot_expected() {
    local candidates_file="$1"
    local expected_dir="$2"
    local manifest_file="$3"
    local project_dir="$4"

    python3 - "$candidates_file" "$expected_dir" "$manifest_file" "$project_dir" <<'PY'
import hashlib
import os
import shutil
import sys
from pathlib import Path

candidates_file, expected_dir, manifest_file, project_dir = sys.argv[1:5]
project = Path(project_dir).resolve()
os.makedirs(expected_dir, exist_ok=True)

with open(candidates_file, encoding="utf-8") as candidates, open(manifest_file, "w", encoding="utf-8") as manifest:
    for raw in candidates:
        path = Path(raw.rstrip("\n"))
        if not path or not path.is_file():
            continue
        key = hashlib.sha1(str(path).encode("utf-8")).hexdigest()[:16] + "_" + path.name
        expected = Path(expected_dir) / key
        shutil.copy2(path, expected)
        try:
            rel = path.relative_to(project)
        except ValueError:
            rel = path
        print(key, path, expected, rel, sep="\t", file=manifest)
PY
}

compare_outputs() {
    local suite_name="$1"
    local project_dir="$2"
    local candidates_file="$3"
    local manifest_file="$4"
    local suite_cache="$5"
    local metrics_file="$6"

    python3 - "$suite_name" "$project_dir" "$candidates_file" "$manifest_file" "$suite_cache" "$metrics_file" <<'PY'
import difflib
import hashlib
import os
import shutil
import sys
from pathlib import Path

suite_name, project_dir, candidates_file, manifest_file, suite_cache, metrics_file = sys.argv[1:7]
project = Path(project_dir).resolve()
suite_cache = Path(suite_cache)
diff_dir = suite_cache / "diffs"
expected_copy_dir = suite_cache / "expected"
actual_copy_dir = suite_cache / "rust"
for directory in (diff_dir, expected_copy_dir, actual_copy_dir):
    directory.mkdir(parents=True, exist_ok=True)

expected = {}
with open(manifest_file, encoding="utf-8") as manifest:
    for raw in manifest:
        raw = raw.rstrip("\n")
        if not raw:
            continue
        key, output_path, expected_path, rel = raw.split("\t", 3)
        expected[Path(output_path)] = (key, Path(expected_path), rel)

actual = set()
with open(candidates_file, encoding="utf-8") as candidates:
    for raw in candidates:
        raw = raw.rstrip("\n")
        if raw and Path(raw).is_file():
            actual.add(Path(raw))

pass_count = 0
changed_count = 0
missing_count = 0
extra_count = 0
hunk_count = 0
failures = []

for output_path, (key, expected_path, rel) in sorted(expected.items(), key=lambda item: item[1][2]):
    diff_path = diff_dir / f"{key}.diff"
    if not output_path.is_file():
        missing_count += 1
        failures.append(f"{rel} (missing Rust output)")
        diff_path.write_text(f"missing Rust output: {output_path}\n", encoding="utf-8")
        continue

    expected_bytes = expected_path.read_bytes()
    actual_bytes = output_path.read_bytes()
    if expected_bytes == actual_bytes:
        pass_count += 1
        continue

    changed_count += 1
    failures.append(f"{rel} (output differs)")
    expected_lines = expected_path.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)
    actual_lines = output_path.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)
    diff_lines = list(difflib.unified_diff(
        expected_lines,
        actual_lines,
        fromfile=f"ocaml/{rel}",
        tofile=f"rust/{rel}",
    ))
    hunk_count += sum(1 for line in diff_lines if line.startswith("@@"))
    diff_path.write_text("".join(diff_lines), encoding="utf-8")
    shutil.copy2(expected_path, expected_copy_dir / key)
    shutil.copy2(output_path, actual_copy_dir / key)

for output_path in sorted(actual - set(expected)):
    extra_count += 1
    key = hashlib.sha1(str(output_path).encode("utf-8")).hexdigest()[:16] + "_" + output_path.name
    try:
        rel = output_path.relative_to(project)
    except ValueError:
        rel = output_path
    failures.append(f"{rel} (extra Rust output)")
    (diff_dir / f"{key}.diff").write_text(f"extra Rust output: {output_path}\n", encoding="utf-8")
    shutil.copy2(output_path, actual_copy_dir / key)

total_count = pass_count + changed_count + missing_count + extra_count
failure_file = suite_cache / "failures.txt"
failure_file.write_text("\n".join(failures[:40]) + ("\n" if failures else ""), encoding="utf-8")

with open(metrics_file, "w", encoding="utf-8") as metrics:
    print(f"PASS_COUNT={pass_count}", file=metrics)
    print(f"CHANGED_COUNT={changed_count}", file=metrics)
    print(f"MISSING_COUNT={missing_count}", file=metrics)
    print(f"EXTRA_COUNT={extra_count}", file=metrics)
    print(f"HUNK_COUNT={hunk_count}", file=metrics)
    print(f"TOTAL_COUNT={total_count}", file=metrics)
    print(f"FAILURE_FILE={failure_file}", file=metrics)
PY
}

has_typecheck_script() {
    local project_dir="$1"

    [[ -f "$project_dir/package.json" ]] || return 1
    python3 - "$project_dir/package.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    package = json.load(handle)
scripts = package.get("scripts", {})
raise SystemExit(0 if "typecheck" in scripts else 1)
PY
}

run_typecheck() {
    local suite_name="$1"
    local project_dir="$2"
    local phase="$3"
    local log_file="$4"

    if ! has_typecheck_script "$project_dir"; then
        echo "not-configured" > "$log_file.status"
        return 0
    fi

    local status
    if (cd "$project_dir" && yarn typecheck > "$log_file" 2>&1); then
        echo "0" > "$log_file.status"
        return 0
    else
        status=$?
    fi

    echo "$status" > "$log_file.status"
    echo -e "${YELLOW}${suite_name}: ${phase} TypeScript typecheck failed (status $status)${RESET}" >&2
    tail -40 "$log_file" >&2
    return 0
}

run_build() {
    local label="$1"
    local log_file="$2"
    shift 2

    echo -e "${BOLD}$label${RESET}"
    if "$@" > "$log_file" 2>&1; then
        tail -20 "$log_file"
        echo ""
        return 0
    fi

    echo -e "${RED}$label failed${RESET}" >&2
    tail -80 "$log_file" >&2
    echo "" >&2
    return 1
}

run_suite() {
    local suite_name="$1"
    local project_dir="$2"
    local suite_cache="$CACHE_DIR/$suite_name"
    local temp_dir
    local candidates_file
    local restore_candidates_file
    local state_file
    local manifest_file
    local metrics_file
    local restored=false

    total_suites=$((total_suites + 1))
    print_suite_header "$suite_name"
    echo "Project:        $project_dir"
    echo "OCaml bsc:      $OCAML_BSC"
    echo "Rust bsc:       $RUST_BSC"
    echo "Rewatch:        $REWATCH_BIN"
    echo "Runtime:        $RESCRIPT_RUNTIME"
    echo "Artifact cache: $suite_cache"
    echo ""

    mkdir -p "$suite_cache/errors"
    temp_dir=$(mktemp -d)
    candidates_file="$temp_dir/candidates.txt"
    restore_candidates_file="$temp_dir/restore-candidates.txt"
    state_file="$temp_dir/original-state.tsv"
    manifest_file="$temp_dir/expected-manifest.tsv"
    metrics_file="$temp_dir/metrics.env"

    cleanup_suite() {
        if [[ "$restored" != "true" ]]; then
            restore_candidates "$state_file" || true
            restored=true
        fi
        if [[ -n "${temp_dir:-}" && -d "$temp_dir" ]]; then
            find "$temp_dir" -type f -delete 2>/dev/null || true
            find "$temp_dir" -depth -type d -empty -delete 2>/dev/null || true
            rmdir "$temp_dir" 2>/dev/null || true
        fi
    }

    make_candidates "$project_dir" "$candidates_file"
    make_restore_candidates "$project_dir" "$restore_candidates_file"
    snapshot_candidates "$restore_candidates_file" "$temp_dir/original" "$state_file"

    if ! run_build "$suite_name: building expected outputs with OCaml bsc" "$suite_cache/errors/ocaml-build.log" bash -c '
        set -e
        cd "$0"
        RESCRIPT_BSC_EXE="$1" "$2" clean
        RESCRIPT_BSC_EXE="$1" "$2" build
    ' "$project_dir" "$OCAML_BSC" "$RESCRIPT_CLI"; then
        echo -e "${RED}$suite_name: OCaml build failed; cannot compute parity for this suite${RESET}" >&2
        failed_suites=$((failed_suites + 1))
        cleanup_suite
        return
    fi

    snapshot_expected "$candidates_file" "$temp_dir/expected" "$manifest_file" "$project_dir"
    local expected_count
    expected_count=$(wc -l < "$manifest_file" | tr -d ' ')
    echo "Snapshotted $expected_count OCaml-generated GenType files"
    run_typecheck "$suite_name" "$project_dir" "OCaml" "$suite_cache/errors/ocaml-typecheck.log"
    local ocaml_typecheck
    ocaml_typecheck=$(cat "$suite_cache/errors/ocaml-typecheck.log.status" 2>/dev/null || echo "not-run")
    echo ""
    remove_candidates "$candidates_file"
    echo ""

    if ! run_build "$suite_name: building actual outputs with Rust in-process compiler" "$suite_cache/errors/rust-build.log" bash -c '
        set -e
        cd "$0"
        RESCRIPT_BSC_EXE="$2" "$1" clean
        RESCRIPT_BSC_EXE="$2" "$1" build --in-process
    ' "$project_dir" "$REWATCH_BIN" "$RUST_BSC"; then
        echo -e "${RED}$suite_name: Rust build failed; log saved to $suite_cache/errors/rust-build.log${RESET}" >&2
        failed_suites=$((failed_suites + 1))
        cleanup_suite
        return
    fi

    compare_outputs "$suite_name" "$project_dir" "$candidates_file" "$manifest_file" "$suite_cache" "$metrics_file"
    # shellcheck disable=SC1090
    source "$metrics_file"

    run_typecheck "$suite_name" "$project_dir" "Rust" "$suite_cache/errors/rust-typecheck.log"
    local rust_typecheck
    rust_typecheck=$(cat "$suite_cache/errors/rust-typecheck.log.status" 2>/dev/null || echo "not-run")

    echo ""
    echo -e "${BOLD}$suite_name summary${RESET}"
    if [[ "$TOTAL_COUNT" -gt 0 ]]; then
        local pct
        pct=$(python3 -c "print(f'{100 * $PASS_COUNT / $TOTAL_COUNT:.1f}')")
        echo -e "Generated parity: ${GREEN}$PASS_COUNT${RESET}/$TOTAL_COUNT (${pct}%)"
    else
        echo -e "Generated parity: ${YELLOW}0/0${RESET}"
    fi
    echo -e "Changed files:    ${YELLOW}$CHANGED_COUNT${RESET}"
    echo -e "Missing files:    ${RED}$MISSING_COUNT${RESET}"
    echo -e "Extra files:      ${RED}$EXTRA_COUNT${RESET}"
    echo "Diff hunks:       $HUNK_COUNT"
    echo "Typecheck OCaml:  $ocaml_typecheck"
    echo "Typecheck Rust:   $rust_typecheck"
    echo "Diffs:            $suite_cache/diffs"
    echo "Build logs:       $suite_cache/errors"

    if [[ -s "$FAILURE_FILE" ]]; then
        echo ""
        echo -e "${BOLD}First failures:${RESET}"
        sed -n '1,20p' "$FAILURE_FILE" | sed 's/^/  - /'
    fi

    if [[ "$CHANGED_COUNT" -eq 0 && "$MISSING_COUNT" -eq 0 && "$EXTRA_COUNT" -eq 0 && "$rust_typecheck" == "$ocaml_typecheck" ]]; then
        passed_suites=$((passed_suites + 1))
    else
        failed_suites=$((failed_suites + 1))
    fi

    cleanup_suite
}

check_prerequisites
setup_cache

echo -e "${BOLD}GenType Output Parity${RESET}"
echo "============================================"
echo "This script always runs all three GenType generated-output suites."
echo "Rust target:    $RUST_TARGET"
echo "Rewatch target: $REWATCH_TARGET"
echo "Cache:          $CACHE_DIR"

run_suite "typescript-react-example" "$PROJECT_ROOT/tests/gentype_tests/typescript-react-example"
run_suite "stdlib-no-shims" "$PROJECT_ROOT/tests/gentype_tests/stdlib-no-shims"
run_suite "tella" "$TELLA_DIR"

echo ""
echo -e "${BOLD}GenType parity summary${RESET}"
echo "============================================"
echo -e "Suites passed: ${GREEN}$passed_suites${RESET}/$total_suites"
echo -e "Suites failed: ${RED}$failed_suites${RESET}"
echo "Cache:         $CACHE_DIR"

if [[ "$failed_suites" -ne 0 ]]; then
    exit 1
fi

echo -e "${GREEN}SUCCESS: all GenType output parity suites match${RESET}"
