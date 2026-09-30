#!/bin/bash

# Tella JS output parity: build the external project once with the OCaml
# compiler, snapshot the generated JS, then build the same project with
# rewatch --in-process and compare the generated JS outputs.
#
# Usage:
#   ./scripts/test_tella_output_parity.sh [OPTIONS] [FILE|PATTERN]
#
# Options:
#   --release        Use target/release Rust compiler and rewatch artifacts
#   -q, --quick       Stop on first output diff
#   -v, --verbose     Show progress for each output file
#   -h, --help        Show this help message

set -euo pipefail

QUICK_MODE=false
VERBOSE=false
FILE_ARG=""

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
            # Accepted for compatibility when called through test_js_output_parity.sh,
            # where these options belong to the local per-file parity harness.
            shift
            ;;
        --skip-js)
            echo "Skipping Tella JS output parity"
            exit 0
            ;;
        -h|--help)
            sed -n '3,13p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        -*)
            echo "Unknown option: $1" >&2
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
DUNE_BIN_DIR="$PROJECT_ROOT/_build/install/default/bin"
OCAML_BSC="${OCAML_BSC:-$DUNE_BIN_DIR/bsc}"
RUST_TARGET="${RUST_TARGET:-debug}"
REWATCH_TARGET="${REWATCH_TARGET:-$RUST_TARGET}"
RUST_BSC="${RUST_BSC:-$PROJECT_ROOT/compiler-rust/target/$RUST_TARGET/bsc}"
REWATCH_BIN="${REWATCH_BIN:-$PROJECT_ROOT/rewatch/target/$REWATCH_TARGET/rescript}"
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/packages/@rescript/$("$script_dir/platform.sh")/bin/rescript.exe}"
RESCRIPT_RUNTIME="${RESCRIPT_RUNTIME:-$PROJECT_ROOT/packages/@rescript/runtime}"
TELLA_DIR="${TELLA_DIR:-$HOME/dev/tella-fusion}"
TELLA_BUILD_DIR="${TELLA_BUILD_DIR:-$TELLA_DIR}"
CACHE_DIR="$PROJECT_ROOT/.parity-cache/tella-output"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BOLD='\033[1m'
RESET='\033[0m'

if [[ ! -x "$OCAML_BSC" ]]; then
    echo -e "${RED}Error: OCaml bsc not found at $OCAML_BSC${RESET}" >&2
    exit 2
fi

if [[ ! -x "$RUST_BSC" ]]; then
    echo -e "${RED}Error: Rust bsc not found at $RUST_BSC${RESET}" >&2
    if [[ "$RUST_TARGET" == "release" ]]; then
        echo "Run 'cargo build --release --manifest-path compiler-rust/Cargo.toml' first." >&2
    else
        echo "Run 'cargo build --manifest-path compiler-rust/Cargo.toml' first." >&2
    fi
    exit 2
fi

if [[ ! -x "$REWATCH_BIN" ]]; then
    echo -e "${RED}Error: rewatch binary not found at $REWATCH_BIN${RESET}" >&2
    if [[ "$REWATCH_TARGET" == "release" ]]; then
        echo "Run 'cargo build --release --manifest-path rewatch/Cargo.toml' first." >&2
    else
        echo "Run 'cargo build --manifest-path rewatch/Cargo.toml' first." >&2
    fi
    exit 2
fi

if [[ ! -x "$RESCRIPT_CLI" ]]; then
    echo -e "${RED}Error: rescript CLI not found at $RESCRIPT_CLI${RESET}" >&2
    exit 2
fi

if [[ ! -d "$RESCRIPT_RUNTIME" ]]; then
    echo -e "${RED}Error: ReScript runtime package not found at $RESCRIPT_RUNTIME${RESET}" >&2
    echo "Set RESCRIPT_RUNTIME to the runtime package matching the compiler under test." >&2
    exit 2
fi
export RESCRIPT_RUNTIME

if [[ ! -d "$TELLA_DIR" ]]; then
    echo -e "${RED}Error: tella-fusion not found at $TELLA_DIR${RESET}" >&2
    echo "Set TELLA_DIR to the external project directory." >&2
    exit 2
fi

if [[ ! -f "$TELLA_BUILD_DIR/rescript.json" && ! -f "$TELLA_BUILD_DIR/bsconfig.json" ]]; then
    echo -e "${RED}Error: ReScript project config not found at $TELLA_BUILD_DIR${RESET}" >&2
    echo "Set TELLA_BUILD_DIR to the package that should be built." >&2
    exit 2
fi

if [[ "$CACHE_DIR" != "$PROJECT_ROOT/.parity-cache/tella-output" ]]; then
    echo "Refusing to clean unexpected cache directory: $CACHE_DIR" >&2
    exit 2
fi

mkdir -p "$CACHE_DIR/diffs" "$CACHE_DIR/errors" "$CACHE_DIR/expected" "$CACHE_DIR/rust"
find "$CACHE_DIR" -mindepth 1 -type f -delete
find "$CACHE_DIR" -mindepth 1 -depth -type d -empty -delete
mkdir -p "$CACHE_DIR/diffs" "$CACHE_DIR/errors" "$CACHE_DIR/expected" "$CACHE_DIR/rust"

TEMP_DIR=$(mktemp -d)
RESTORE_READY=false

restore_generated_files() {
    if [[ "$RESTORE_READY" != "true" ]]; then
        return
    fi

    python3 - "$TEMP_DIR/original-state.tsv" <<'PY'
import os
import shutil
import sys

state_path = sys.argv[1]
if not os.path.exists(state_path):
    raise SystemExit(0)

with open(state_path, encoding="utf-8") as handle:
    for line in handle:
        line = line.rstrip("\n")
        if not line:
            continue
        status, path, backup = line.split("\t", 2)
        if status == "exists":
            os.makedirs(os.path.dirname(path), exist_ok=True)
            shutil.copy2(backup, path)
        elif status == "missing":
            if os.path.isfile(path) or os.path.islink(path):
                os.unlink(path)
PY
}

cleanup() {
    restore_generated_files || true
    if [[ -n "${TEMP_DIR:-}" && -d "$TEMP_DIR" ]]; then
        find "$TEMP_DIR" -type f -delete 2>/dev/null || true
        find "$TEMP_DIR" -depth -type d -empty -delete 2>/dev/null || true
        rmdir "$TEMP_DIR" 2>/dev/null || true
    fi
}
trap cleanup EXIT

echo -e "${BOLD}Tella JS Output Parity${RESET}"
echo "============================================"
echo "Tella dir:       $TELLA_DIR"
echo "Build dir:       $TELLA_BUILD_DIR"
echo "OCaml bsc:       $OCAML_BSC"
echo "Rust bsc:        $RUST_BSC"
echo "Rewatch:         $REWATCH_BIN"
echo "Rust target:     $RUST_TARGET"
echo "Rewatch target:  $REWATCH_TARGET"
echo "Runtime:         $RESCRIPT_RUNTIME"
echo "Artifact cache:  $CACHE_DIR"
echo ""

echo -e "${BOLD}Step 1: Finding source files...${RESET}"
find "$TELLA_DIR" \
    -type d \( -name .git -o -name target -o -name .next -o -name _build -o -path "*/lib/bs" -o -path "*/lib/ocaml" \) -prune \
    -o -type f -name "*.res" -print 2>/dev/null | sort > "$TEMP_DIR/sources.all.txt"

if [[ -n "$FILE_ARG" ]]; then
    if [[ -f "$FILE_ARG" ]]; then
        realpath "$FILE_ARG" > "$TEMP_DIR/sources.txt"
    elif [[ -f "$TELLA_DIR/$FILE_ARG" ]]; then
        realpath "$TELLA_DIR/$FILE_ARG" > "$TEMP_DIR/sources.txt"
    elif [[ -f "$TELLA_DIR/${FILE_ARG}.res" ]]; then
        realpath "$TELLA_DIR/${FILE_ARG}.res" > "$TEMP_DIR/sources.txt"
    else
        grep -E "$FILE_ARG" "$TEMP_DIR/sources.all.txt" > "$TEMP_DIR/sources.txt" || true
    fi
else
    cp "$TEMP_DIR/sources.all.txt" "$TEMP_DIR/sources.txt"
fi

if [[ ! -s "$TEMP_DIR/sources.txt" ]]; then
    echo -e "${RED}Error: no Tella source files found${RESET}" >&2
    exit 1
fi

SOURCE_COUNT=$(wc -l < "$TEMP_DIR/sources.txt" | tr -d ' ')
echo "Found $SOURCE_COUNT source files"
echo ""

python3 - "$TEMP_DIR/sources.txt" "$TEMP_DIR/generated-candidates.txt" "$TEMP_DIR/js-candidates.txt" <<'PY'
import sys
from pathlib import Path

sources_path, generated_path, js_path = sys.argv[1:4]
generated_exts = [".bs.js", ".js", ".mjs", ".cjs", ".gen.ts", ".ast"]
js_exts = [".bs.js", ".js", ".mjs", ".cjs"]
generated = set()
js_outputs = set()

with open(sources_path, encoding="utf-8") as handle:
    for raw in handle:
        raw = raw.strip()
        if not raw:
            continue
        source = Path(raw)
        stem = source.with_suffix("")
        for ext in generated_exts:
            generated.add(str(stem) + ext)
        for ext in js_exts:
            js_outputs.add(str(stem) + ext)

with open(generated_path, "w", encoding="utf-8") as handle:
    for path in sorted(generated):
        print(path, file=handle)

with open(js_path, "w", encoding="utf-8") as handle:
    for path in sorted(js_outputs):
        print(path, file=handle)
PY

echo -e "${BOLD}Step 2: Snapshotting current generated files for restore...${RESET}"
python3 - "$TEMP_DIR/generated-candidates.txt" "$TEMP_DIR/original" "$TEMP_DIR/original-state.tsv" <<'PY'
import hashlib
import os
import shutil
import sys

candidates_path, backup_dir, state_path = sys.argv[1:4]
os.makedirs(backup_dir, exist_ok=True)

with open(candidates_path, encoding="utf-8") as candidates, open(state_path, "w", encoding="utf-8") as state:
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
RESTORE_READY=true
echo ""

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

touch "$TEMP_DIR/ocaml-build-start.marker"
if ! run_build "Step 3: Building expected outputs with OCaml bsc..." "$TEMP_DIR/ocaml-build.log" bash -c '
    set -e
    cd "$0"
    RESCRIPT_SUBPROCESS_BUILD=1 RESCRIPT_BSC_EXE="$1" "$2" clean
    RESCRIPT_SUBPROCESS_BUILD=1 RESCRIPT_BSC_EXE="$1" "$2" build
' "$TELLA_BUILD_DIR" "$OCAML_BSC" "$RESCRIPT_CLI"; then
    cp "$TEMP_DIR/ocaml-build.log" "$CACHE_DIR/errors/ocaml-build.err" 2>/dev/null || true
    exit 2
fi

python3 - "$TEMP_DIR/js-candidates.txt" "$TEMP_DIR/expected" "$TEMP_DIR/expected-manifest.tsv" "$TEMP_DIR/ocaml-build-start.marker" <<'PY'
import hashlib
import os
import shutil
import sys

candidates_path, expected_dir, manifest_path, marker_path = sys.argv[1:5]
marker_mtime = os.path.getmtime(marker_path)
os.makedirs(expected_dir, exist_ok=True)
with open(candidates_path, encoding="utf-8") as candidates, open(manifest_path, "w", encoding="utf-8") as manifest:
    for raw in candidates:
        path = raw.rstrip("\n")
        if not path or not os.path.isfile(path):
            continue
        if os.path.getmtime(path) < marker_mtime:
            continue
        key = hashlib.sha1(path.encode("utf-8")).hexdigest()[:16] + "_" + os.path.basename(path)
        expected = os.path.join(expected_dir, key)
        shutil.copy2(path, expected)
        print(key, path, expected, sep="\t", file=manifest)
PY

EXPECTED_COUNT=$(wc -l < "$TEMP_DIR/expected-manifest.tsv" | tr -d ' ')
if [[ "$EXPECTED_COUNT" -eq 0 ]]; then
    echo -e "${RED}Error: OCaml build did not produce any JS outputs to compare${RESET}" >&2
    exit 2
fi
echo "Snapshotted $EXPECTED_COUNT OCaml-generated JS outputs"
echo ""

if ! run_build "Step 4: Building actual outputs with rewatch --in-process..." "$TEMP_DIR/rust-build.log" bash -c '
    set -e
    cd "$0"
    RESCRIPT_BSC_EXE="$2" "$1" clean
    RESCRIPT_BSC_EXE="$2" "$1" build --in-process
' "$TELLA_BUILD_DIR" "$REWATCH_BIN" "$RUST_BSC"; then
    cp "$TEMP_DIR/rust-build.log" "$CACHE_DIR/errors/rust-build.err" 2>/dev/null || true
    echo -e "${RED}Rust in-process build failed; log saved to $CACHE_DIR/errors/rust-build.err${RESET}" >&2
    exit 1
fi
# Keep both build logs so their diagnostics can be compared.
mkdir -p "$CACHE_DIR/logs"
cp "$TEMP_DIR/ocaml-build.log" "$CACHE_DIR/logs/ocaml-build.log" 2>/dev/null || true
cp "$TEMP_DIR/rust-build.log" "$CACHE_DIR/logs/rust-build.log" 2>/dev/null || true

echo -e "${BOLD}Step 5: Comparing generated JS outputs...${RESET}"
pass_count=0
diff_count=0
missing_count=0
failed_files=""

while IFS=$'\t' read -r key output_path expected_path; do
    [[ -n "$key" ]] || continue
    rel_path="${output_path#$TELLA_DIR/}"
    diff_file="$CACHE_DIR/diffs/$key.diff"

    if [[ ! -f "$output_path" ]]; then
        missing_count=$((missing_count + 1))
        failed_files+="$rel_path (missing Rust output)"$'\n'
        printf 'missing Rust output: %s\n' "$output_path" > "$diff_file"
        if [[ "$QUICK_MODE" == "true" ]]; then
            echo -e "${RED}Quick mode: stopping on missing output${RESET}"
            cat "$diff_file"
            exit 1
        fi
        continue
    fi

    if diff -q "$expected_path" "$output_path" >/dev/null 2>&1; then
        pass_count=$((pass_count + 1))
        if [[ "$VERBOSE" == "true" ]]; then
            echo -e "${GREEN}PASS${RESET} $rel_path"
        fi
    else
        diff_count=$((diff_count + 1))
        failed_files+="$rel_path (output differs)"$'\n'
        diff -u "$expected_path" "$output_path" > "$diff_file" 2>&1 || true
        cp "$expected_path" "$CACHE_DIR/expected/$key" 2>/dev/null || true
        cp "$output_path" "$CACHE_DIR/rust/$key" 2>/dev/null || true
        if [[ "$VERBOSE" == "true" ]]; then
            echo -e "${RED}FAIL${RESET} $rel_path"
        fi
        if [[ "$QUICK_MODE" == "true" ]]; then
            echo -e "${RED}Quick mode: stopping on output diff${RESET}"
            head -120 "$diff_file"
            exit 1
        fi
    fi
done < "$TEMP_DIR/expected-manifest.tsv"

total_count=$((pass_count + diff_count + missing_count))
echo ""
echo -e "${BOLD}Summary${RESET}"
if [[ "$total_count" -gt 0 ]]; then
    pct=$(python3 -c "print(f'{100 * $pass_count / $total_count:.1f}')")
    echo -e "Passed:         ${GREEN}$pass_count${RESET}/$total_count (${pct}%)"
else
    echo -e "Passed:         ${YELLOW}0/0${RESET}"
fi
echo -e "Output differs: ${YELLOW}$diff_count${RESET}"
echo -e "Missing output: ${RED}$missing_count${RESET}"
echo "Diffs:          $CACHE_DIR/diffs"
echo "Build errors:   $CACHE_DIR/errors"

if [[ -n "$failed_files" ]]; then
    echo ""
    echo -e "${BOLD}Failed outputs (first 20):${RESET}"
    FAILED_FILES="$failed_files" python3 - <<'PY'
import os

printed = 0
for line in os.environ["FAILED_FILES"].splitlines():
    if not line:
        continue
    print(f"  - {line}")
    printed += 1
    if printed >= 20:
        break
PY
fi

if [[ "$diff_count" -gt 0 || "$missing_count" -gt 0 ]]; then
    exit 1
fi

echo ""
echo -e "${GREEN}${BOLD}SUCCESS: all Tella JS outputs match the OCaml build.${RESET}"
