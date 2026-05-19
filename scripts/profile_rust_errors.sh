#!/bin/bash
# Profile Rust compiler errors across all test files
# Collects error messages, groups by type, identifies root causes

set -e

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)
RUST_TARGET="${RUST_TARGET:-debug}"
RUST_BSC="$PROJECT_ROOT/compiler-rust/target/$RUST_TARGET/bsc"
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/packages/@rescript/$("$scriptDir/platform.sh")/bin/rescript.exe}"
OCAML_BSC="$PROJECT_ROOT/_build/install/default/bin/bsc"
TEST_PROJECT="$PROJECT_ROOT/tests/tests"
TIMEOUT_SECONDS=10

TEMP_DIR=$(mktemp -d)

cleanup_dir_tree() {
    local dir="$1"
    [[ -n "$dir" && -d "$dir" ]] || return 0
    find "$dir" -type f -exec rm -f {} + 2>/dev/null || true
    find "$dir" -type l -exec rm -f {} + 2>/dev/null || true
    find "$dir" -depth -type d -empty -exec rmdir {} \; 2>/dev/null || true
}

trap 'cleanup_dir_tree "$TEMP_DIR"' EXIT

echo "Profiling Rust compiler errors..."
echo "================================="
echo "Rust bsc: $RUST_BSC"
echo "Rust target: $RUST_TARGET"

# Find all .res files
find tests/tests/src -name "*.res" -type f 2>/dev/null | sort > "$TEMP_DIR/files.txt"
TOTAL=$(wc -l < "$TEMP_DIR/files.txt" | tr -d ' ')
echo "Total test files: $TOTAL"
echo ""

# Results files
PASS_FILE="$TEMP_DIR/pass.txt"
FAIL_FILE="$TEMP_DIR/fail.txt"
ERROR_FILE="$TEMP_DIR/errors.txt"
touch "$PASS_FILE" "$FAIL_FILE" "$ERROR_FILE"

PASS=0
FAIL=0
COUNT=0

while IFS= read -r file; do
    COUNT=$((COUNT + 1))

    full_file_path="$PROJECT_ROOT/$file"
    rel_path="${full_file_path#$TEST_PROJECT/}"

    # Get compiler arguments from rewatch
    compiler_args_json=$(cd "$TEST_PROJECT" && "$RESCRIPT_CLI" compiler-args "$rel_path" 2>/dev/null) || compiler_args_json=""

    if [[ -n "$compiler_args_json" ]]; then
        args=$(echo "$compiler_args_json" | python3 -c "import sys, json; d=json.load(sys.stdin); print(' '.join(d.get('compiler_args', [])))" 2>/dev/null) || args=""
    else
        args=""
    fi

    # Run Rust compiler
    if [[ -n "$args" ]]; then
        error_output=$(cd "$TEST_PROJECT/lib/bs" && timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -dtyped-sexp $args 2>&1 1>/dev/null) || true
    else
        error_output=$(timeout "$TIMEOUT_SECONDS" "$RUST_BSC" -dtyped-sexp "$full_file_path" 2>&1 1>/dev/null) || true
    fi

    # Check if sexp output was produced (starts with "(structure")
    if echo "$error_output" | grep -q "^(structure"; then
        PASS=$((PASS + 1))
        echo "$file" >> "$PASS_FILE"
    else
        FAIL=$((FAIL + 1))
        echo "$file" >> "$FAIL_FILE"
        # Extract the first error line
        first_error=$(echo "$error_output" | head -20)
        echo "FILE: $file" >> "$ERROR_FILE"
        echo "ERROR: $first_error" >> "$ERROR_FILE"
        echo "---" >> "$ERROR_FILE"
    fi

    if [[ $((COUNT % 50)) -eq 0 ]]; then
        echo "  Progress: $COUNT/$TOTAL (pass=$PASS, fail=$FAIL)"
    fi
done < "$TEMP_DIR/files.txt"

echo ""
echo "Results: $PASS passed, $FAIL failed out of $TOTAL"
echo ""

# Save results
cp "$PASS_FILE" "$PROJECT_ROOT/tmp_parity_diffs/rust_pass.txt" 2>/dev/null || mkdir -p "$PROJECT_ROOT/tmp_parity_diffs" && cp "$PASS_FILE" "$PROJECT_ROOT/tmp_parity_diffs/rust_pass.txt"
cp "$FAIL_FILE" "$PROJECT_ROOT/tmp_parity_diffs/rust_fail.txt"
cp "$ERROR_FILE" "$PROJECT_ROOT/tmp_parity_diffs/rust_errors.txt"

echo "Categorizing errors..."
echo ""

# Extract error patterns and count them
echo "=== Error Categories ==="
echo ""

# Common error patterns to look for
echo "--- By error keyword ---"
grep "^ERROR:" "$ERROR_FILE" | sed 's/ERROR: //' | while read -r line; do
    # Extract the primary error type
    if echo "$line" | grep -q "Unbound module"; then
        echo "UnboundModule"
    elif echo "$line" | grep -q "Unbound value"; then
        echo "UnboundValue"
    elif echo "$line" | grep -q "Unbound type constructor"; then
        echo "UnboundTypeConstructor"
    elif echo "$line" | grep -q "Unbound constructor"; then
        echo "UnboundConstructor"
    elif echo "$line" | grep -q "UndefinedMethod"; then
        echo "UndefinedMethod"
    elif echo "$line" | grep -q "NotAVariantType"; then
        echo "NotAVariantType"
    elif echo "$line" | grep -q "not yet implemented"; then
        echo "NotImplemented"
    elif echo "$line" | grep -q "todo!"; then
        echo "TodoPanic"
    elif echo "$line" | grep -q "panicked"; then
        echo "Panic"
    elif echo "$line" | grep -q "not implemented"; then
        echo "NotImplemented"
    elif echo "$line" | grep -q "Error"; then
        # Generic error - capture more context
        echo "OtherError"
    elif echo "$line" | grep -q "thread.*panicked"; then
        echo "Panic"
    elif [[ -z "$line" ]]; then
        echo "EmptyOutput"
    else
        echo "Unknown"
    fi
done | sort | uniq -c | sort -rn

echo ""
echo "Full error details saved to tmp_parity_diffs/rust_errors.txt"
echo "Pass list saved to tmp_parity_diffs/rust_pass.txt"
echo "Fail list saved to tmp_parity_diffs/rust_fail.txt"
