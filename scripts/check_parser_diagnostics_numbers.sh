#!/bin/bash

set -euo pipefail

scriptDir=$(dirname "$0")
PROJECT_ROOT=$(cd "$scriptDir/.."; pwd -P)
MATRIX_FILE="${1:-$PROJECT_ROOT/tests/syntax_tests/data/parsing/diagnostics_numbers.csv}"
CHECK_RUNTIME="${CHECK_RUNTIME:-0}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-10}"
RES_PARSER="${RES_PARSER:-$PROJECT_ROOT/_build/install/default/bin/res_parser}"

if [[ ! -f "$MATRIX_FILE" ]]; then
  echo "Error: matrix file not found: $MATRIX_FILE"
  exit 1
fi

if [[ "$CHECK_RUNTIME" == "1" && ! -x "$RES_PARSER" ]]; then
  echo "Error: parser executable not found: $RES_PARSER"
  echo "Run 'make' first or set RES_PARSER."
  exit 1
fi

tmp_dir=$(mktemp -d)
cleanup_tmp_dir() {
  find "$tmp_dir" -type f -delete 2>/dev/null || true
  find "$tmp_dir" -mindepth 1 -type d -empty -delete 2>/dev/null || true
  rmdir "$tmp_dir" 2>/dev/null || true
}
trap cleanup_tmp_dir EXIT

error_numbers_file="$tmp_dir/error_numbers.txt"
warning_numbers_file="$tmp_dir/warning_numbers.txt"
seen_keys_file="$tmp_dir/seen_keys.txt"
touch "$error_numbers_file" "$warning_numbers_file" "$seen_keys_file"

total_rows=0
error_rows=0
warning_rows=0
failures=0
error_rows_with_syntax_header=0
error_rows_recovery_only=0

while IFS=, read -r kind number source_file expected_file; do
  [[ -z "${kind// }" ]] && continue
  [[ "$kind" =~ ^# ]] && continue

  total_rows=$((total_rows + 1))

  if [[ "$kind" != "error" && "$kind" != "warning" ]]; then
    echo "FAIL: invalid kind '$kind' in row $total_rows"
    failures=$((failures + 1))
    continue
  fi

  if ! [[ "$number" =~ ^[0-9]+$ ]]; then
    echo "FAIL: invalid number '$number' for $kind row $total_rows"
    failures=$((failures + 1))
    continue
  fi

  key="$kind:$number"
  if grep -Fxq "$key" "$seen_keys_file"; then
    echo "FAIL: duplicate $kind number $number"
    failures=$((failures + 1))
    continue
  fi
  echo "$key" >> "$seen_keys_file"

  if [[ ! -f "$PROJECT_ROOT/$source_file" && ! -f "$source_file" ]]; then
    echo "FAIL: source file missing for $key: $source_file"
    failures=$((failures + 1))
    continue
  fi

  if [[ ! -f "$PROJECT_ROOT/$expected_file" && ! -f "$expected_file" ]]; then
    echo "FAIL: expected output missing for $key: $expected_file"
    failures=$((failures + 1))
    continue
  fi

  src="$source_file"
  exp="$expected_file"

  if [[ "$kind" == "error" ]]; then
    error_rows=$((error_rows + 1))
    echo "$number" >> "$error_numbers_file"
    if [[ ! -s "$PROJECT_ROOT/$exp" && ! -s "$exp" ]]; then
      echo "FAIL: expected output for error $number is empty: $expected_file"
      failures=$((failures + 1))
      continue
    fi
    if rg -q "Syntax error!" "$PROJECT_ROOT/$exp" 2>/dev/null || rg -q "Syntax error!" "$exp"; then
      error_rows_with_syntax_header=$((error_rows_with_syntax_header + 1))
    else
      error_rows_recovery_only=$((error_rows_recovery_only + 1))
    fi
    if [[ "$CHECK_RUNTIME" == "1" ]]; then
      runtime_out="$tmp_dir/runtime_error_${number}.txt"
      runtime_norm="$tmp_dir/runtime_error_${number}.norm.txt"
      (
        cd "$PROJECT_ROOT"
        if timeout "$TIMEOUT_SECONDS" "$RES_PARSER" -recover -print ml "$src" > "$runtime_out" 2>&1; then :; fi
      )
      # Expected snapshots in syntax_tests are keyed without the leading "tests/" prefix.
      sed 's#tests/syntax_tests/#syntax_tests/#g' "$runtime_out" > "$runtime_norm"
      if ! diff -q "$PROJECT_ROOT/$exp" "$runtime_norm" >/dev/null 2>&1; then
        echo "FAIL: runtime parser output differs from expected for error $number: $source_file"
        echo "  diff $expected_file $runtime_norm"
        failures=$((failures + 1))
      fi
    fi
  else
    warning_rows=$((warning_rows + 1))
    echo "$number" >> "$warning_numbers_file"
    if ! rg -q "Warning number $number" "$exp"; then
      echo "FAIL: expected output for warning $number has no 'Warning number $number': $expected_file"
      failures=$((failures + 1))
      continue
    fi
    if [[ "$CHECK_RUNTIME" == "1" ]]; then
      runtime_out="$tmp_dir/runtime_warning_${number}.txt"
      runtime_norm="$tmp_dir/runtime_warning_${number}.norm.txt"
      (
        cd "$PROJECT_ROOT"
        if timeout "$TIMEOUT_SECONDS" "$RES_PARSER" -jsx-version 4 "$src" > "$runtime_out" 2>&1; then :; fi
      )
      sed 's#tests/syntax_tests/#syntax_tests/#g' "$runtime_out" > "$runtime_norm"
      if ! diff -q "$PROJECT_ROOT/$exp" "$runtime_norm" >/dev/null 2>&1; then
        echo "FAIL: runtime parser output differs from expected for warning $number: $source_file"
        echo "  diff $expected_file $runtime_norm"
        failures=$((failures + 1))
      fi
    fi
  fi
done < "$MATRIX_FILE"

# Ensure error numbering is contiguous from 1..max (iteration guarantee).
if [[ -s "$error_numbers_file" ]]; then
  sort -n -u "$error_numbers_file" > "$tmp_dir/error_numbers_sorted.txt"
  max_error=$(tail -1 "$tmp_dir/error_numbers_sorted.txt")
  seq 1 "$max_error" > "$tmp_dir/error_numbers_expected.txt"
  if ! diff -q "$tmp_dir/error_numbers_expected.txt" "$tmp_dir/error_numbers_sorted.txt" >/dev/null 2>&1; then
    echo "FAIL: error numbering has gaps; expected a contiguous 1..$max_error range"
    echo "Missing error numbers:"
    comm -23 "$tmp_dir/error_numbers_expected.txt" "$tmp_dir/error_numbers_sorted.txt" | sed 's/^/  /'
    failures=$((failures + 1))
  fi
fi

echo "Parser diagnostics number matrix:"
echo "  total rows:    $total_rows"
echo "  error rows:    $error_rows"
echo "  warning rows:  $warning_rows"
echo "  error rows with 'Syntax error!': $error_rows_with_syntax_header"
echo "  error rows recovery-only:        $error_rows_recovery_only"
if [[ "$CHECK_RUNTIME" == "1" ]]; then
  echo "  runtime check: enabled"
else
  echo "  runtime check: disabled (set CHECK_RUNTIME=1 to enable)"
fi

if [[ "$failures" -gt 0 ]]; then
  echo "FAILED: $failures issue(s) found"
  exit 1
fi

echo "SUCCESS: diagnostics matrix iterates all numbered parser errors/warnings without gaps"
