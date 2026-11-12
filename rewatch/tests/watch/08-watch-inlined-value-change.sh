#!/bin/bash
cd $(dirname $0)
source "../utils.sh"
cd ../../testrepo

bold "Test: Watcher recompiles dependents when an inlined value changes"

# Changing `let flag = true` to `false` keeps the module's signature but changes
# the constant its dependents inline into their JavaScript. Every flip must
# recompile the dependent, not only the first rebuild after the watcher starts.

error_output=$(rewatch clean 2>&1)
if [ $? -eq 0 ];
then
  success "Repo Cleaned"
else
  error "Error Cleaning Repo"
  printf "%s\n" "$error_output" >&2
  exit 1
fi

flag_source=./src/WatchInlinedFlag.res
use_source=./src/WatchInlinedUse.res
use_output=./src/WatchInlinedUse.mjs

cleanup_sources() {
  rm -f "$flag_source" "$use_source" ./src/WatchInlinedFlag.mjs "$use_output"
}

echo 'let flag = true' > "$flag_source"
echo 'let b = if WatchInlinedFlag.flag { 838 } else { 2 }' > "$use_source"

rewatch_bg watch > rewatch.log 2>&1 &
success "Watcher Started"

if ! wait_for_pattern_count rewatch.log "Finished .*compilation" 1 30; then
  error "Initial build did not settle"
  cat rewatch.log
  exit_watcher
  cleanup_sources
  exit 1
fi

if ! grep -q "let b = 838" "$use_output" 2>/dev/null; then
  error "Initial output is incorrect"
  cat "$use_output"
  exit_watcher
  cleanup_sources
  exit 1
fi

flip() {
  local value="$1"; local expected="$2"
  local completed_builds
  completed_builds=$(grep -c "Finished .*compilation" rewatch.log || true)
  echo "let flag = $value" > "$flag_source"
  if ! wait_for_pattern_count rewatch.log "Finished .*compilation" "$((completed_builds + 1))" 30; then
    error "Watcher did not rebuild after setting flag to $value"
    cat rewatch.log
    exit_watcher
    cleanup_sources
    exit 1
  fi
  if grep -q "let b = $expected" "$use_output"; then
    success "Dependent recompiled for flag = $value"
  else
    error "Dependent is stale after setting flag to $value"
    cat "$use_output"
    exit_watcher
    cleanup_sources
    exit 1
  fi
}

flip false 2
flip true 838
flip false 2

completed_builds=$(grep -c "Finished .*compilation" rewatch.log || true)
rm -f "$flag_source" "$use_source"
wait_for_pattern_count rewatch.log "Finished .*compilation\|Build failed" "$((completed_builds + 1))" 30

if ! exit_watcher; then
  cleanup_sources
  exit 1
fi

cleanup_sources
rm -f rewatch.log

if git diff --exit-code . > /dev/null 2>&1 && [ -z "$(git ls-files --others --exclude-standard .)" ];
then
  success "No leftover changes"
else
  error "Leftover changes detected"
  git diff .
  git ls-files --others --exclude-standard .
  exit 1
fi
