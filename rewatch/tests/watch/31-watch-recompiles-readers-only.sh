#!/bin/bash
cd $(dirname $0)
source "../utils.sh"
cd ../../testrepo

bold "Test: Watcher recompiles only the dependents that read what changed"

# The watcher records every build and starts the next one from that record,
# as `rescript build` does: a value no dependent reads recompiles its module
# alone, and a changed constant that dependents inline into their JavaScript
# recompiles those dependents.

error_output=$(rewatch clean 2>&1)
if [ $? -eq 0 ];
then
  success "Repo Cleaned"
else
  error "Error Cleaning Repo"
  printf "%s\n" "$error_output" >&2
  exit 1
fi

base_source=./src/WatchReadersBase.res
first_source=./src/WatchReadersFirst.res
second_source=./src/WatchReadersSecond.res
first_output=./src/WatchReadersFirst.mjs
second_output=./src/WatchReadersSecond.mjs

cleanup_sources() {
  rm -f "$base_source" "$first_source" "$second_source" \
    ./src/WatchReadersBase.mjs "$first_output" "$second_output"
}

fail() {
  error "$1"
  cat rewatch.log
  exit_watcher
  cleanup_sources
  exit 1
}

echo 'let flag = true' > "$base_source"
echo 'let first = if WatchReadersBase.flag { 838 } else { 2 }' > "$first_source"
echo 'let second = if WatchReadersBase.flag { 839 } else { 3 }' > "$second_source"

rewatch_bg watch > rewatch.log 2>&1 &
success "Watcher Started"

if ! wait_for_pattern_count rewatch.log "Finished .*compilation" 1 30; then
  fail "Initial build did not settle"
fi

# Wait for the next build and print what its "Compiled" line says.
next_build() {
  local completed_builds
  completed_builds=$(grep -c "Finished .*compilation" rewatch.log || true)
  "$@"
  if ! wait_for_pattern_count rewatch.log "Finished .*compilation" "$((completed_builds + 1))" 30; then
    fail "Watcher did not rebuild"
  fi
}

next_build sh -c "echo 'let unread = 1' >> '$base_source'"
compiled=$(grep "^Compiled" rewatch.log | tail -n 1)
if [ "$compiled" = "Compiled 1 module" ]; then
  success "A value no dependent reads recompiles its module alone"
else
  fail "Expected the new value to recompile one module, got: $compiled"
fi

next_build sh -c "printf 'let flag = false\nlet unread = 1\n' > '$base_source'"
compiled=$(grep "^Compiled" rewatch.log | tail -n 1)
if [ "$compiled" = "Compiled 3 modules" ] \
  && grep -q "let first = 2" "$first_output" \
  && grep -q "let second = 3" "$second_output"; then
  success "A changed constant recompiles the dependents that inline it"
else
  error "Expected the changed constant to recompile both readers, got: $compiled"
  cat "$first_output" "$second_output"
  fail "Readers were not recompiled"
fi

completed_builds=$(grep -c "Finished .*compilation" rewatch.log || true)
cleanup_sources
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
