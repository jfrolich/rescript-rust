#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: Parse warnings persist after an incremental watch start"
root=$(mktemp -d "${TMPDIR:-/tmp}/rescript-watch-parse-warnings.XXXXXX")
watcher_pid=""
cleanup() {
  if [ -n "$watcher_pid" ]; then
    exit_watcher || kill_process "$watcher_pid"
    wait "$watcher_pid" || true
  fi
  TEST_ROOT="$root" node -e 'require("fs").rmSync(process.env.TEST_ROOT, {recursive:true, force:true})'
}
trap cleanup EXIT
cd "$root"
mkdir src
cat > rescript.json <<'JSON'
{"name":"watch-parse-warnings","sources":"src","warnings":{"error":"-a"}}
JSON
failed=0
for changed in A B; do
  rewatch clean > clean.log 2>&1
  printf 'let f = () => %%todo("persistent")\n\n\n\n\n' > src/A.res
  printf 'let value = 1\n' > src/B.res
  rewatch build > build.log 2>&1
  # A previous successful record exists. Change either the warning source or
  # an unrelated source, then start the watcher without cleaning.
  printf '// changed before watch\n' >> "src/$changed.res"
  rewatch_bg watch > watch.log 2>&1 &
  watcher_pid=$!
  if ! wait_for_pattern_count watch.log 'Finished .*compilation' 1 60; then
    cat watch.log
    exit 1
  fi
  initial_output=$(grep -c 'Todo found: persistent' watch.log || true)
  initial_log=$(grep -c 'Todo found: persistent' lib/rescript/.compiler.log || true)
  printf '// unrelated edit while watching\n' >> src/B.res
  if ! wait_for_pattern_count watch.log 'Finished .*compilation' 2 40; then
    cat watch.log
    exit 1
  fi
  total_output=$(grep -c 'Todo found: persistent' watch.log || true)
  rebuilt_output=$((total_output - initial_output))
  rebuilt_log=$(grep -c 'Todo found: persistent' lib/rescript/.compiler.log || true)
  echo "Changed $changed before watch: initial output/log=$initial_output/$initial_log; rebuild output/log=$rebuilt_output/$rebuilt_log"
  if [ "$initial_output/$initial_log/$rebuilt_output/$rebuilt_log" != '1/1/1/1' ]; then
    error "Parse warning must occur once in each build's output and compiler log"
    failed=1
  fi
  exit_watcher
  wait "$watcher_pid"
  watcher_pid=""
done
[ "$failed" -eq 0 ]
success "Changed and unchanged parse warnings survive incremental watch startup"
