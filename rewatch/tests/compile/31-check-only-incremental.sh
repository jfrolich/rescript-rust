#!/bin/bash
set -eu
cd "$(dirname "$0")"
source ../utils.sh

bold "Test: check-only checks only what changed since the last build"
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT
# Every file below the project but the sources the test edits, with its content.
snapshot() {
  (cd "$1" && find . -type f ! -name '*.res' | LC_ALL=C sort | while read -r file; do cksum "$file"; done)
}
project="$work/project"
mkdir -p "$project/src"
cat > "$project/rescript.json" <<'JSON'
{"name":"check-only-incremental","sources":"src","package-specs":{"module":"esmodule","in-source":true}}
JSON
printf 'let value = 1\nlet other = "a"\n' > "$project/src/A.res"
printf 'let value = A.value + 1\n' > "$project/src/B.res"
printf 'let value = 2\n' > "$project/src/C.res"
timeout 10 "$REWATCH_EXECUTABLE" build "$project" > "$work/out" 2> "$work/err"
snapshot "$project" > "$work/built"

# Check the project, expecting the given status and "Compiled" line (a
# failed check prints none), the diagnostics of a check that reads no
# record, and no file written.
check() {
  local expected_status=$1 expected_compiled=$2 status=0 full_status=0
  timeout 10 "$REWATCH_EXECUTABLE" build "$project" --check-only > "$work/out" 2> "$work/err" || status=$?
  RESCRIPT_FULL_BUILD=1 timeout 10 "$REWATCH_EXECUTABLE" build "$project" --check-only \
    > "$work/full.out" 2> "$work/full.err" || full_status=$?
  [ "$status" -eq "$expected_status" ] && [ "$full_status" -eq "$expected_status" ]
  diff -u "$work/full.err" "$work/err"
  [ -z "$expected_compiled" ] || grep -qx "$expected_compiled" "$work/out" || { cat "$work/out"; return 1; }
  snapshot "$project" | diff -u "$work/built" -
}

check 0 'Compiled 0 modules'

# A change no other module reads is checked on its own.
printf 'let value = 3\n' > "$project/src/C.res"
check 0 'Compiled 1 module'
printf 'let value = 1\nlet other = 2\n' > "$project/src/A.res"
check 0 'Compiled 2 modules'

# A change another module reads is checked there too, and its error reported.
printf 'let value = "one"\nlet other = 2\n' > "$project/src/A.res"
timeout 10 "$REWATCH_EXECUTABLE" build "$project" --check-only > "$work/out" 2> "$work/err" && exit 1
grep -q 'src/B.res:1:' "$work/err"
check 1 ''

# A watcher building beside the check leaves JavaScript newer than the
# source, while the record still holds the interface of the last build.
touch "$project/src/A.js"
check 1 ''

# A warning recorded by the build is reported by checking its module again.
printf 'let value = 1\nlet other = "a"\n' > "$project/src/A.res"
printf 'let value = { let unused = 1; 2 }\n' > "$project/src/C.res"
timeout 10 "$REWATCH_EXECUTABLE" build "$project" > "$work/out" 2> "$work/build.err"
grep -q 'unused variable unused' "$work/build.err"
snapshot "$project" > "$work/built"
check 0 'Compiled 1 module'
diff -u "$work/build.err" "$work/err"
success "Check-only checks the changed modules and reports what a full check does"
