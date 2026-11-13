#!/bin/bash
# Compare `rescript-tools doc`, which runs the build system's `rescript doc`,
# with the doc snapshots in src/expected: the OCaml `rescript-tools doc`
# output that test.sh writes. Exits 1 when a module's docs differ.
set -u
cd "$(dirname "$0")"

actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
status=0
for file in src/*.res src/*.resi; do
  expected="src/expected/$(basename "$file").json"
  if ! node ../../cli/rescript-tools.js doc "$file" > "$actual"; then
    printf "\033[0;31m❌ rescript-tools doc %s failed\033[0m\n" "$file"
    status=1
  elif ! diff -u "$expected" "$actual"; then
    printf "\033[0;31m❌ rescript-tools doc %s differs from %s\033[0m\n" "$file" "$expected"
    status=1
  fi
done
if [ "$status" = 0 ]; then
  printf "\033[0;32m✅ rescript-tools doc matches the doc snapshots.\033[0m\n"
fi
exit $status
