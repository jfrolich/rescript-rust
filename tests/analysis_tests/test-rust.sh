#!/bin/bash
# Run the analysis test files against the Rust editor analysis (`rescript
# analysis`, served by `rescript watch`) and compare, directive by directive,
# with the OCaml analysis snapshots. Prints a per-directive summary; exits 1
# when a directive the Rust analysis supports differs from its snapshot.
#
# Usage: test-rust.sh [project...]   (default: every analysis test project)
set -u
cd "$(dirname "$0")"

projects=("$@")
if [ ${#projects[@]} = 0 ]; then
  projects=(
    tests
    tests-generic-jsx-transform
    tests-incremental-typechecking
    tests-namespaced-references
    tests-sourcedirs-dependency
  )
fi

results=$(mktemp)
trap 'rm -f "$results"' EXIT
status=0
for project in "${projects[@]}"; do
  echo "== $project"
  (cd "$project" && ../with-watcher.sh node ../rust-analysis.mjs run "$results") || status=1
done
echo
node rust-analysis.mjs summary "$results" || status=1
exit $status
