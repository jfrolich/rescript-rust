#!/bin/bash
# Compare `rescript-tools reanalyze`, which runs the build system's `rescript
# reanalyze`, with the reanalyze snapshots: the OCaml `rescript-tools
# reanalyze` output that each project's test.sh writes. Exits 1 when a report
# differs.
set -u
cd "$(dirname "$0")"

tools="$PWD/../../../cli/rescript-tools.js"
actual=$(mktemp)
trap 'rm -f "$actual"' EXIT
status=0

# check <project> <snapshot> <reanalyze options...>
check() {
  local project=$1 expected=$2
  shift 2
  if ! (cd "$project" && node "$tools" reanalyze "$@") > "$actual"; then
    printf "\033[0;31m❌ rescript-tools reanalyze %s failed in %s\033[0m\n" "$*" "$project"
    status=1
  elif ! diff -u "$project/$expected" "$actual"; then
    printf "\033[0;31m❌ rescript-tools reanalyze %s differs from %s\033[0m\n" "$*" "$project/$expected"
    status=1
  fi
}

check deadcode expected/deadcode.txt -config -debug -ci \
  -exclude-paths src/exception \
  -live-names globallyLive1 -live-names globallyLive2,globallyLive3 \
  -suppress src/ToSuppress.res
check deadcode expected/exception.txt -exception -ci \
  -suppress src -unsuppress src/exception
check termination expected/termination.txt -config -ci -debug

# The rescript-tools executable itself, where a build has put it next to
# rescript.exe, analyzes with the build system too.
tools_exe=$(node -e 'import(process.argv[1]).then(bins => console.log(bins.rescript_tools_exe))' "$PWD/../../../cli/common/bins.js")
if [ -x "$tools_exe" ]; then
  if ! (cd termination && "$tools_exe" reanalyze -config -ci -debug) > "$actual" \
    || ! diff -u termination/expected/termination.txt "$actual"; then
    printf "\033[0;31m❌ %s reanalyze differs from termination/expected/termination.txt\033[0m\n" "$tools_exe"
    status=1
  fi
fi

# The version needs no project.
if [ "$(cd / && node "$tools" reanalyze -version)" != "reanalyze version 2.22.0" ]; then
  printf "\033[0;31m❌ rescript-tools reanalyze -version outside a project failed\033[0m\n"
  status=1
fi

if [ "$status" = 0 ]; then
  printf "\033[0;32m✅ rescript-tools reanalyze matches the reanalyze snapshots.\033[0m\n"
fi
exit $status
