#!/usr/bin/env bash
# Count the allocations of one clean build of a project.
#
#   scripts/perf/alloc_count.sh RESCRIPT_BIN PROJECT_DIR [SITES_FILE]
#
# RESCRIPT_BIN must be built with `--features alloc-stats`. Prints the totals
# and the size histogram. With SITES_FILE, also samples allocation sites into
# it; summarize them with scripts/perf/alloc_sites.py. Set RESCRIPT_RUNTIME as
# for any direct rewatch run. See scripts/perf/README.md.
set -euo pipefail

if [ $# -lt 2 ]; then
  sed -n '2,9p' "$0"
  exit 2
fi
bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
project=$2
sites=${3:+$(cd "$(dirname "$3")" && pwd)/$(basename "$3")}

cd "$project"
"$bin" clean >/dev/null 2>&1
if [ -n "$sites" ]; then
  export RESCRIPT_ALLOC_SITES=$sites
fi
report=$(RESCRIPT_ALLOC_COUNT=1 "$bin" build 2>&1 >/dev/null | grep '^ALLOCS' || true)
if [ -z "$report" ]; then
  echo "no allocation report: was $1 built with --features alloc-stats?" >&2
  exit 1
fi
echo "$report"
