#!/usr/bin/env bash
# Profile clean builds of a project and print the data-movement breakdown.
#
#   scripts/perf/profile_build.sh RESCRIPT_BIN PROJECT_DIR OUT_DIR [RUNS]
#
# Each run cleans PROJECT_DIR, records `RESCRIPT_BIN build` with samply at
# 4 kHz into OUT_DIR/run-N, and also times one unprofiled clean build so the
# breakdown can be shown in CPU seconds. Set RESCRIPT_RUNTIME as for any direct
# rewatch run. Build RESCRIPT_BIN with symbols, e.g.
#   CARGO_PROFILE_RELEASE_DEBUG=line-tables-only CARGO_PROFILE_RELEASE_STRIP=none \
#     cargo build --release --manifest-path rewatch/Cargo.toml
# To compare two binaries, profile both in the same batch on an idle machine.
set -euo pipefail

if [ $# -lt 3 ]; then
  sed -n '2,12p' "$0"
  exit 2
fi
bin=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
project=$2
out=$3
runs=${4:-2}
here=$(cd "$(dirname "$0")" && pwd)
samply=${SAMPLY:-samply}

mkdir -p "$out"
cd "$project"

cpu_total=0
for i in $(seq 1 "$runs"); do
  "$bin" clean >/dev/null 2>&1
  # time(1) reports on stderr after the build's own output; keep only its lines.
  timing=$( (/usr/bin/time -p "$bin" build >/dev/null) 2>&1 | grep -E '^(user|sys) ' )
  user=$(awk '/^user/ {print $2}' <<<"$timing")
  sys=$(awk '/^sys/ {print $2}' <<<"$timing")
  cpu_total=$(awk -v a="$cpu_total" -v u="$user" -v s="$sys" 'BEGIN {print a + u + s}')

  run="$out/run-$i"
  mkdir -p "$run"
  "$bin" clean >/dev/null 2>&1
  "$samply" record --save-only --unstable-presymbolicate --rate 4000 \
    -o "$run/prof.json.gz" -- "$bin" build >"$run/build.log" 2>&1
done

cpu=$(awk -v t="$cpu_total" -v n="$runs" 'BEGIN {printf "%.2f", t / n}')
echo "mean unprofiled CPU (user + sys): ${cpu}s over $runs run(s)"
dirs=()
for i in $(seq 1 "$runs"); do dirs+=("$out/run-$i"); done
python3 "$here/dod_breakdown.py" "${dirs[@]}" --cpu-seconds "$cpu" | tee "$out/breakdown.txt"
