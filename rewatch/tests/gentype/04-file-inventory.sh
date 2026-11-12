#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
source ../utils.sh
fixture=$(mktemp -d)
mkdir -p "$fixture/src"
cd "$fixture"
printf '%s\n' '{"name":"gentype-file-inventory","sources":["src"],"gentypeconfig":{},"suffix":".mjs","package-specs":{"module":"esmodule","in-source":true}}' >rescript.json
printf '%s\n' '{"name":"gentype-file-inventory","version":"0.0.0"}' >package.json
mode=${1:-incremental}
if [ "$mode" = clean ]; then
    # The compiler unit wrapper counts zero file operations for Absent actions.
    # Check that a real build selects exactly that action for all 64 modules.
    mkdir -p counts/src
    cp rescript.json package.json counts/
    for i in $(seq 1 64); do printf 'type t = int\n' >"counts/src/M$i.res"; done
    RESCRIPT_PHASE_TIMINGS=1 timeout 10 "$REWATCH_EXECUTABLE" build counts >counts.log 2>&1
    grep -Eq 'phase=gentype_files ms=[0-9.]+ artifacts=64$' counts.log
    grep -q 'phase=gentype_file_no_match ms=0.000 artifacts=0' counts.log
    grep -q 'phase=gentype_file_write ms=0.000 artifacts=0' counts.log
fi
for module in Keep Gone Edited Missing; do printf '@genType type t = int\n' >"src/$module.res"; done
for module in Never Stale; do printf 'type t = int\n' >"src/$module.res"; done
# No store exists: discover and remove even a handwritten stale output.
printf 'handwritten stale\n' >src/Stale.gen.tsx
build() { timeout 10 "$REWATCH_EXECUTABLE" build >build.log 2>&1 || { cat build.log; exit 1; }; }
if [ "$mode" = watch ]; then
    "$REWATCH_EXECUTABLE" watch >watch.log 2>&1 & watcher=$!
    trap 'kill -TERM "$watcher" 2>/dev/null || true; wait "$watcher" || true' EXIT
    wait_for_pattern_count watch.log 'Finished .*compilation' 1 30
else
    build
fi
[ ! -f src/Stale.gen.tsx ]
[ ! -f src/Never.gen.tsx ]
cp src/Keep.gen.tsx expected
cp src/Edited.gen.tsx expected-edited
cp src/Missing.gen.tsx expected-missing
# File edits alone do not rebuild a module. Preserve today's lazy repair.
printf 'manual edit\n' >src/Edited.gen.tsx
rm src/Missing.gen.tsx
printf 'manual stale\n' >src/Stale.gen.tsx
if [ "$mode" = watch ]; then
    printf '\n// unrelated trigger\n' >>src/Never.res
    wait_for_pattern_count watch.log 'Finished .*compilation' 2 30
else
    build
fi
grep -q 'manual edit' src/Edited.gen.tsx
[ ! -f src/Missing.gen.tsx ]
grep -q 'manual stale' src/Stale.gen.tsx
if [ "$mode" = clean ]; then "$REWATCH_EXECUTABLE" clean >clean.log 2>&1; fi
# Actual recompilation must repair annotated outputs and remove stale ones.
printf 'type t = int\n' >src/Gone.res
for module in Keep Edited Missing Stale; do printf '\n// recompile\n' >>"src/$module.res"; done
if [ "$mode" = watch ]; then
    wait_for_pattern_count watch.log 'Finished .*compilation' 3 30
    timeout 30 bash -c 'until cmp -s expected-edited src/Edited.gen.tsx &&
        cmp -s expected-missing src/Missing.gen.tsx &&
        [ ! -f src/Gone.gen.tsx ] && [ ! -f src/Stale.gen.tsx ]; do sleep 0.1; done'
else
    build
fi
cmp expected src/Keep.gen.tsx
cmp expected-edited src/Edited.gen.tsx
cmp expected-missing src/Missing.gen.tsx
[ ! -f src/Gone.gen.tsx ]
[ ! -f src/Stale.gen.tsx ]
[ ! -f src/Never.gen.tsx ]
if [ "$mode" = watch ]; then
    kill -TERM "$watcher"; wait "$watcher" || true; trap - EXIT
fi
success "genType file inventory: $mode, stale outputs and manual edits"
