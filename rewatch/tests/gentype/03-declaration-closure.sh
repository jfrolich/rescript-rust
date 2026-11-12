#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
source ../utils.sh

# Leave the disposable fixture and logs available for failure diagnosis.
fixture=$(mktemp -d)
mkdir -p "$fixture/src"
cat > "$fixture/rescript.json" <<'JSON'
{"name":"gentype-closure","sources":["src"],"gentypeconfig":{},"package-specs":{"module":"esmodule","in-source":true},"suffix":".mjs"}
JSON
printf '{"name":"gentype-closure","version":"0.0.0"}\n' > "$fixture/package.json"
printf 'type t = {value: int}\n' > "$fixture/src/Dependency.res"
printf 'type t = Dependency.t\n' > "$fixture/src/Alias.res"
printf 'type t = string\n' > "$fixture/src/Unused.res"
cd "$fixture"
write_plain() { printf 'let id = (x: Alias.t) => x\n' > src/Output.res; }
write_annotated() { printf '@genType let id = (x: Alias.t) => x\n' > src/Output.res; }
build() { timeout 10 "$REWATCH_EXECUTABLE" build > "$1" 2>&1 || { cat "$1"; exit 1; }; }
clean() { timeout 10 "$REWATCH_EXECUTABLE" clean > clean.log 2>&1; }

# Snapshot checked against the base compiler's clean output. The unrelated
# module is also annotated for the first build, then excluded from the closure.
write_annotated
printf '@genType type t = string\n' > src/Unused.res
RAYON_NUM_THREADS=1 build oracle.log
cat > expected.gen.tsx <<'TS'
/* TypeScript file generated from Output.res by genType. */

/* eslint-disable */
/* tslint:disable */

import * as OutputJS from './Output.mjs';

import type {t as Alias_t} from './Alias.gen';

export const id: (x:Alias_t) => Alias_t = OutputJS.id as any;
TS
cmp expected.gen.tsx src/Output.gen.tsx
printf 'type t = string\n' > src/Unused.res
clean
RESCRIPT_COMPILER_COUNTERS=1 RAYON_NUM_THREADS=1 build clean-one.log
cmp expected.gen.tsx src/Output.gen.tsx
grep -q 'gentype_closure needed=3 total=4' clean-one.log
grep -q 'gentype annotated=false modules=2 declarations=2' clean-one.log
cp src/Output.mjs expected.mjs
mkdir expected-js
for output in src/*.mjs; do cp "$output" expected-js/; done
clean
RESCRIPT_VERIFY_GENTYPE_CLOSURE=1 RAYON_NUM_THREADS=8 build clean-eight.log
cmp expected.gen.tsx src/Output.gen.tsx
cmp expected.mjs src/Output.mjs
for output in src/*.mjs; do cmp "expected-js/$(basename "$output")" "$output"; done

# Nobody initially asks for Dependency or Alias's declarations. Adding the
# annotation must rebuild these unchanged dependencies, not just Output.
write_plain
clean
RESCRIPT_COMPILER_COUNTERS=1 build plain.log
grep -q 'gentype annotated=false modules=0 declarations=0' plain.log
[ ! -f src/Output.gen.tsx ]
if [ "${1:-}" = watch ]; then
    RESCRIPT_VERIFY_GENTYPE_CLOSURE=1 "$REWATCH_EXECUTABLE" watch > watch.log 2>&1 &
    watcher=$!
    trap 'kill -TERM "$watcher" 2>/dev/null || true; wait "$watcher" 2>/dev/null || true' EXIT
    wait_for_pattern_count watch.log 'Finished .*compilation' 1 30
    write_annotated
    wait_for_file src/Output.gen.tsx 30
    wait_for_pattern_count watch.log 'Finished .*compilation' 2 30
    cmp expected.gen.tsx src/Output.gen.tsx
    cmp expected.mjs src/Output.mjs
    # Grow the closure again by adding a dependency to an already annotated module.
    printf '\n@genType let second = (x: Unused.t) => x\n' >> src/Output.res
    wait_for_pattern_count watch.log 'Finished .*compilation' 3 30
    grep -q 'export const second' src/Output.gen.tsx
    cp src/Output.gen.tsx dependency-growth.gen.tsx
    kill -TERM "$watcher"
    wait "$watcher" || true
    trap - EXIT
    clean
    build dependency-growth-clean.log
    cmp dependency-growth.gen.tsx src/Output.gen.tsx
else
    write_annotated
    RESCRIPT_VERIFY_GENTYPE_CLOSURE=1 RESCRIPT_COMPILER_COUNTERS=1 build incremental.log
    cmp expected.gen.tsx src/Output.gen.tsx
    cmp expected.mjs src/Output.mjs
    # A following incremental build keeps the declarations available in the
    # database. Editing just Output must not needlessly recompile its imports.
    printf '\n// same interface\n' >> src/Output.res
    RESCRIPT_COMPILER_COUNTERS=1 build repeated.log
    cmp expected.gen.tsx src/Output.gen.tsx
    grep -q 'gentype annotated=false modules=0 declarations=0' repeated.log
    printf '\n@genType let second = (x: Unused.t) => x\n' >> src/Output.res
    build dependency-growth.log
    grep -q 'export const second' src/Output.gen.tsx
    cp src/Output.gen.tsx dependency-growth.gen.tsx
    clean
    build dependency-growth-clean.log
    cmp dependency-growth.gen.tsx src/Output.gen.tsx
fi
success "genType dependency closure: ${1:-incremental}, one/eight workers, output identity"
