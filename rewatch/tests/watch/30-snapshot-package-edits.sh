#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/../utils.sh"
# Enabled by the implementation commit. Opt in to reproduce the baseline failure.
if [[ ${RESCRIPT_TEST_SNAPSHOT_WATCH:-0} != 1 ]]; then
  echo 'Snapshot watch regression pending implementation (RESCRIPT_TEST_SNAPSHOT_WATCH=1 to reproduce)'
  exit 0
fi
repo=$(cd "$here/../../.." && pwd)
export REWATCH_EXECUTABLE=${REWATCH_EXECUTABLE:-$repo/rewatch/target/debug/rescript}
work=$(mktemp -d)
mkdir -p "$work/project/src" "$work/project/node_modules/@rescript"
cd "$work/project"
cat > rescript.json <<'JSON'
{"name":"snapshot-watch-test","sources":["src"],"dependencies":["@rescript/belt"],"package-specs":{"module":"esmodule","in-source":true},"suffix":".mjs"}
JSON
pid=''
trap 'if [[ -n $pid ]]; then kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; fi' EXIT
for package in belt runtime; do
  for mode in snapshot off; do
    for name in belt runtime; do
      target="node_modules/@rescript/$name"
      mkdir -p "$target"
      cp "$repo/packages/@rescript/$name/"*.json "$target/"
      if [[ $name == belt ]]; then
        mkdir -p "$target/src"
        cp "$repo/packages/@rescript/belt/src/"*.res* "$target/src/"
      else
        cp "$repo/packages/@rescript/runtime/"*.res* "$target/"
      fi
    done
    export RESCRIPT_RUNTIME="$PWD/node_modules/@rescript/runtime"
    unset RESCRIPT_SNAPSHOT
    [[ $mode != off ]] || export RESCRIPT_SNAPSHOT=off
    rewatch clean > "$work/clean.log" 2>&1
    printf 'let value = Belt.Array.length([1, 2])\nlet length = List.length(list{1, 2})\n' > src/Main.res
    rewatch watch -v > "$work/$package-$mode.log" 2>&1 &
    pid=$!
    wait_for_file src/Main.mjs 60
    wait_for_pattern_count "$work/$package-$mode.log" 'Finished .*compilation' 1 60
    if [[ $mode == snapshot ]]; then
      ! grep -q 'Not using the prebuilt' "$work/$package-$mode.log"
    fi
    if [[ $package == belt ]]; then
      printf '\n// snapshot watch source edit\n' >> node_modules/@rescript/belt/src/Belt_Array.res
    else
      printf '\n// snapshot watch source edit\n' >> node_modules/@rescript/runtime/Stdlib_List.res
    fi
    wait_for_pattern_count "$work/$package-$mode.log" 'Finished .*compilation' 2 60
    exit_watcher
    wait "$pid"
    pid=''
    # Compare every generated JS file, including dependency outputs, at identical paths.
    find . -type f \( -name '*.mjs' -o -name '*.cjs' -o -name '*.js' \) -print | LC_ALL=C sort > "$work/files"
    mkdir -p "$work/$package-$mode"
    while IFS= read -r file; do
      mkdir -p "$work/$package-$mode/$(dirname "$file")"
      cp "$file" "$work/$package-$mode/$file"
    done < "$work/files"
    # Successful fixture must have no diagnostics in either mode.
    ! grep -E 'Warning number|Syntax error|We.ve found a bug' "$work/$package-$mode.log"
  done
  diff -r "$work/$package-snapshot" "$work/$package-off"
  success "$package watch output and diagnostics match from-source"
done
