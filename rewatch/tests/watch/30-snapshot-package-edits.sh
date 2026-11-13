#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/../utils.sh"
repo=$(cd "$here/../../.." && pwd)
export REWATCH_EXECUTABLE=${REWATCH_EXECUTABLE:-$repo/rewatch/target/debug/rescript}
case "$REWATCH_EXECUTABLE" in
  *rescript-ocaml.exe|*rescript-ocaml.js)
    echo 'Runtime snapshots are a Rust build-system feature; not applicable to the OCaml executable.'
    exit 0
    ;;
esac
work=$(mktemp -d)
mkdir -p "$work/project/src" "$work/project/node_modules/@rescript"
cd "$work/project"
cat > rescript.json <<'JSON'
{"name":"snapshot-watch-test","sources":["src"],"dependencies":["@rescript/belt"],"package-specs":{"module":"esmodule","in-source":true},"suffix":".mjs"}
JSON
pid=''
trap 'if [[ -n $pid ]]; then kill "$pid" 2>/dev/null || true; wait "$pid" 2>/dev/null || true; fi' EXIT
for package in belt runtime touch; do
  for mode in snapshot off; do
    if [[ $package == touch && $mode == off ]]; then continue; fi
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
    export RESCRIPT_SNAPSHOT=require
    [[ $mode != off ]] || export RESCRIPT_SNAPSHOT=off
    rewatch clean > "$work/clean.log" 2>&1
    printf 'let value = Belt.Float.fromString("2.0")\nlet length = List.length(list{1, 2})\n' > src/Main.res
    "$REWATCH_EXECUTABLE" watch -v > "$work/$package-$mode.log" 2>&1 &
    pid=$!
    wait_for_file src/Main.mjs 60
    wait_for_pattern_count "$work/$package-$mode.log" 'Finished .*compilation' 1 60
    if [[ $mode == snapshot ]]; then
      if grep -q 'Not using the prebuilt' "$work/$package-$mode.log"; then
        cat "$work/$package-$mode.log"; exit 1
      fi
    fi
    if [[ $package == touch ]]; then
      touch node_modules/@rescript/belt/src/Belt_Array.res
    elif [[ $package == belt ]]; then
      python3 -c 'from pathlib import Path; p=Path("node_modules/@rescript/belt/src/Belt_Float.res"); p.write_text(p.read_text().replace("| i => Some(i)", "| i => Some(i +. 1.0)"))'
    else
      python3 -c 'from pathlib import Path; p=Path("node_modules/@rescript/runtime/Stdlib_List.res"); p.write_text(p.read_text().replace("let length = xs => lengthAux(xs, 0)", "let length = xs => lengthAux(xs, 1)"))'
    fi
    if [[ $package != touch ]]; then
      wait_for_pattern_count "$work/$package-$mode.log" 'Finished .*compilation' 2 60
    fi
    if [[ $package == touch ]]; then
      wait_for_pattern_count "$work/$package-$mode.log" 'Keeping the prebuilt @rescript/belt: its sources are unchanged' 1 60
      if grep -q 'Not using the prebuilt' "$work/$package-$mode.log"; then exit 1; fi
    elif [[ $mode == snapshot ]]; then
      grep -q "Not using the prebuilt @rescript/$package:.*rest of this watch session" "$work/$package-$mode.log"
    fi
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
    if grep -E 'Warning number|Syntax error|We.ve found a bug' "$work/$package-$mode.log"; then exit 1; fi
  done
  if [[ $package == touch ]]; then
    success 'Belt touch keeps the snapshot'
  else
    diff -r "$work/$package-snapshot" "$work/$package-off"
    success "$package watch output and diagnostics match from-source"
  fi
done
