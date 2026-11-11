#!/usr/bin/env bash
# Compare clean project builds; requires Python 3 and, unless disabled, Valgrind.
# Each compiler first builds the runtime (a base built before the flat
# lib/rescript layout reads the runtime's lib/ocaml sources, which that writes).
# Belt is compiled from source as a project dependency. Runtime preparation is
# outside the measured project build and its output digest.
# Uses disposable projects: clean/build modify outputs, the two package copies
# in .rescript-pkgs are replaced, and node_modules/@rescript/belt is relinked.
exec python3 "$(dirname "$0")/bench_project.py" "$@"
