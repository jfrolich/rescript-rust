#!/usr/bin/env bash
# Compare clean project builds; requires Python 3 and, unless disabled, Valgrind.
# The runtime must first be built by each compiler to populate lib/ocaml sources.
# Belt is compiled from source as a project dependency. Runtime preparation is
# outside the measured project build and its output digest.
# Uses disposable projects: clean/build modify outputs, the two package copies
# in .rescript-pkgs are replaced, and node_modules/@rescript/belt is relinked.
exec python3 "$(dirname "$0")/bench_project.py" "$@"
