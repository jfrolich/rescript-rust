#!/bin/bash
# Link `bsc` and `res_parser_rust` to the `rescript` executable built in
# rewatch/target/<debug|release>. Invoked under those names, `rescript` runs the
# file-at-a-time commands of the compiler linked into it, which the parity
# scripts compare against the OCaml reference compiler.
#
# Usage: scripts/rust_compiler_links.sh [debug|release]

set -e
root=$(cd "$(dirname "$0")/.." && pwd -P)
dir="$root/rewatch/target/${1:-release}"
[[ -x "$dir/rescript" ]] || exit 0
for name in bsc res_parser_rust; do
    ln -sfn rescript "$dir/$name"
done
