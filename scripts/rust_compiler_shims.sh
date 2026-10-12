#!/bin/bash
# Write `bsc` and `res_parser_rust` wrappers next to the rescript executable in
# rewatch/target/<debug|release>. They run its hidden `rescript bsc` and
# `rescript res-parser` commands, so scripts that take a compiler executable
# path (RUST_BSC, RUST_PARSER) drive the compiler linked into rescript.
#
# Usage: scripts/rust_compiler_shims.sh [debug|release]

set -e
root=$(cd "$(dirname "$0")/.." && pwd -P)
dir="$root/rewatch/target/${1:-release}"
[[ -x "$dir/rescript" ]] || exit 0
# Concurrent callers (e.g. the fuzz workers, which each import difftest.py)
# may run a wrapper while another rewrites it, so an unchanged wrapper is left
# alone and a new one replaces the old by rename.
write_shim() {
    local name=$1 command=$2 content tmp
    content=$(printf '#!/bin/sh\nexec "%s/rescript" %s "$@"' "$dir" "$command")
    if [[ -x "$dir/$name" && ! -L "$dir/$name" && "$(cat "$dir/$name")" == "$content" ]]; then
        return
    fi
    tmp=$(mktemp "$dir/.$name.XXXXXX")
    printf '%s\n' "$content" > "$tmp"
    chmod +x "$tmp"
    mv -f "$tmp" "$dir/$name"
}
write_shim bsc bsc
write_shim res_parser_rust res-parser
