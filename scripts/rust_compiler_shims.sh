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
write_shim() {
    local name=$1 command=$2
    rm -f "$dir/$name"
    printf '#!/bin/sh\nexec "%s/rescript" %s "$@"\n' "$dir" "$command" > "$dir/$name"
    chmod +x "$dir/$name"
}
write_shim bsc bsc
write_shim res_parser_rust res-parser
