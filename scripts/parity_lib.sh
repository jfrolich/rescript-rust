# Shared setup for the parity scripts; source it after setting PROJECT_ROOT
# and RUST_TARGET.
#
# The two compilers build separately:
#   - Rust: `rescript build --dump` compiles in process and writes the
#     intermediate representations of every module to a dump directory.
#   - OCaml: the hidden `rescript build-reference --bsc OCAML_BSC` runs the
#     file-backed build with the OCaml bsc, writing .ast/.cmi/.cmj files, so
#     the OCaml bsc can then recompile any single file.
# Only the OCaml side reads or writes .cmi files.

# The OCaml bsc: the dune build, or its copy in the platform npm package.
parity_default_ocaml_bsc() {
    local dune="$PROJECT_ROOT/_build/install/default/bin/bsc"
    if [[ -x "$dune" ]]; then
        echo "$dune"
    else
        echo "$PROJECT_ROOT/packages/@rescript/$("$PROJECT_ROOT/scripts/platform.sh")/bin/bsc.exe"
    fi
}

OCAML_BSC="${OCAML_BSC:-$(parity_default_ocaml_bsc)}"
RESCRIPT_CLI="${RESCRIPT_CLI:-$PROJECT_ROOT/rewatch/target/$RUST_TARGET/rescript}"
PARITY_RUNTIME="$PROJECT_ROOT/packages/@rescript/runtime"
PARITY_BELT="$PROJECT_ROOT/packages/@rescript/belt"

# The `name` of the rescript.json in directory $1.
parity_package_name() {
    python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["name"])' "$1/rescript.json"
}

# Build project $1 in process, writing dumps of kinds $3 (comma-separated
# `rescript build --dump` kinds) under directory $2. Returns non-zero when the
# build failed; dumps of the modules that compiled are still written.
parity_build_rust_dumps() {
    local project="$1" dump_dir="$2" kinds="$3"
    find "$dump_dir" -type f -delete 2>/dev/null || true
    mkdir -p "$dump_dir"
    # The runtime's lib/ocaml sources must exist before any project build.
    RESCRIPT_RUNTIME="$PARITY_RUNTIME" "$RESCRIPT_CLI" build "$PARITY_RUNTIME" >/dev/null 2>&1 || true
    RESCRIPT_RUNTIME="$PARITY_RUNTIME" "$RESCRIPT_CLI" build "$project" \
        --dump "$kinds" --dump-dir "$dump_dir"
}

# Build the runtime, Belt and project $1 with the OCaml bsc. Run after
# parity_build_rust_dumps: an in-process build by another compiler identity
# cleans the build folders this writes into.
parity_build_ocaml_reference() {
    local project="$1" status=0
    local dir
    for dir in "$PARITY_RUNTIME" "$PARITY_BELT" "$project"; do
        if [[ "$dir" == "$project" && ( "$project" == "$PARITY_RUNTIME" || "$project" == "$PARITY_BELT" ) ]]; then
            continue
        fi
        RESCRIPT_RUNTIME="$PARITY_RUNTIME" "$RESCRIPT_CLI" build-reference --bsc "$OCAML_BSC" "$dir" ||
            status=1
    done
    return $status
}

# The dump of kind $3 for source file $2 (absolute) of project $1, written by
# parity_build_rust_dumps into directory $4.
parity_dump_path() {
    local project="$1" source="$2" kind="$3" dump_dir="$4"
    echo "$dump_dir/$(parity_package_name "$project")/${source#$project/}.$kind"
}
