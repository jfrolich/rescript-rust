# Shared setup for the output parity scripts; source it after setting
# PROJECT_ROOT and RUST_TARGET.
#
# The OCaml reference build is the hidden `rescript build-reference --bsc
# OCAML_BSC`: the file-backed build with the OCaml bsc, writing .ast/.cmi/.cmj
# files, so the OCaml bsc can then recompile any single file.

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

# Build the runtime, Belt and project $1 with the OCaml bsc. Run it after any
# in-process build of the same folders: a build by another compiler identity
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
