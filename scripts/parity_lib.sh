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

# Called once before comparisons. The wrapper exports the built tool to its
# child suites, so a combined run builds it only once. Exact mode needs no Rust
# tool and retains byte-for-byte comparison.
parity_init_comparison() {
    PARITY_COMPARE_MODE="${PARITY_COMPARE_MODE:-exact}"
    echo "Comparison mode: $PARITY_COMPARE_MODE"
    if [[ "$PARITY_COMPARE_MODE" == reformat && -z "${PARITY_REFORMAT_BIN:-}" ]]; then
        local target="$PROJECT_ROOT/scripts/js-reformat/target"
        cargo build --locked --manifest-path "$PROJECT_ROOT/scripts/js-reformat/Cargo.toml" \
            --target-dir "$target" || return
        export PARITY_REFORMAT_BIN="$target/debug/js-reformat"
    fi
    export PARITY_COMPARE_MODE
}

# Write diagnostics to stdout for the caller's existing diff artifact. The
# normalizer accepts trees, so stage the pair with the same basename. Keeping
# the source paths in the diagnostic identifies either side of a parse error.
parity_compare_js() {
    local reference="$1" candidate="$2" status=0
    if [[ "${PARITY_COMPARE_MODE:-exact}" == exact ]]; then
        diff -u --text "$reference" "$candidate"
        return
    fi
    local temp name
    temp=$(mktemp -d) || return
    name=$(basename "$reference")
    if mkdir "$temp/reference" "$temp/candidate" &&
        cp "$reference" "$temp/reference/$name" && cp "$candidate" "$temp/candidate/$name"; then
        "$PARITY_REFORMAT_BIN" compare "$temp/reference" "$temp/candidate" \
            --split-file --drop-decoration-comments > "$temp/report" 2>&1 || status=$?
    else
        status=2
    fi
    if [[ "$status" -ne 0 ]]; then
        if [[ -f "$temp/report" ]]; then cat "$temp/report"; fi
        printf 'Reference: %s\nCandidate: %s\n' "$reference" "$candidate"
    fi
    find "$temp" -type f -delete
    find "$temp" -depth -type d -empty -delete
    return "$status"
}
