#!/bin/bash
# GenType prints its notes (`Log_.info`, "Warning genType") to bsc's stdout,
# which rescript-ocaml shows only for a compile that fails. A build that
# succeeds shows neither kind of note, on its first build or on a rebuild,
# and keeps them out of the compiler log; the module's real warning is still
# shown and replayed, and genType still writes its file.

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: A successful build shows no genType notes"

# The temporary fixture is left in place for inspection.
fixture=$(mktemp -d 2>/dev/null || mktemp -d -t rewatch-gentype-notes)

mkdir -p "$fixture/src"

cat > "$fixture/package.json" <<'EOF'
{
  "name": "rewatch-gentype-notes",
  "version": "0.0.1"
}
EOF

cat > "$fixture/rescript.json" <<'EOF'
{
  "name": "rewatch-gentype-notes",
  "sources": { "dir": "src" },
  "package-specs": { "module": "esmodule", "in-source": true },
  "suffix": ".res.js",
  "gentypeconfig": {},
  "warnings": { "number": "+27" }
}
EOF

# Warning 27 (unused `a`) and a genType note (an ignored `@genType` payload).
cat > "$fixture/src/A.res" <<'EOF'
let f = (~a) => ()
@genType(`x`) let x = 1
EOF

# A genType note: the implementation's annotation is ignored for the `.resi`.
cat > "$fixture/src/I.res" <<'EOF'
@genType let y = 2
EOF

cat > "$fixture/src/I.resi" <<'EOF'
let y: int
EOF

cat > "$fixture/src/B.res" <<'EOF'
let y = A.x + I.y
EOF

cd "$fixture"

fail() {
  error "$1"
  printf "%s\n" "$2" >&2
  exit 1
}

strip_ansi() { sed 's/\x1b\[[0-9;]*m//g'; }

# Build, failing the test with `$1` if the build fails; the output, without
# colours, is in `output`.
build() {
  if ! output=$(rewatch build 2>&1); then
    fail "$1" "$output"
  fi
  output=$(printf "%s\n" "$output" | strip_ansi)
}

expect_warning_without_notes() {
  printf "%s\n" "$output" | grep -q 'unused variable a' ||
    fail "$1 did not show A's warning" "$output"
  if printf "%s\n" "$output" | grep -q 'Warning genType'; then
    fail "$1 showed a genType note" "$output"
  fi
}

build "Clean build failed"
expect_warning_without_notes "The clean build"
[ -f src/A.gen.tsx ] || fail "GenType did not write A.gen.tsx" "$output"

log=lib/rescript/.compiler.log
[ -f "$log" ] || fail "No compiler log" "$output"
grep -q 'unused variable a' "$log" || fail "The compiler log lacks A's warning" "$(cat "$log")"

# Recompile only B: A's warning is replayed.
printf '\n// edit\n' >> src/B.res
build "Rebuild of B failed"
expect_warning_without_notes "The rebuild of B"

# Recompile A and I themselves.
printf '\n// edit\n' >> src/A.res
printf '\n// edit\n' >> src/I.res
build "Rebuild of A and I failed"
expect_warning_without_notes "The rebuild of A and I"

if grep -q 'Warning genType' "$log"; then
  fail "The compiler log contains a genType note" "$(cat "$log")"
fi

success "A successful build shows no genType notes and keeps its warnings"
