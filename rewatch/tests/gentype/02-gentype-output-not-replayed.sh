#!/bin/bash
# GenType prints its notes to stdout (bsc's `Log_.info`), not as compiler
# warnings: a build shows a module's genType notes after its warnings, but
# neither the compiler log nor the warnings a later build replays for a
# module it does not recompile contain them. The module's real warning is
# still replayed.

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: GenType notes follow their module's warnings and are not replayed"

fixture=$(mktemp -d 2>/dev/null || mktemp -d -t rewatch-gentype-replay)
trap "rm -rf '$fixture'" EXIT

mkdir -p "$fixture/src"

cat > "$fixture/package.json" <<'EOF'
{
  "name": "rewatch-gentype-replay",
  "version": "0.0.1"
}
EOF

cat > "$fixture/rescript.json" <<'EOF'
{
  "name": "rewatch-gentype-replay",
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

cat > "$fixture/src/B.res" <<'EOF'
let y = A.x
EOF

cd "$fixture"

fail() {
  error "$1"
  printf "%s\n" "$2" >&2
  exit 1
}

output=$(rewatch build 2>&1 | sed 's/\x1b\[[0-9;]*m//g')
[ ${PIPESTATUS[0]} -eq 0 ] || fail "Clean build failed" "$output"

warning_line=$(printf "%s\n" "$output" | grep -n 'unused variable a' | head -1 | cut -d: -f1)
note_line=$(printf "%s\n" "$output" | grep -n 'Annotation payload is ignored' | head -1 | cut -d: -f1)
[ -n "$warning_line" ] || fail "Clean build did not show A's warning" "$output"
[ -n "$note_line" ] || fail "Clean build did not show A's genType note" "$output"
[ "$warning_line" -lt "$note_line" ] || fail "A's genType note preceded its warning" "$output"
[ "$(printf "%s\n" "$output" | grep -c 'Warning genType')" -eq 1 ] ||
  fail "The genType note was not shown exactly once" "$output"

log=lib/bs/.compiler.log
[ -f "$log" ] || fail "No compiler log" "$output"
grep -q 'unused variable a' "$log" || fail "The compiler log lacks A's warning" "$(cat "$log")"
if grep -q 'Warning genType' "$log"; then
  fail "The compiler log contains the genType note" "$(cat "$log")"
fi

# Recompile only B: A's warning is replayed, its genType note is not.
printf '\n// edit\n' >> src/B.res
output=$(rewatch build 2>&1 | sed 's/\x1b\[[0-9;]*m//g')
[ ${PIPESTATUS[0]} -eq 0 ] || fail "Rebuild failed" "$output"
printf "%s\n" "$output" | grep -q 'unused variable a' ||
  fail "The rebuild did not replay A's warning" "$output"
if printf "%s\n" "$output" | grep -q 'Warning genType'; then
  fail "The rebuild replayed A's genType note" "$output"
fi
if grep -q 'Warning genType' "$log"; then
  fail "The compiler log contains the genType note after the rebuild" "$(cat "$log")"
fi

success "GenType notes follow their warnings and are neither logged nor replayed"
