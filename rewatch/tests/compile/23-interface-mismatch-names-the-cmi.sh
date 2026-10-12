#!/bin/bash

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: An interface mismatch names the interface the file build reports"

# On a clean in-process build the interface's .cmi is not written yet when the
# implementation is checked, and the error named `<project>/src/R.cmi`. The
# file build reports the `lib/ocaml` copy relative to `lib/bs`:
# `../ocaml/r.cmi` (uncapitalised where the filesystem ignores case).

project=$(mktemp -d)
trap 'rm -r "$project"' EXIT
mkdir "$project/src"
cat > "$project/rescript.json" << 'JSON'
{
  "name": "interface-mismatch-name",
  "sources": "src",
  "package-specs": { "module": "esmodule", "in-source": true },
  "suffix": ".res.js"
}
JSON
printf 'let a = 1\n' > "$project/src/R.res"
printf 'let a: int\nlet b: int\n' > "$project/src/R.resi"

output=$(cd "$project" && rewatch build 2>&1)
if [ $? -eq 0 ]; then
  error "An implementation missing a value built"
  printf "%s\n" "$output" >&2
  exit 1
fi
if ! echo "$output" | grep -Eq "does not match the interface \.\./ocaml/[rR]\.cmi:"; then
  error "The mismatch did not name ../ocaml/r.cmi"
  printf "%s\n" "$output" >&2
  exit 1
fi
success "Interface mismatch names ../ocaml/r.cmi"
