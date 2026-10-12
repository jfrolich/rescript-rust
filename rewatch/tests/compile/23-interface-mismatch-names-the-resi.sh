#!/bin/bash

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: An interface mismatch names the interface source file"

# The .cmi an interface is read from is a build artifact; errors name the
# .resi. A clean in-process build used to name `<project>/src/R.cmi`, and the
# file build `../ocaml/r.cmi`.

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
if ! echo "$output" | grep -Eq "does not match the interface .*/src/R\.resi:"; then
  error "The mismatch did not name src/R.resi"
  printf "%s\n" "$output" >&2
  exit 1
fi
if echo "$output" | grep -q "\.cmi"; then
  error "The error mentions a .cmi file"
  printf "%s\n" "$output" >&2
  exit 1
fi
success "Interface mismatch names src/R.resi"
