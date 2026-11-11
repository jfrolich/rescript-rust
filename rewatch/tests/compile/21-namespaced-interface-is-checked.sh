#!/bin/bash

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: A namespaced implementation is checked against its interface"

# In-process builds register a namespaced interface as `A-Ns`. The check of
# `A.res` against `A.resi` looked the interface up as `A`, missed it, and
# skipped the check: mismatches compiled and every value counted as unused.

project=$(mktemp -d)
trap 'rm -r "$project"' EXIT
mkdir "$project/src"
cat > "$project/rescript.json" << 'JSON'
{
  "name": "namespaced-interface",
  "namespace": true,
  "sources": "src",
  "package-specs": { "module": "esmodule", "in-source": true },
  "suffix": ".res.js",
  "warnings": { "number": "+a" }
}
JSON
printf 'let used = 1\nlet hidden = 2\n' > "$project/src/A.res"
printf 'let x = A.used\n' > "$project/src/B.res"

printf 'let used: int\n' > "$project/src/A.resi"
output=$(cd "$project" && rewatch build 2>&1)
if [ $? -ne 0 ]; then
  error "A matching interface failed to build"
  printf "%s\n" "$output" >&2
  exit 1
fi
if echo "$output" | grep -q "unused value used"; then
  error "A value the interface exports was reported unused"
  printf "%s\n" "$output" >&2
  exit 1
fi
if ! echo "$output" | grep -q "unused value hidden"; then
  error "A value the interface hides was not reported unused"
  printf "%s\n" "$output" >&2
  exit 1
fi
success "Exported values count as used"

printf 'let used: string\n' > "$project/src/A.resi"
output=$(cd "$project" && rewatch build 2>&1)
if [ $? -eq 0 ]; then
  error "An implementation that does not match its interface built"
  printf "%s\n" "$output" >&2
  exit 1
fi
if ! echo "$output" | grep -q "Expected declaration"; then
  error "The interface mismatch was not reported"
  printf "%s\n" "$output" >&2
  exit 1
fi
success "Interface mismatch is reported"

printf 'let used: int\nlet missing: string\n' > "$project/src/A.resi"
output=$(cd "$project" && rewatch build 2>&1)
if [ $? -eq 0 ] || ! echo "$output" | grep -q "is required but not provided"; then
  error "A value missing from the implementation was not reported"
  printf "%s\n" "$output" >&2
  exit 1
fi
success "Missing value is reported"
