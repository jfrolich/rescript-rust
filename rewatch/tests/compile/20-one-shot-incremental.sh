#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
cd "../fixtures/in-process-namespaced-package-module"

bold "Test: One-shot in-process builds reuse clean modules"
rewatch clean &> /dev/null
rewatch build --in-process &> /dev/null
full_js=$(shasum lib/es6/src/*.mjs)
output=$(rewatch build --in-process 2>&1)
if [[ "$output" != *"Parsed 0 source files"* || "$output" != *"Compiled 0 modules"* ]]; then
  error "No-op build reparsed or recompiled modules"
  printf '%s\n' "$output" >&2
  exit 1
fi

touch src/Consumer.res
output=$(rewatch build --in-process 2>&1)
if [[ "$output" != *"Parsed 1 source files"* || "$output" != *"Compiled 1 modules"* ]]; then
  error "Leaf-only change reparsed or recompiled unrelated modules"
  printf '%s\n' "$output" >&2
  exit 1
fi
touch src/Provider.res
output=$(rewatch build --in-process 2>&1)
if [[ "$output" != *"Compiled 1 modules"* ]]; then
  error "Unchanged interface recompiled a dependent"
  printf '%s\n' "$output" >&2
  exit 1
fi
if [[ "$(shasum lib/es6/src/*.mjs)" != "$full_js" ]]; then
  error "Incremental JS differs from a clean full build"
  exit 1
fi
# A missing sidecar must fall back to parsing, without using stale dependency data.
deps_file=lib/ocaml/Consumer-InProcessNamespace.in-process-deps.json
if [[ ! -f "$deps_file" ]]; then
  error "Missing dependency sidecar after successful build"
  exit 1
fi
rm "$deps_file"
output=$(rewatch build --in-process 2>&1)
if [[ "$output" != *"Parsed 1 source files"* || "$output" != *"Compiled 0 modules"* ]]; then
  error "Missing dependency cache did not reparse its module"
  printf '%s\n' "$output" >&2
  exit 1
fi
rewatch clean &> /dev/null
rewatch build --in-process &> /dev/null
success "No-op, leaf-only and cache-miss builds are incremental"
