#!/bin/bash

cd "$(dirname "$0")"
source "../utils.sh"

bold "Test: A module cannot reach a package it may not use through another module's compile"

# Each worker caches the module views it builds for persistent units. A view
# of `Dep` built while compiling the `dep` package was reused by a later
# compile on the same worker whose package may not use `dep` (here: a
# dev-dependency used from a non-dev source), so whether `Dep` resolved
# depended on scheduling. One worker thread makes that order deterministic.

project=$(mktemp -d)
trap 'rm -r "$project"' EXIT
mkdir -p "$project/src" "$project/node_modules/dep/src"
cat > "$project/rescript.json" << 'JSON'
{
  "name": "root",
  "sources": "src",
  "package-specs": { "module": "esmodule", "in-source": true },
  "suffix": ".res.js",
  "dev-dependencies": ["dep"]
}
JSON
cat > "$project/node_modules/dep/rescript.json" << 'JSON'
{
  "name": "dep",
  "namespace": true,
  "sources": "src",
  "package-specs": { "module": "esmodule", "in-source": true },
  "suffix": ".res.js"
}
JSON
echo '{"name": "root"}' > "$project/package.json"
echo '{"name": "dep"}' > "$project/node_modules/dep/package.json"
echo 'let base = 7' > "$project/node_modules/dep/src/D1.res"
echo 'let twice = x => x * 2 + D1.base' > "$project/node_modules/dep/src/D2.res"
echo 'let fromDep = Dep.D2.twice(1)' > "$project/src/B.res"

output=$(cd "$project" && RAYON_NUM_THREADS=1 rewatch build 2>&1)
if [ $? -eq 0 ]; then
  error "A non-dev source built against a dev-dependency"
  printf "%s\n" "$output" >&2
  exit 1
fi
if echo "$output" | grep -q "The module or file Dep can't be found"; then
  success "The dev-dependency is not visible to a non-dev source"
else
  error "Expected Dep to be unresolvable"
  printf "%s\n" "$output" >&2
  exit 1
fi
