#!/bin/bash
# A project with no parent workspace owns the packages nested in it, also when
# they are linked from a node_modules above it: a build reports their warnings
# and applies their warning settings. An installed (node_modules) package
# stays quiet.

cd $(dirname $0)
source "../utils.sh"

bold "Test: Warnings of packages nested in the project are reported"

fixture=$(mktemp -d 2>/dev/null || mktemp -d -t rewatch-nested-warnings)
trap "rm -rf '$fixture'" EXIT

# package DIR NAME RESCRIPT_JSON_EXTRA MODULE
package() {
  mkdir -p "$fixture/$1/src"
  printf '{"name":"%s"}\n' "$2" > "$fixture/$1/package.json"
  printf '{"name":"%s","sources":"src","package-specs":{"module":"esmodule","in-source":true},"suffix":".mjs"%s}\n' \
    "$2" "$3" > "$fixture/$1/rescript.json"
  printf 'let value = () => {\n  let unusedIn%s = 1\n  2\n}\n' "$4" > "$fixture/$1/src/$4.res"
}

# The workspace has no rescript.json: webapp is the project.
printf '{"name":"root","private":true,"workspaces":["webapp","webapp/packages/*"]}\n' > "$fixture/package.json"
package webapp webapp ',"dependencies":["nested","quiet","installed"]' Webapp
package webapp/packages/nested nested '' Nested
package webapp/packages/quiet quiet ',"warnings":{"number":"-26"}' Quiet
package node_modules/installed installed '' Installed
ln -s ../webapp "$fixture/node_modules/webapp"
ln -s ../webapp/packages/nested "$fixture/node_modules/nested"
ln -s ../webapp/packages/quiet "$fixture/node_modules/quiet"

check() {
  local label=$1 stderr_output
  stderr_output=$(rewatch build 2>&1 1>/dev/null)
  if [ $? -ne 0 ]; then
    error "$label: build failed"
    printf "%s\n" "$stderr_output" >&2
    exit 1
  fi
  for name in Webapp Nested; do
    if ! echo "$stderr_output" | grep -qF "unused variable unusedIn$name."; then
      error "$label: expected the warning of $name"
      printf "%s\n" "$stderr_output" >&2
      exit 1
    fi
  done
  for name in Quiet Installed; do
    if echo "$stderr_output" | grep -qF "unusedIn$name"; then
      error "$label: expected no warning of $name"
      printf "%s\n" "$stderr_output" >&2
      exit 1
    fi
  done
  success "$label: warnings of nested packages are reported"
}

cd "$fixture/webapp"
check "Build"
# Not recompiled: the warnings are replayed.
check "Rebuild"
