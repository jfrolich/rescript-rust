#!/bin/bash
set -e
cd "$(dirname "$0")"
source "../utils.sh"
cd ../../testrepo/packages/with-ppx

bold "Test: External PPX configuration is rejected"
if output=$("$REWATCH_EXECUTABLE" build 2>&1); then
  error "Build unexpectedly accepted an external PPX"
  exit 1
fi
printf '%s\n' "$output" | grep -F "Package '@testrepo/with-ppx' has unsupported ppx-flags entry 'sury-ppx/bin': external PPXs are no longer supported"
success "External PPX rejected at configuration validation"

# The old wrong-magic parity case now rejects before the executable can run.
# It intentionally differs from OCaml, which still accepts external rewriters.
fixture="$(cd ../../../tests/fixtures/external-ppx && pwd)"
set +e
output=$("$REWATCH_EXECUTABLE" bsc -ppx "$fixture/ppx_wrong_magic.sh" "$fixture/Input.res" 2>&1)
status=$?
set -e
[ "$status" -eq 2 ]
[ "$output" = "External PPXs are no longer supported: $fixture/ppx_wrong_magic.sh" ]
success "Compiler helper rejects external PPX before running it"
