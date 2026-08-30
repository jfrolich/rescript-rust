#!/bin/bash
cd $(dirname $0)
source "../utils.sh"
cd ../../testrepo

bold "Test: Missing source folders abort package discovery"

error_output=$(rewatch clean 2>&1)
if [ $? -eq 0 ]; then
  success "Repo Cleaned"
else
  error "Error Cleaning Repo"
  printf "%s\n" "$error_output" >&2
  exit 1
fi

DEP01_CONFIG=packages/dep01/rescript.json

# Add a non-existent source folder to dep01's rescript.json.
node -e "
  const fs = require('fs');
  const config = JSON.parse(fs.readFileSync('$DEP01_CONFIG', 'utf8'));
  config.sources = [{dir: 'nonexistent-folder'}, config.sources];
  fs.writeFileSync('$DEP01_CONFIG', JSON.stringify(config, null, 2) + '\n');
"

# Source discovery must fail rather than returning a partial package graph that
# cleanup could mistake for deleted modules.
build_output=$(rewatch build 2>&1)
build_status=$?
if [ $build_status -eq 0 ]; then
  error "Build unexpectedly succeeded with a missing source folder"
  git checkout "$DEP01_CONFIG"
  exit 1
fi
success "Build aborted on missing source folder"

if printf "%s\n" "$build_output" | grep -q 'nonexistent-folder'; then
  success "Missing source folder error was reported"
else
  error "Missing source folder error was NOT reported"
  printf "%s\n" "$build_output" >&2
  git checkout "$DEP01_CONFIG"
  exit 1
fi

# Restore the valid config and verify a subsequent build recovers normally.
git checkout "$DEP01_CONFIG"
if ! rewatch build > /dev/null 2>&1; then
  error "Build did not recover after restoring the source folder config"
  exit 1
fi

if git diff --exit-code . > /dev/null 2>&1 && [ -z "$(git ls-files --others --exclude-standard .)" ]; then
  success "No leftover changes"
else
  error "Leftover changes detected"
  git diff .
  git ls-files --others --exclude-standard .
  exit 1
fi
