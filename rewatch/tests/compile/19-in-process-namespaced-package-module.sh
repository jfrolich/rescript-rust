#!/bin/bash

cd "$(dirname "$0")"
source "../utils.sh"
cd "../fixtures/in-process-namespaced-package-module"

bold "Test: In-process compilation resolves package module types through a namespace"

rewatch clean &> /dev/null
build_output=$(rewatch build --in-process 2>&1)
build_status=$?

if [ $build_status -eq 0 ]; then
  success "Namespaced first-class module built in-process"
else
  error "Namespaced first-class module failed to build in-process"
  printf "%s\n" "$build_output" >&2
  exit 1
fi
