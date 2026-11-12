#!/bin/bash
# Without a running `rescript watch` there is no typed information: the
# editor tooling client (`rescript analysis`) says to start the watcher and
# exits with EX_UNAVAILABLE (69).
set -u
cd "$(dirname "$0")/tests"
rm -f lib/rescript-watch.addr
output=$(yarn rescript analysis definition "$PWD/src/Definition.res" 2 8 2>&1)
status=$?
if [ "$status" != 69 ] || [[ "$output" != *"start it with \`rescript watch\`"* ]]; then
  printf "\033[0;33m⚠️ Expected analysis to exit with 69 and ask for a watcher, got %s:\n%s\033[0m\n" "$status" "$output"
  exit 1
fi
printf "\033[0;32m✅ Analysis asks for a watcher when none runs.\033[0m\n"
