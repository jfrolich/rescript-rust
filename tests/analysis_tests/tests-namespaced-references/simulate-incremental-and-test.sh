#!/bin/bash
set -e
# Simulate editor-written incremental CMTs, from the artifacts the watcher serves.
for artifact in src/MyModule1-MyNamespace src/MyModule2-MyNamespace MyNamespace; do
  node ../fetch-artifact.mjs "lib/bs/$artifact.cmt" "lib/bs/___incremental/$(basename "$artifact").cmt"
done
./test.sh
