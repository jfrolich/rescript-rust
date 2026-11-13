#!/bin/bash

set -e

unset CLICOLOR_FORCE

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <rewatch executable>"
  exit 1
fi

REWATCH_EXECUTABLE="$(realpath "$1")"
export REWATCH_EXECUTABLE

# Make sure we are in the right directory
cd $(dirname $0)

if [[ "$REWATCH_EXECUTABLE" == */cli/rescript.js ||
  "$REWATCH_EXECUTABLE" == */cli/rescript-ocaml.js ]]; then
  echo "Using rewatch CLI script: $REWATCH_EXECUTABLE"
else
  echo "Using rewatch executable: $REWATCH_EXECUTABLE"
  eval $(node ./get_bin_paths.js)
  export RESCRIPT_RUNTIME
  echo Using runtime path: $RESCRIPT_RUNTIME
fi

source ./utils.sh

bold "Check for stale rescript processes"
STALE_PIDS=$(ps aux | grep "$REWATCH_EXECUTABLE" | grep -v grep | awk '{print $2}')
if [ -n "$STALE_PIDS" ]; then
  error "Found stale rescript processes using this executable:"
  ps aux | grep "$REWATCH_EXECUTABLE" | grep -v grep
  exit 1
fi
success "No stale rescript processes found"

# The published ReScript versions model dependency layouts; compilation uses
# the repository-built compiler and runtime. See ../testrepo/README.md.
bold "Yarn install"
(cd ../testrepo && yarn)
node ./add-belt-dependencies.mjs

bold "Rescript version"
(cd ../testrepo && ./node_modules/.bin/rescript --version)

# we need to reset the yarn.lock and package.json to the original state
# so there is not diff in git. The CI will install new ReScript package
bold "Reset package.json and yarn.lock"
git restore --worktree -- ../testrepo/yarn.lock ../testrepo/package.json &> /dev/null
success "Reset package.json and yarn.lock"

bold "Make sure the testrepo is clean"
if git diff --exit-code ../testrepo &> diff.txt;
then
  rm diff.txt
  success "Testrepo has no changes"
else
  error "Testrepo is not clean to start with"
  cat diff.txt
  rm diff.txt
  exit 1
fi

# Individual test files
# Comment out any test to skip it

# Compile tests
./compile/01-basic-compile.sh &&
./compile/02-standalone-package.sh &&
./compile/03-rename-file.sh &&
./compile/04-rename-file-internal-dep.sh &&
./compile/05-rename-file-namespace.sh &&
./compile/06-rename-interface-file.sh &&
./compile/07-rename-file-with-interface.sh &&
./compile/08-remove-file.sh &&
./compile/09-dependency-cycle.sh &&
./compile/10-duplicate-module-name.sh &&
./compile/11-dev-dependency-non-dev-source.sh &&
./compile/12-compile-dev-dependencies.sh &&
./compile/13-no-infinite-loop-with-cycle.sh &&
./compile/17-prod-flag.sh &&
./compile/18-external-dep-uncurried-dot.sh &&
./compile/19-in-process-namespaced-package-module.sh &&
./compile/19-utf8-warning.sh &&
./compile/20-schedule-independent-modules-after-error.sh &&
./compile/21-namespaced-interface-is-checked.sh &&
./compile/22-worker-store-respects-package-visibility.sh &&
./compile/23-interface-mismatch-names-the-resi.sh &&
./compile/21-rebuild-dependency-for-package-specs.sh &&
./compile/22-qualified-own-namespace-dependency.sh &&
./compile/23-root-source-dir-rebuild.sh &&
./compile/24-location-free-retry.sh &&
./compile/27-warning-build-modes.sh &&
./compile/28-runtime-compiled-once.sh &&
./compile/29-otel-console-verbosity.sh &&
./compile/30-nested-package-warnings.sh &&
./compile/25-deterministic-records.sh &&
./compile/26-external-ppx-rejected.sh &&
./compile/14-no-testrepo-changes.sh &&
# After 14, which builds the testrepo again: 17 ends with a clean, and
# check-only requires an unchanged, built testrepo.
./compile/26-check-only.sh &&
./compile/15-no-new-files.sh &&
./compile/16-snapshots-unchanged.sh &&

# GenType tests
./gentype/01-gentype-project-root.sh &&
./gentype/02-gentype-notes-not-shown.sh &&
./gentype/03-declaration-closure.sh &&
./gentype/04-file-inventory.sh clean &&
./gentype/04-file-inventory.sh incremental &&
./gentype/04-file-inventory.sh watch &&

# Watch tests
./watch/30-snapshot-package-edits.sh &&
./watch/11-gentype-declaration-closure.sh &&
./watch/01-watch-recompile.sh &&
./watch/02-watch-warnings-persist.sh &&
./watch/18-incremental-start-parse-warnings.sh &&
./watch/02-watch-warnings-persist-atomic-save.sh &&
./watch/03-watch-new-file.sh &&
./watch/04-watch-config-change.sh &&
./watch/05-watch-ignores-non-source.sh &&
./watch/06-watch-missing-source-folder.sh &&
./watch/07-changed-interface-after-failed-implementation.sh &&
./watch/08-watch-inlined-value-change.sh &&
./watch/08-watch-overlapping-source-removed.sh &&
./watch/09-watch-recovers-from-invalid-config.sh &&
./watch/10-watch-recovers-new-dependency-config.sh &&

# Lock tests
./lock/01-lock-when-watching.sh &&

# Suffix tests
./suffix/01-custom-suffix.sh &&

# Format tests
./format/01-format-all-files.sh &&
./format/02-format-single-file.sh &&
./format/03-format-stdin.sh &&
./format/04-format-current-project.sh &&
./format/05-format-line-endings.sh &&

# Clean tests
./clean/01-clean-single-project.sh &&
./clean/02-clean-dev-dependencies.sh &&
./clean/03-clean-node-modules.sh &&
./clean/04-clean-rebuild-no-compiler-update.sh &&
./clean/05-clean-invalid-module-graph.sh &&
./clean/06-clean-duplicate-names-across-packages.sh &&

# Experimental tests
./experimental/01-experimental-features-emit.sh &&
./experimental/02-experimental-features-parse-error.sh &&
./experimental/03-watch-invalid-experimental.sh &&

# Experimental-invalid tests
./experimental-invalid/01-invalid-experimental-key.sh &&

# Features tests
./features/01-features-default-all-active.sh &&
./features/02-features-cli-restricts-to-one.sh &&
./features/03-features-transitive-expansion.sh &&
./features/04-features-toggle-cleans-artifacts.sh &&
./features/05-features-cycle-errors.sh &&
./features/06-features-empty-flag-rejected.sh &&

# Compiler-args tests
./compiler-args/01-compiler-args-cwd-invariant.sh &&
./compiler-args/02-warnings-in-parser-and-compiler.sh
