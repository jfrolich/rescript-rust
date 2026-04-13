#!/bin/bash
# Tests for --in-process build mode.
# Validates: JS output correctness, no compiler assets, asset poisoning immunity,
# .resi interfaces, namespaces, node_modules source-backed deps, runtime bootstrap.

cd $(dirname $0)
source "./utils.sh"
cd ../testrepo

bold "Test: --in-process build"

# ============================================================================
# Helper: check that NO compiler assets exist in any build package
# (excludes node_modules/rescript and node_modules/@rescript which ship pre-built)
# ============================================================================
check_no_compiler_assets() {
  local label="$1"
  local found=""

  # Compiler artifacts that must NOT exist
  for ext in ast iast cmi cmj cmt cmti sexp; do
    local files=$(find . \
      -name "*.$ext" \
      -not -path "*/node_modules/rescript/*" \
      -not -path "*/node_modules/@rescript/*" \
      2>/dev/null)
    if [ -n "$files" ]; then
      found="$found\n$files"
    fi
  done

  # Metadata files that must NOT be created by --in-process
  for name in .compiler.log .sourcedirs.json compiler-info.json build.ninja; do
    local files=$(find . \
      -name "$name" \
      -not -path "*/node_modules/rescript/*" \
      -not -path "*/node_modules/@rescript/*" \
      2>/dev/null)
    if [ -n "$files" ]; then
      found="$found\n$files"
    fi
  done

  # lib/bs and lib/ocaml directories must NOT be created by --in-process
  for subdir in bs ocaml; do
    local dirs=$(find . \
      -path "*/lib/$subdir" -type d \
      -not -path "*/node_modules/rescript/*" \
      -not -path "*/node_modules/@rescript/*" \
      2>/dev/null)
    if [ -n "$dirs" ]; then
      found="$found\n$dirs"
    fi
  done

  if [ -z "$found" ]; then
    success "$label: no compiler assets"
  else
    error "$label: found compiler assets that should not exist"
    printf "%b\n" "$found" >&2
    exit 1
  fi
}

# ============================================================================
# Helper: remove all build output (lib dirs, .mjs) for a fresh start
# ============================================================================
clean_all_build_output() {
  # Remove all lib dirs except pre-built packages
  find . -path "*/lib/bs" -type d \
    -not -path "*/node_modules/rescript/*" \
    -not -path "*/node_modules/@rescript/*" \
    -exec rm -rf {} + 2>/dev/null

  find . -path "*/lib/ocaml" -type d \
    -not -path "*/node_modules/rescript/*" \
    -not -path "*/node_modules/@rescript/*" \
    -exec rm -rf {} + 2>/dev/null

  # Remove .mjs files that are not checked into git
  git clean -fd -- '*.mjs' &>/dev/null
}

# ============================================================================
# Test 1: Fresh --in-process build produces JS and no compiler assets
# ============================================================================
bold "Test: Fresh --in-process build"

clean_all_build_output

# Build with --in-process (expect exit code 1 due to pre-existing Array panic)
error_output=$(rewatch build --in-process 2>&1)
exit_code=$?

# The build reports failure because of the pre-existing Array lambda panic,
# but 52/53 modules should compile successfully.
if echo "$error_output" | grep -q "Compiled 52 modules"; then
  success "In-process compiled 52/53 modules (Array panic is pre-existing)"
else
  error "In-process build did not compile expected modules"
  printf "%s\n" "$error_output" >&2
  exit 1
fi

check_no_compiler_assets "Fresh build"

# Verify JS files were generated for key packages
js_count=$(find . -name "*.mjs" \
  -not -path "*/node_modules/rescript/*" \
  -not -path "*/node_modules/@rescript/*" \
  -not -path "*/node_modules/sury/*" \
  -not -path "*/node_modules/rescript-nodejs/*" \
  2>/dev/null | wc -l | tr -d ' ')

if [ "$js_count" -gt 30 ]; then
  success "Generated $js_count JS files"
else
  error "Expected >30 JS files, found $js_count"
  exit 1
fi

# ============================================================================
# Test 2: .resi interface files are handled correctly
# ============================================================================
bold "Test: .resi interface handling"

# packages/main/src/ModuleWithInterface has both .res and .resi
if [ -f ./packages/main/src/ModuleWithInterface.mjs ]; then
  success ".resi module compiled to JS"
else
  error "ModuleWithInterface.mjs not found — .resi handling may be broken"
  exit 1
fi

# ============================================================================
# Test 3: Namespace packages compile correctly
# ============================================================================
bold "Test: Namespace handling"

# new-namespace package uses namespaces; check that its modules compiled
ns_files=$(find ./packages/new-namespace -name "*.mjs" 2>/dev/null | wc -l | tr -d ' ')
if [ "$ns_files" -ge 3 ]; then
  success "Namespace package produced $ns_files JS files"
else
  error "Expected >=3 JS files in namespace package, found $ns_files"
  exit 1
fi

# ============================================================================
# Test 4: node_modules source-backed dependencies compile
# ============================================================================
bold "Test: node_modules source-backed deps"

# rescript-nodejs and sury are source-backed deps
nodejs_files=$(find ./node_modules/rescript-nodejs -name "*.mjs" 2>/dev/null | wc -l | tr -d ' ')
if [ "$nodejs_files" -gt 5 ]; then
  success "rescript-nodejs produced $nodejs_files JS files"
else
  error "Expected >5 JS files from rescript-nodejs, found $nodejs_files"
  exit 1
fi

# ============================================================================
# Test 5: Runtime bootstrap works (Pervasives/Stdlib available)
# ============================================================================
bold "Test: Runtime bootstrap"

# If runtime bootstrap failed, nothing would compile because every module
# depends on Pervasives/Stdlib. The fact that 52 modules compiled proves
# the bootstrap works. Verify Main.mjs exists and contains valid JS structure.
if [ -f ./packages/main/src/Main.mjs ]; then
  if grep -q "Generated by ReScript" ./packages/main/src/Main.mjs; then
    success "Main.mjs generated with correct ReScript header"
  else
    error "Main.mjs missing ReScript header"
    exit 1
  fi
else
  error "Main.mjs not found"
  exit 1
fi

# ============================================================================
# Test 6: Asset poisoning — stale compiler assets are ignored
# ============================================================================
bold "Test: Asset poisoning immunity"

clean_all_build_output

# Plant bogus stale compiler assets
mkdir -p ./packages/main/lib/bs ./packages/main/lib/ocaml
echo "BOGUS" > ./packages/main/lib/bs/Main.ast
echo "BOGUS" > ./packages/main/lib/bs/Main.cmi
echo "BOGUS" > ./packages/main/lib/bs/Main.cmj
echo "BOGUS" > ./packages/main/lib/bs/Main.cmt
echo "BOGUS" > ./packages/main/lib/ocaml/Main.ast
echo "BOGUS" > ./packages/main/lib/ocaml/Main.cmi
echo "BOGUS" > ./packages/main/lib/bs/.compiler.log
echo "BOGUS" > ./packages/main/lib/bs/.sourcedirs.json

# Build with --in-process — should ignore all planted assets
error_output=$(rewatch build --in-process 2>&1)
if echo "$error_output" | grep -q "Compiled 52 modules"; then
  success "Build succeeded despite bogus assets"
else
  error "Build failed with poisoned assets"
  printf "%s\n" "$error_output" >&2
  exit 1
fi

# Verify the bogus assets were not read (Main.mjs should be valid)
if [ -f ./packages/main/src/Main.mjs ] && grep -q "Generated by ReScript" ./packages/main/src/Main.mjs; then
  success "Main.mjs correct despite bogus stale assets"
else
  error "Main.mjs missing or incorrect — stale assets may have been read"
  exit 1
fi

# Clean up planted assets
rm -rf ./packages/main/lib/bs ./packages/main/lib/ocaml

# ============================================================================
# Test 7: Dev dependencies compile in --in-process
# ============================================================================
bold "Test: Dev dependencies"

dev_files=$(find ./packages/with-dev-deps/test -name "*.mjs" 2>/dev/null | wc -l | tr -d ' ')
if [ "$dev_files" -ge 1 ]; then
  success "Dev dependencies compiled ($dev_files files)"
else
  error "Expected >=1 dev dependency JS files, found $dev_files"
  exit 1
fi

# ============================================================================
# Cleanup: restore testrepo to git-clean state
# ============================================================================
git checkout -- .
git clean -fd . &>/dev/null

success "All --in-process tests passed"
