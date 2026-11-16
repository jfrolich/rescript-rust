#!/bin/bash
# Compare `rescript-tools doc`, which runs the build system's `rescript doc`,
# with the doc snapshots in src/expected: the OCaml `rescript-tools doc`
# output that test.sh writes. Exits 1 when a module's docs differ.
set -u
cd "$(dirname "$0")"

red='\033[0;31m'
green='\033[0;32m'
reset='\033[0m'

tools="$PWD/../../cli/rescript-tools.js"
doc() {
  node "$tools" doc "$@"
}

actual=$(mktemp)
project=$(mktemp -d)
trap 'rm -f "$actual" "$project"/src/*.res "$project"/rescript.json; rmdir "$project/src" "$project"' EXIT
status=0
fail() {
  printf "${red}❌ %s${reset}\n" "$1"
  status=1
}

for file in src/*.res src/*.resi; do
  expected="src/expected/$(basename "$file").json"
  if ! doc "$file" > "$actual"; then
    fail "rescript-tools doc $file failed"
  elif ! diff -u "$expected" "$actual"; then
    fail "rescript-tools doc $file differs from $expected"
  fi
done

# A file named by its absolute path, from another directory.
if ! (cd / && doc "$OLDPWD/src/ModC.res" > "$actual") || ! diff -u src/expected/ModC.res.json "$actual"; then
  fail "rescript-tools doc <absolute path> differs from src/expected/ModC.res.json"
fi

# The rescript-tools executable itself, where a build has put it next to
# rescript.exe, documents with the build system too.
tools_exe=$(node -e 'import(process.argv[1]).then(bins => console.log(bins.rescript_tools_exe))' "$PWD/../../cli/common/bins.js")
if [ -x "$tools_exe" ]; then
  if ! "$tools_exe" doc src/ModC.res > "$actual" || ! diff -u src/expected/ModC.res.json "$actual"; then
    fail "$tools_exe doc differs from src/expected/ModC.res.json"
  fi
fi

# Failures exit with a status other than 0 and print no docs.
for file in src/Missing.res rescript.json; do
  if doc "$file" > "$actual" 2> /dev/null; then
    fail "rescript-tools doc $file should fail"
  elif [ -s "$actual" ]; then
    fail "rescript-tools doc $file printed docs"
  fi
done

# A namespace module aliases every module of its package, the one that
# aliases it included: that alias is documented once, without its items
# (the OCaml tool does not return here).
mkdir "$project/src"
echo '{"name": "self-alias", "namespace": "Ns", "sources": "src"}' > "$project/rescript.json"
printf '/** Doc of x. */\nlet x = 1\n' > "$project/src/Other.res"
echo 'module Me = Ns' > "$project/src/Self.res"
if ! (cd "$project" && doc src/Self.res > "$actual"); then
  fail "rescript-tools doc of a namespace alias failed"
elif [ "$(grep -c '"id": "Self-Ns.Me.Other.x"' "$actual")" != 1 ] \
  || [ "$(grep -c '"id": "Self-Ns.Me.Self' "$actual")" != 1 ]; then
  fail "rescript-tools doc of a namespace alias printed unexpected docs"
  cat "$actual"
fi

# Items of an `include` are placed where their declaration is in the
# current source, also after an edit that moves the declaration and keeps
# the interface, so that a build recompiles the declaring module (B) but not
# the module that includes it (C): C's recorded interface then still holds
# B's declarations as B was before the edit.
reexport=$(mktemp -d)
cleanup_reexport() {
  case "$reexport" in
    "${TMPDIR:-/tmp}"*|/tmp/*|/var/folders/*) rm -r -- "$reexport" ;;
  esac
}
mkdir "$reexport/src"
echo '{"name": "reexport", "sources": "src"}' > "$reexport/rescript.json"
printf 'let f = () => 1\n/** The x. */\nlet x = 1\n' > "$reexport/src/B.res"
printf 'include B\n' > "$reexport/src/C.res"
printf 'include C\n' > "$reexport/src/T.res"
x_line() {
  grep -A8 '"id": "T.x"' "$actual" | grep -o '"line": [0-9]*' | head -1
}
rescript_cli="$PWD/../../cli/rescript.js"
rescript() {
  node "$rescript_cli" "$@"
}
if ! (cd "$reexport" && rescript build > /dev/null && doc src/T.res > "$actual"); then
  fail "rescript-tools doc of an included module failed"
elif [ "$(x_line)" != '"line": 3' ]; then
  fail "rescript-tools doc placed an included item at $(x_line), not line 3"
  cat "$actual"
fi
printf 'let f = () => {\n  let a = [1, 2]\n  a->Array.length\n}\n\n/** The x. */\nlet x = 1\n' > "$reexport/src/B.res"
# Without a build since the edit, then after one.
for step in edited built; do
  if [ "$step" = built ] && ! (cd "$reexport" && rescript build > /dev/null); then
    fail "rescript build after the edit failed"
  elif ! (cd "$reexport" && doc src/T.res > "$actual"); then
    fail "rescript-tools doc of an included module failed ($step)"
  elif [ "$(x_line)" != '"line": 7' ]; then
    fail "rescript-tools doc placed an included item at $(x_line), not line 7 ($step)"
    cat "$actual"
  fi
done
cleanup_reexport

if [ "$status" = 0 ]; then
  printf "${green}✅ rescript-tools doc matches the doc snapshots.${reset}\n"
fi
exit $status
