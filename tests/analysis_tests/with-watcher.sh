#!/bin/bash
# Run a command while `rescript watch` serves this project's typed artifacts.
#
# In-process builds write no .cmi/.cmt/.cmti files: editor tooling reads them
# from a running watcher, which announces itself in lib/rescript-watch.addr
# once its initial build has finished.
#
# Usage (from a test project directory): with-watcher.sh <command> [args...]
set -u

rm -f lib/rescript-watch.addr
yarn rescript watch > lib/watch-test.log 2>&1 &
watcher=$!

stop_watcher() {
  # The watcher exits when its lock file goes away.
  rm -f lib/rescript/watch.lock
  for _ in $(seq 1 100); do
    kill -0 "$watcher" 2> /dev/null || break
    sleep 0.1
  done
  kill "$watcher" 2> /dev/null || true
  rm -f lib/watch-test.log
}
trap stop_watcher EXIT

for _ in $(seq 1 600); do
  [ -f lib/rescript-watch.addr ] && break
  if ! kill -0 "$watcher" 2> /dev/null; then
    echo "rescript watch exited before serving artifacts:" >&2
    cat lib/watch-test.log >&2
    exit 1
  fi
  sleep 0.2
done
if [ ! -f lib/rescript-watch.addr ]; then
  echo "Timed out waiting for rescript watch:" >&2
  cat lib/watch-test.log >&2
  exit 1
fi

"$@"
