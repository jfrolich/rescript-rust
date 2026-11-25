#!/bin/bash
# Instructions per iteration of each operation: cachegrind at N and at 0.
BIN=${1:-./target/release/checker-kernel}
N=1000000
count() { valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=/dev/null "$BIN" "$1" "$2" 2>&1 | sed -n 's/.*I *refs: *//p' | tr -d ','; }
for op in empty instance1 instance3 instance5 instance7 two_instance1 unify_ground1 two_instance3 unify_ground3 two_instance5 unify_fun5 unify_same var_instance3 bind_var3 apply7 generalize7 lookup_name lookup_binder bind_close; do
  zero=$(count "$op" 0)
  full=$(count "$op" $N)
  echo "$op $(( (full - zero) / N ))"
done
