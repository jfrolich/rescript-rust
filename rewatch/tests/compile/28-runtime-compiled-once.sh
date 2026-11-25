#!/bin/bash
set -euo pipefail
# Copy the sources so the regression never cleans an installed runtime.
fixture=$(mktemp -d)
cp "$RESCRIPT_RUNTIME"/*.res "$RESCRIPT_RUNTIME"/*.resi "$RESCRIPT_RUNTIME/rescript.json" "$fixture/"
export RESCRIPT_RUNTIME="$fixture"
export RESCRIPT_COMPILER_COUNTERS=1
export RESCRIPT_BACKEND=check
export RESCRIPT_BACKEND_STATS="$fixture/reports"
mkdir "$RESCRIPT_BACKEND_STATS"
timeout 10 "$REWATCH_EXECUTABLE" build "$fixture" > "$fixture/build.log" 2>&1 || {
    cat "$fixture/build.log"
    exit 1
}
# The driver's main-signature census runs for each compiled implementation,
# not for loaded interfaces. Counting exports detects a second compile even
# if both invocations use exactly the same path and overwrite their reports.
grep -q 'exported_signatures units=113 ' "$fixture/build.log"
python3 - "$fixture/reports" <<'PY'
import json
import pathlib
import sys
units = {json.loads(p.read_text())["unit"] for p in pathlib.Path(sys.argv[1]).rglob("*.json")}
assert len(units) == 113, len(units)
assert all("/./" not in unit for unit in units)
print("runtime: 113 compile entries, 113 distinct normalized unit paths")
PY
