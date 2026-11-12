#!/usr/bin/env python3
"""Report disjoint environment operation costs from an env-shadow-profile run.

Build rewatch with --release --features rescript-compiler/env-shadow-profile,
then clean the project and run its build from its project directory with
RESCRIPT_ENV_SHADOW=1 RAYON_NUM_THREADS=1 under:
  valgrind --tool=callgrind --cache-sim=no --branch-sim=no \
    --callgrind-out-file=env.callgrind RESCRIPT build .

The feature suppresses nested shadow comparisons inside a measured operation.
Normal shadow mode does not suppress them. Incoming call-edge costs are
inclusive; entry points cannot nest, so these costs can be summed. Copies made
solely to feed both representations and equality checks sit outside entries.
Table copy-on-write preparation uses tag 128+operation and is added to the
write's cost. Tag 255 calibrates empty entry overhead, once per worker.
"""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
OPERATIONS = ROOT / "compiler-rust/tests/env_shadow_profile_operations.json"
ENTRY = re.compile(r"::env::profile::(table|log)_entry::<(\d+),")
COMPRESSED = re.compile(r"\((\d+)\)(?: (.*))?$")


def parse(text):
    names = {}
    calls, inclusive = Counter(), Counter()
    target = None
    pending = False
    positions = None
    events = None
    total = None
    for line in text.splitlines():
        if line.startswith("positions: "):
            positions = len(line.split()[1:])
        elif line.startswith("events: "):
            events = line.split()[1:]
            if events != ["Ir"]:
                raise ValueError("profile must collect only Ir")
        elif line.startswith("summary: "):
            if total is not None:
                raise ValueError("multiple profile parts are not supported")
            total = int(line.split()[1])
        elif line.startswith(("fn=", "cfn=")):
            value = line.split("=", 1)[1]
            match = COMPRESSED.fullmatch(value)
            if match:
                key = match[1]
                if match[2] is not None:
                    names[key] = match[2]
            else:
                key = value
                names[key] = value
            if line.startswith("cfn="):
                target = key
            else:
                target = None
        elif line.startswith("calls="):
            if target is None or pending:
                raise ValueError("call edge without a function or cost")
            calls[target] += int(line[6:].split()[0])
            pending = True
        elif line and line[0] in "0123456789+-*" and pending:
            if positions is None or events is None:
                raise ValueError("cost without positions/events")
            inclusive[target] += int(line.split()[positions])
            pending = False
    if pending or total is None or total <= 0:
        raise ValueError("incomplete profile")
    result = defaultdict(lambda: {"table": Counter(), "log": Counter()})
    for key, instructions in inclusive.items():
        name = names.get(key)
        if name is None:
            raise ValueError(f"undefined function id {key}")
        match = ENTRY.search(name)
        if not match:
            continue
        side, tag = match[1], int(match[2])
        operation = tag - 128 if 128 <= tag < 255 else tag
        chunk = "cow" if 128 <= tag < 255 else "body"
        result[operation][side]["instructions"] += instructions
        result[operation][side]["entry_calls"] += calls[key]
        result[operation][side][chunk + "_calls"] += calls[key]
    if not result or 255 not in result:
        raise ValueError("no calibrated environment entries (check the Cargo feature)")
    if sum(values[side]["instructions"] for values in result.values()
           for side in ("table", "log")) > total:
        raise ValueError("entry costs overlap or exceed the build total")
    return total, result


def summarize(text, operation_names):
    total, groups = parse(text)
    overhead = {}
    present = [side for side in ("table", "log") if groups[255][side]["entry_calls"]]
    folded = len(present) == 1
    if folded:
        # The two empty entry functions have identical bodies. LLVM can fold
        # them into one symbol; calibrate() calls each 10,000 times per worker.
        common = groups[255][present[0]]
        if common["entry_calls"] < 20_000 or common["entry_calls"] % 20_000:
            raise ValueError("incomplete folded calibration")
    for side in ("table", "log"):
        calibration = groups[255][present[0] if folded else side]
        if not calibration["entry_calls"]:
            raise ValueError(f"missing {side} calibration")
        overhead[side] = calibration["instructions"] / calibration["entry_calls"]
    rows = []
    for operation, sides in sorted(groups.items()):
        if operation == 255:
            continue
        if operation not in operation_names:
            raise ValueError(f"unknown operation {operation}")
        row = {"operation": operation_names[operation], "id": operation}
        for side in ("table", "log"):
            values = dict(sides[side])
            values["adjusted_instructions"] = max(0, values.get("instructions", 0)
                - overhead[side] * values.get("entry_calls", 0))
            row[side] = values
        row["paired"] = bool(sides["table"]["body_calls"] and sides["log"]["body_calls"])
        row["same_body_call_count"] = sides["table"]["body_calls"] == sides["log"]["body_calls"]
        rows.append(row)
    paired = [row for row in rows if row["paired"]]
    if not paired:
        raise ValueError("zero paired operations")
    return {
        "build_instructions": total,
        "empty_entry_instructions": overhead,
        "empty_entries_folded": folded,
        "paired_instructions": {
            side: sum(row[side]["adjusted_instructions"] for row in paired)
            for side in ("table", "log")
        },
        "operations": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    args = parser.parse_args()
    names = {value: name for name, value in json.loads(OPERATIONS.read_text()).items()}
    result = summarize(args.profile.read_text(), names)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
