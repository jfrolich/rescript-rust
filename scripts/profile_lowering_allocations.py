"""Run under GDB against the debug compiler test executable.

  gdb -q -batch -ex 'source scripts/profile_lowering_allocations.py' TEST_BINARY

Only allocations between the test's entry/completion markers are attributed.
Import, warmup, validation and printing are excluded, exactly as in the tests.
The nearest BIR/Lambda source frame identifies the owner; full stacks retain
up to five such frames. No allocator or production compiler instrumentation.
"""
import collections
import json
import os
from pathlib import Path

import gdb

windows = []


class Allocation(gdb.Breakpoint):
    def stop(self):
        frame = gdb.newest_frame()
        stack = []
        while frame:
            name = frame.name() or ""
            location = frame.find_sal()
            filename = location.symtab.filename if location.symtab else ""
            if ("src/bir/" in filename or "src/lambda/" in filename) and "allocation_window" not in name:
                stack.append(f"{name} {filename.split('src/')[-1]}:{location.line}")
            frame = frame.older()
        assert stack, "allocation without a BIR/Lambda owner"
        windows[-1]["\n".join(stack[:5])] += 1
        return False


allocation = Allocation(
    "<allocation_counter::allocator::CountingAllocator as core::alloc::global::GlobalAlloc>::alloc",
    internal=True,
)
allocation.enabled = False


class Start(gdb.Breakpoint):
    def stop(self):
        windows.append(collections.Counter())
        allocation.enabled = True
        return False


class End(gdb.Breakpoint):
    def stop(self):
        allocation.enabled = False
        return False


Start("rescript_compiler::bir::lower::unit::tests::allocation_window_start", internal=True)
End("rescript_compiler::bir::lower::unit::tests::allocation_window_end", internal=True)
gdb.execute("set pagination off")
gdb.execute("run full_unit_allocation_boundary --nocapture --test-threads=1")
assert int(gdb.parse_and_eval("$_exitcode")) == 0, "allocation tests failed"
assert len(windows) == 8, "expected two measured widths for each of four tests"
# libtest runs these tests in alphabetical order with one test thread.
names = ["applications", "conditionals", "switches", "untagged"]
report = {}
for index, name in enumerate(names):
    samples = []
    for width, stacks in zip([1000, 10000], windows[2 * index:2 * index + 2]):
        owners = collections.Counter()
        for stack, count in stacks.items():
            owner = stack.split("\n")[0].rsplit(" ", 1)[1].rsplit(":", 1)[0]
            owners[owner] += count
        samples.append({"width": width, "count": sum(stacks.values()), "owners": owners, "stacks": stacks})
    assert samples[0]["count"] == samples[1]["count"], name
    report[name] = samples
output = Path(os.environ.get("PROFILE_ALLOCATIONS_OUT", "temp/lowering-allocation-sites.json"))
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(report, indent=2) + "\n")
columns = ["conditionals", "switches", "applications", "untagged"]
rows = set().union(*(report[name][1]["owners"] for name in columns))
rows = sorted(rows, key=lambda row: (-max(report[name][1]["owners"].get(row, 0) for name in columns), row))
print("Owner | " + " | ".join(columns))
for row in rows:
    print(row + " | " + " | ".join(str(report[name][1]["owners"].get(row, 0)) for name in columns))
