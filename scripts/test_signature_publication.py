#!/usr/bin/env python3
"""Check P3a's same-build decode and worker-count determinism invariants."""
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
exe = Path(sys.argv[1] if len(sys.argv) > 1 else root / "rewatch/target/release/rescript").resolve()
project = root / "tests/tests"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"), RESCRIPT_COMPILER_COUNTERS="1")


def run(*args):
    result = subprocess.run([str(exe), *map(str, args)], env=env, capture_output=True, text=True, timeout=30)
    output = result.stdout + result.stderr
    if result.returncode:
        raise AssertionError(output)
    return output


def portable_interface(data):
    """The StoredCore's leading Option<PortablePersStruct>, byte for byte.

    JS metadata follows it and contains unordered maps. Do not compare that
    metadata's map iteration order as if it were a signature difference.
    """
    pos = 0

    def integer():
        nonlocal pos
        value = shift = 0
        while True:
            byte = data[pos]
            pos += 1
            value |= (byte & 127) << shift
            if byte < 128:
                return value
            shift += 7

    def blob():
        nonlocal pos
        length = integer()
        pos += length
        assert pos <= len(data)

    if integer():  # Some(PortablePersStruct)
        blob()  # name
        blob()  # filename
        if integer():
            blob()  # deprecation
        for _ in range(integer()):
            blob()  # CRC unit name
            if integer():
                for _ in range(16):
                    integer()
        integer()  # shareable
        blob()  # encoded main signature
        if integer():
            blob()  # encoded raw signature
        integer()  # fingerprint
    return data[:pos]


run("build", env["RESCRIPT_RUNTIME"])
snapshots = []
for workers in (1, 8):
    env["RAYON_NUM_THREADS"] = str(workers)
    run("clean", project)
    output = run("build", project)
    compiled = re.findall(r"Compiled (\d+) modules", output)
    assert compiled and int(compiled[-1]) > 0, output
    decodes = re.findall(r"published_signature_decodes=(\d+)", output)
    assert decodes and all(int(n) == 0 for n in decodes), output
    with sqlite3.connect(project / "lib/bs/rescript.sqlite") as db:
        snapshot = {name: portable_interface(data) for name, data in db.execute("SELECT module, data FROM interfaces")}
    assert snapshot, "build stored no interfaces"
    snapshots.append(snapshot)
    print(f"{workers} workers: compiled {compiled[-1]} modules; published_signature_decodes=0; {len(snapshot)} stored interfaces")
    second = run("build", project)
    assert not re.search(r"Compiled [1-9]\d* modules", second), second
    print(f"{workers} workers: edit-free second build compiled no modules")

assert snapshots[0].keys() == snapshots[1].keys()
different = [name for name in snapshots[0] if snapshots[0][name] != snapshots[1][name]]
assert not different, f"worker-dependent stored interfaces: {different}"
print("Stored interfaces are byte-identical with 1 and 8 workers")
