#!/usr/bin/env python3
"""Abort a debug build during persistence; require a full, correct recovery."""
import os
from pathlib import Path
import resource
import re
import shutil
import sqlite3
import signal
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
exe = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root / "rewatch/target/debug/rescript"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for source_runtime in (False, True):
    with tempfile.TemporaryDirectory(prefix="interrupted-store-") as tmp:
        project = Path(tmp)
        (project / "rescript.json").write_text('{"name":"interrupted-store","sources":["src"],"package-specs":[{"module":"esmodule","in-source":true,"suffix":".mjs"}]}')
        (project / "src").mkdir()
        (project / "src/A.res").write_text('let value = 42\n')
        (project / "src/B.res").write_text('let value = A.value\n')

        if source_runtime:
            runtime = project / "runtime"
            runtime.mkdir()
            for file in (root / "packages/@rescript/runtime").iterdir():
                if file.suffix in (".res", ".resi", ".json"):
                    shutil.copyfile(file, runtime / file.name)
            # Change the compatibility key without changing runtime behavior.
            with (runtime / "Primitive_int.res").open("a") as file:
                file.write("\n// Exercise source-fallback runtime cache recovery.\n")
            env["RESCRIPT_RUNTIME"] = str(runtime)

        def runtime_rows():
            with sqlite3.connect(project / "lib/rescript/rescript.sqlite") as conn:
                return conn.execute("SELECT count(*) FROM runtime_interfaces").fetchone()[0]

        def build(extra=None, succeeds=True):
            result = subprocess.run([str(exe), "-vv", "build", str(project)],
                                    env=env | (extra or {}), capture_output=True, text=True, timeout=30)
            output = result.stdout + result.stderr
            assert result.returncode == (0 if succeeds else -signal.SIGABRT), output
            return output

        assert "Compiled 2 modules" in build()
        expected = {p.relative_to(project): p.read_bytes() for p in project.rglob("*.mjs")}
        assert expected
        assert "Compiled 0 modules" in build()
        if source_runtime:
            assert runtime_rows() > 0
        for hook in ("RESCRIPT_TEST_ABORT_RECORD_WRITE", "RESCRIPT_TEST_ABORT_DURING_RECORD_WRITE",
                     "RESCRIPT_TEST_ABORT_AFTER_RECORD_MARKER"):
            # Keep this on the sparse incremental transaction path. Whole
            # records now use atomic image publication (tested separately).
            with (project / "src/A.res").open("a") as file:
                file.write("\n// Force a sparse edit.\n")
            aborted = build({hook: "interrupted-store"}, False)
            assert "Finished compilation" in aborted, aborted
            assert (project / "lib/rescript/rescript.sqlite.pending").exists()
            recovered = build()
            assert "Compiled 2 modules" in recovered, recovered
            actual = {p.relative_to(project): p.read_bytes() for p in project.rglob("*.mjs")}
            assert actual == expected
            assert not (project / "lib/rescript/rescript.sqlite.pending").exists()
            unchanged = build()
            assert "Compiled 0 modules" in unchanged
            if source_runtime:
                assert runtime_rows() > 0
                # A no-op skips the runtime entirely. Force project compilation
                # to verify that the recovered runtime is actually reused.
                reused = build({"RESCRIPT_FULL_BUILD": "1"})
                assert re.search(r"Loaded \d+ stored runtime interfaces", reused), reused
            print(f"source_runtime={source_runtime} {hook}: full recovery with identical JS, then zero-module incremental build")
