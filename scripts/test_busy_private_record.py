#!/usr/bin/env python3
"""Force SQLite busy using a second process's fcntl lock; require bounded fallback.

On Linux flock and fcntl are independent. lockf here uses fcntl(F_SETLK),
conflicting with SQLite just as a same-inode flock can on macOS/BSD. This
emulates the busy condition, not the native BSD flock implementation.
"""
import fcntl
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import time

root = Path(__file__).resolve().parents[1]
exe = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root / "rewatch/target/debug/rescript"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"))
with tempfile.TemporaryDirectory(prefix="busy-private-record-") as tmp:
    project = Path(tmp).resolve()
    dependency = project / "node_modules/local-dep"
    for directory, name in ((project, "busy-record"), (dependency, "local-dep")):
        (directory / "src").mkdir(parents=True)
        (directory / "package.json").write_text(json.dumps({"name": name, "version": "1.0.0"}))
        (directory / "rescript.json").write_text(json.dumps({
            "name": name, "sources": ["src"],
            "dependencies": ["local-dep"] if directory == project else [],
            "package-specs": [{"module": "esmodule", "in-source": True, "suffix": ".mjs"}],
        }))
    (dependency / "src/Dependency.res").write_text("let value = 1\n")
    (project / "src/A.res").write_text("let f = x => x + Dependency.value\n")
    (project / "src/B.res").write_text("let value = A.f(2)\n")
    (project / "src/B.resi").write_text("let value: int\n")

    def build(extra=None):
        result = subprocess.run([str(exe), "build", str(project)], env=env | (extra or {}),
                                capture_output=True, text=True, timeout=10)
        assert result.returncode == 0, result.stdout + result.stderr
        return result.stdout

    def rows():
        records = []
        for directory in (project, dependency):
            with sqlite3.connect(directory / "lib/rescript/rescript.sqlite") as db:
                assert db.execute("PRAGMA integrity_check").fetchone() == ("ok",)
                assert db.execute("SELECT value FROM meta WHERE key='record_complete'").fetchone() == ("1",)
                record = {table: sorted(db.execute(f"SELECT * FROM {table}")) for table in
                          ("sources", "deps", "parse_warnings", "reads", "items", "interfaces", "interface_extras")}
                record["modules"] = list(db.execute(
                    "SELECT module, implementation_warnings, interface_warnings, interface_digest, imports "
                    "FROM modules ORDER BY module"))
                records.append(record)
        return records

    def outputs():
        return {str(p.relative_to(project)): p.read_bytes() for p in project.rglob("*.mjs")}

    build()
    expected_rows, expected_outputs = rows(), outputs()
    for clean in (False, True):
        for phase in ("open", "insert"):
            for workers in (1, 2, 8):
                for package in ("busy-record", "local-dep"):
                    # A new rendezvous file allows exactly one injected failure.
                    ready = project / f"{clean}-{phase}-{workers}-{package}.ready"
                    if clean:
                        result = subprocess.run([str(exe), "clean", str(project)], env=env,
                                                capture_output=True, text=True, timeout=10)
                        assert result.returncode == 0, result.stdout + result.stderr
                    extra = {"RESCRIPT_FULL_BUILD": "1", "RAYON_NUM_THREADS": str(workers),
                             "RESCRIPT_TEST_PRIVATE_LOCK": f"{package}:{phase}:{ready}"}
                    process = subprocess.Popen([str(exe), "build", str(project)], env=env | extra,
                                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                    try:
                        deadline = time.monotonic() + 10
                        while not ready.exists() or not ready.read_text():
                            assert process.poll() is None, process.communicate()
                            assert time.monotonic() < deadline, "private-lock rendezvous timed out"
                            time.sleep(0.005)
                        with Path(ready.read_text()).open("r+b") as locked_db:
                            # Hold across the entire fallback, not just the failing
                            # statement. The fallback must never wait on this inode.
                            fcntl.lockf(locked_db, fcntl.LOCK_EX | fcntl.LOCK_NB)
                            ready.with_suffix(".locked").touch()
                            stdout, stderr = process.communicate(timeout=5)
                        assert process.returncode == 0, stdout + stderr
                        diagnostic = f"Could not prepare {package}: database is locked; falling back to final-state recording"
                        assert (stdout + stderr).count(diagnostic) == 1, stdout + stderr
                    finally:
                        if process.poll() is None:
                            process.kill()
                            process.communicate(timeout=5)
                    assert rows() == expected_rows, (phase, workers, package)
                    assert outputs() == expected_outputs
                    for directory in (project, dependency):
                        assert not list((directory / "lib/rescript").glob(".rescript-record-*"))
                    assert "Compiled 0 modules" in build()
                    print(f"clean={clean}, {phase}, {workers} workers, {package}: busy reported once; bounded fallback, identical records and output")
    (project / "src/B.res").write_text("let value = A.f(3)\n")
    assert "Compiled 1 module" in build()
    incremental = outputs()
    build({"RESCRIPT_FULL_BUILD": "1", "RESCRIPT_TEST_FINAL_RECORD": "1"})
    assert outputs() == incremental
    assert "Compiled 0 modules" in build()
    print("Recovered record supports one-module edits and zero-module unchanged rebuilds")
