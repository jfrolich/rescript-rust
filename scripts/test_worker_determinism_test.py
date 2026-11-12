"""Exercise the gate with a tiny executable producing all four output kinds."""
import contextlib
import io
import os
import sqlite3
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import test_worker_determinism as gate


FAKE_COMPILER = r'''#!/usr/bin/env python3
import json
import os
from pathlib import Path
import sqlite3
import sys

command, project, *args = sys.argv[1:]
project = Path(project)
if "--dump" in args and "--dump-dir" not in args:
    sys.exit(2)
if project.name == "runtime":
    sys.exit(0)
mode = json.loads((project / "rescript.json").read_text())["mode"]
lib = project / "lib/rescript"
lib.mkdir(parents=True, exist_ok=True)
if command == "clean":
    for path in (project / "out.bin", lib / "rescript.sqlite", lib / ".compiler.log"):
        path.unlink(missing_ok=True)
    sys.exit(0)
workers = os.environ["RAYON_NUM_THREADS"]
seed = os.environ.get("RESCRIPT_WORLD_SHUFFLE", "off")
with open(os.environ["FAKE_TRACE"], "a") as trace:
    trace.write(f"{workers}/{seed}\n")
if mode == "failure" and workers == "8":
    sys.exit(1)
changed = workers == "8" and seed == "2"
value = lambda kind: "different" if changed and mode == kind else "same"
(project / "out.bin").write_text(value("generated"))
(lib / ".compiler.log").write_text("Warning 1\n  Source.res:1:1\n" + value("diagnostics"))
sig = Path(args[args.index("--dump-dir") + 1])
sig.mkdir(parents=True)
if mode != "missing-signatures":
    (sig / "Source.sig").write_text(value("signatures"))
with sqlite3.connect(lib / "rescript.sqlite") as db:
    for table in ("interfaces", "interface_extras", "runtime_interfaces"):
        db.execute(f"CREATE TABLE {table} (module TEXT, data BLOB)")
        db.execute(f"INSERT INTO {table} VALUES (?, ?)", ("Source", value("interfaces").encode()))
'''


class WorkerDeterminismTests(unittest.TestCase):
    def run_gate(self, mode):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            project = root / "project"
            project.mkdir()
            (project / "rescript.json").write_text('{"mode": "' + mode + '"}')
            executable = root / "rescript"
            executable.write_text(FAKE_COMPILER)
            executable.chmod(0o755)
            trace = root / "trace"
            output = io.StringIO()
            with patch.dict(os.environ, {"FAKE_TRACE": str(trace), "RESCRIPT_WORLD_SHUFFLE": "777"}), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
                try:
                    result = gate.main([str(project), "--rescript", str(executable),
                                        "--runtime", str(root / "runtime"),
                                        "--work-dir", str(root / "snapshots")])
                except SystemExit as error:
                    result = error.code
            return result, output.getvalue(), trace.read_text().splitlines()

    def test_workspace_collects_child_interfaces_but_rejects_all_empty(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            paths = [root / "lib/rescript/rescript.sqlite",
                     root / "child/lib/rescript/rescript.sqlite"]
            for path in paths:
                path.parent.mkdir(parents=True)
                with sqlite3.connect(path) as db:
                    for table in ("interfaces", "interface_extras", "runtime_interfaces"):
                        db.execute(f"CREATE TABLE {table} (module TEXT, data BLOB)")
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                gate.interfaces(root)
            self.assertEqual(error.exception.code, 2)
            with sqlite3.connect(paths[1]) as db:
                db.execute("INSERT INTO interfaces VALUES (?, ?)", ("Child", b"signature"))
            self.assertEqual(gate.interfaces(root), {
                ("child/lib/rescript/rescript.sqlite/interfaces", "Child"): b"signature",
            })
            # The existing standalone check remains strict by default.
            with self.assertRaises(ValueError):
                gate.read_interfaces(paths[0])

    def test_four_distinct_builds_and_inherited_shuffle_is_cleared(self):
        result, output, trace = self.run_gate("equal")
        self.assertEqual(result, 0, output)
        self.assertEqual(trace, ["1/off", "8/off", "8/1", "8/2"])
        self.assertIn("generated: no difference (1 compared)", output)

    def test_each_output_kind_can_fail_independently(self):
        for kind in ("generated", "diagnostics", "signatures", "interfaces"):
            with self.subTest(kind=kind):
                result, output, trace = self.run_gate(kind)
                self.assertEqual(result, 1, output)
                self.assertEqual(len(trace), 4)

    def test_build_failure_is_two_not_a_difference(self):
        result, output, trace = self.run_gate("failure")
        self.assertEqual(result, 2, output)
        self.assertEqual(len(trace), 2)

    def test_missing_signatures_is_an_error(self):
        result, output, trace = self.run_gate("missing-signatures")
        self.assertEqual(result, 2, output)
        self.assertIn("no canonical signatures", output)


if __name__ == "__main__":
    unittest.main()
