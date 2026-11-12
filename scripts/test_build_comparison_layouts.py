"""Regression tests for current and legacy build comparison layouts."""

import contextlib
import io
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import compare_checker_builds as checker
import test_stored_interface_determinism as determinism


class BuildComparisonLayouts(unittest.TestCase):
    def test_database_layouts(self):
        for relative in ("rescript.sqlite", "lib/rescript/rescript.sqlite", "lib/bs/rescript.sqlite"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                database = root / relative
                database.parent.mkdir(parents=True, exist_ok=True)
                with sqlite3.connect(database) as db:
                    for table in determinism.TABLES:
                        db.execute(f"CREATE TABLE {table} (module TEXT, data BLOB)")
                    db.execute("INSERT INTO interfaces VALUES (?, ?)", ("Example", b"interface"))
                with patch.object(determinism.sqlite3, "connect", wraps=sqlite3.connect) as connect:
                    self.assertEqual(determinism.read_interfaces(root),
                                     {("interfaces", "Example"): b"interface"})
                    connect.assert_called_once_with(database.resolve().as_uri() + "?mode=ro", uri=True)
                self.assertEqual(determinism.database_path(database), database)

    def test_current_database_precedes_legacy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for layout in ("rescript", "bs"):
                database = root / "lib" / layout / "rescript.sqlite"
                database.parent.mkdir(parents=True)
                database.touch()
            self.assertEqual(determinism.database_path(root), root / "lib/rescript/rescript.sqlite")

    def test_missing_database_lists_candidates_without_creating_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaises(FileNotFoundError) as error:
                determinism.read_interfaces(root)
            for relative in ("rescript.sqlite", "lib/rescript/rescript.sqlite", "lib/bs/rescript.sqlite"):
                self.assertIn(str(root / relative), str(error.exception))
            self.assertEqual(list(root.iterdir()), [])
            missing = root / "missing.sqlite"
            with self.assertRaisesRegex(FileNotFoundError, "missing.sqlite"):
                determinism.read_interfaces(missing)
            self.assertFalse(missing.exists())

    def test_compiler_log_layouts_and_generated_file_filter(self):
        for layout in ("rescript", "bs"):
            with self.subTest(layout=layout), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                log = root / "lib" / layout / ".compiler.log"
                log.parent.mkdir(parents=True)
                log.write_text("#Start(0)\nWarning\n  src/Example.res:1:1\nUnused value\n#Done(0)\n")
                self.assertEqual(checker.compiler_logs(root), [log])
                self.assertEqual(len(checker.diagnostics_of(root, log.read_text())["src/Example.res"]), 1)
                for internal in ("lib/rescript", "lib/bs", "lib/ocaml"):
                    path = root / internal / "internal.js"
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.touch()
                output = root / "lib/js/Example.js"
                output.parent.mkdir(parents=True)
                output.touch()
                self.assertEqual(set(checker.generated_candidates(root)), {Path("lib/js/Example.js")})

    def test_build_without_logs_exits_two(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            project = root / "project"
            project.mkdir()
            result = subprocess.CompletedProcess([], 0, "", "")
            errors = io.StringIO()
            with patch.object(checker.os, "access", return_value=True), \
                    patch.object(checker.Side, "run", return_value=result), \
                    contextlib.redirect_stderr(errors):
                side = checker.Side("base", root / "rescript", None, project, root, [])
                with self.assertRaises(SystemExit) as error:
                    side.build(False)
            self.assertEqual(error.exception.code, 2)
            self.assertIn("base: build produced no compiler log", errors.getvalue())
            self.assertIn("lib/rescript/.compiler.log", errors.getvalue())
            self.assertIn("lib/bs/.compiler.log", errors.getvalue())


if __name__ == "__main__":
    unittest.main()
