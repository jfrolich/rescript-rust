"""The sequential gate can share inputs without overlapping compiler runs."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import compare_build_instructions as gate


class SequentialGateTest(unittest.TestCase):
    def run_gate(self, sequential):
        calls = []

        class Side:
            def __init__(self, name, exe, checkout, project, work_dir):
                self.name = name
                self.project = Path(checkout) / project
                self.modules = 1
                self.counts = []

            def prepare(self):
                calls.append((self.name, "prepare"))

            def measure(self, index):
                calls.append((self.name, "measure"))
                self.counts.append((100, Path("unused")))
                return 100

            def best(self):
                return min(self.counts)

        with tempfile.TemporaryDirectory() as work:
            args = ["gate", "--base", "base", work, "--head", "head", work,
                    "--runs", "1", "--work-dir", work]
            if sequential:
                args.append("--sequential")
            with patch("sys.argv", args), patch.object(gate, "Side", Side), \
                    patch.object(gate, "function_diff", return_value=""), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                result = gate.main()
        return result, calls

    def test_shared_inputs_are_prepared_and_measured_sequentially(self):
        result, calls = self.run_gate(True)
        self.assertEqual(result, 0)
        self.assertEqual(calls, [("base", "prepare"), ("head", "prepare"),
                                 ("base", "measure"), ("head", "measure")])

    def test_parallel_mode_still_rejects_shared_inputs(self):
        with self.assertRaisesRegex(SystemExit, "separate checkouts"):
            self.run_gate(False)
