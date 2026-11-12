"""Unit tests for the coverage gate; no compiler subprocesses required."""
import copy
import unittest
from unittest.mock import patch
import subprocess
import test_backend_coverage as coverage
import json
import tempfile
from pathlib import Path
from test_backend_coverage import check, summarize


class CoverageGateTests(unittest.TestCase):
    def setUp(self):
        self.baseline = {"runtime": {"units": 10, "identical": 8,
                                     "unsupported": {"reason": 2}}}

    def test_unchanged_and_improved_pass(self):
        check(self.baseline, self.baseline)
        improved = {"runtime": {"units": 10, "identical": 9,
                                 "unsupported": {"reason": 1}}}
        check(improved, self.baseline)

    def test_any_mode_fallback_wins(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for i, reason in enumerate([None, "reason", None]):
                (directory / f"{i}.json").write_text(json.dumps({
                    "unit": "Unit.res", "stage": "lambda-bridge",
                    "identical": reason is None, "unsupported": reason,
                }))
            self.assertEqual(summarize(directory), {
                "units": 1, "identical": 0, "unsupported": {"reason": 1}})

    def test_package_is_cleaned_and_zero_reports_still_fail(self):
        with patch("sys.argv", ["test_backend_coverage.py"]), patch.object(
                coverage.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)) as run:
            with self.assertRaisesRegex(RuntimeError, "runtime: no shadow reports"):
                coverage.main()
        binary = str(coverage.ROOT / "rewatch/target/release/rescript")
        runtime = str(coverage.ROOT / "packages/@rescript/runtime")
        self.assertEqual([call.args[0] for call in run.call_args_list], [
            [binary, "clean", runtime], [binary, "build", runtime]])

    def test_failed_clean_stops_before_build(self):
        with patch("sys.argv", ["test_backend_coverage.py"]), patch.object(
                coverage.subprocess, "run", return_value=subprocess.CompletedProcess([], 1)) as run:
            with self.assertRaisesRegex(RuntimeError, "runtime: oracle command failed"):
                coverage.main()
        self.assertEqual(run.call_count, 1)
        self.assertEqual(run.call_args.args[0][1], "clean")

    def test_missing_units_fail(self):
        actual = copy.deepcopy(self.baseline)
        actual["runtime"]["units"] = 9
        with self.assertRaisesRegex(RuntimeError, "missing units"):
            check(actual, self.baseline)

    def test_growing_fallback_fails(self):
        actual = copy.deepcopy(self.baseline)
        actual["runtime"]["unsupported"]["reason"] = 3
        with self.assertRaisesRegex(RuntimeError, "fallback count grew"):
            check(actual, self.baseline)

    def test_new_reason_fails(self):
        actual = copy.deepcopy(self.baseline)
        actual["runtime"]["unsupported"] = {"different": 2}
        with self.assertRaisesRegex(RuntimeError, "fallback reason grew"):
            check(actual, self.baseline)


if __name__ == "__main__":
    unittest.main()
