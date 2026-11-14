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
        corpora = {"runtime": {"units": 10, "identical": 8,
                               "unsupported": {"reason": 2}}}
        self.baseline = {stage: copy.deepcopy(corpora) for stage in coverage.STAGES}
        self.baseline[coverage.UNCOMPARED] = {"runtime": 1}

    def test_unchanged_and_improved_pass(self):
        check(self.baseline, self.baseline)
        improved = copy.deepcopy(self.baseline)
        for stage in coverage.STAGES:
            improved[stage] = {"runtime": {"units": 10, "identical": 9,
                                           "unsupported": {"reason": 1}}}
        check(improved, self.baseline)

    def test_each_stage_is_ratcheted_on_its_own(self):
        for stage in coverage.STAGES:
            actual = copy.deepcopy(self.baseline)
            actual[stage]["runtime"]["unsupported"]["reason"] = 3
            with self.assertRaisesRegex(RuntimeError, f"{stage}: runtime: fallback count grew"):
                check(actual, self.baseline)

    def test_reports_are_counted_per_stage(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for i, (stage, reason) in enumerate([("lambda-bridge", None),
                                                 ("lambda-norm", "reason")]):
                (directory / f"{i}.json").write_text(json.dumps({
                    "unit": "Unit.res", "stage": stage,
                    "identical": reason is None, "unsupported": reason,
                }))
            self.assertEqual(summarize(directory, "lambda-bridge"), {
                "units": 1, "identical": 1, "unsupported": {}})
            self.assertEqual(summarize(directory, "lambda-norm"), {
                "units": 1, "identical": 0, "unsupported": {"reason": 1}})
            (directory / "2.json").write_text(json.dumps({
                "unit": "Unit.res", "stage": "other", "identical": True, "unsupported": None}))
            with self.assertRaisesRegex(RuntimeError, "unexpected report stage"):
                summarize(directory, "lambda-norm")

    def test_any_mode_fallback_wins(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for i, reason in enumerate([None, "reason", None]):
                (directory / f"{i}.json").write_text(json.dumps({
                    "unit": "Unit.res", "stage": "lambda-bridge",
                    "identical": reason is None, "unsupported": reason,
                }))
            self.assertEqual(summarize(directory, "lambda-bridge"), {
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
        actual["lambda-bridge"]["runtime"]["units"] = 9
        with self.assertRaisesRegex(RuntimeError, "missing units"):
            check(actual, self.baseline)

    def test_growing_fallback_fails(self):
        actual = copy.deepcopy(self.baseline)
        actual["lambda-bridge"]["runtime"]["unsupported"]["reason"] = 3
        with self.assertRaisesRegex(RuntimeError, "fallback count grew"):
            check(actual, self.baseline)

    def test_added_unit_may_fall_back_where_fallbacks_exist(self):
        actual = copy.deepcopy(self.baseline)
        actual["lambda-bridge"]["runtime"] = {"units": 11, "identical": 8,
                                              "unsupported": {"reason": 3}}
        check(actual, self.baseline)
        actual["lambda-bridge"]["runtime"] = {"units": 11, "identical": 7,
                                              "unsupported": {"reason": 4}}
        with self.assertRaisesRegex(RuntimeError, "fallback count grew"):
            check(actual, self.baseline)

    def test_fully_supported_corpus_keeps_no_fallback(self):
        full = {stage: {"runtime": {"units": 10, "identical": 10, "unsupported": {}}}
                for stage in coverage.STAGES}
        full[coverage.UNCOMPARED] = {"runtime": 0}
        actual = copy.deepcopy(full)
        actual["lambda-bridge"]["runtime"] = {"units": 11, "identical": 11, "unsupported": {}}
        check(actual, full)
        actual["lambda-bridge"]["runtime"] = {"units": 11, "identical": 10,
                                              "unsupported": {"reason": 1}}
        with self.assertRaisesRegex(RuntimeError, "gained a fallback"):
            check(actual, full)

    def test_growing_uncompared_units_fail(self):
        actual = copy.deepcopy(self.baseline)
        actual[coverage.UNCOMPARED]["runtime"] = 0
        check(actual, self.baseline)
        actual[coverage.UNCOMPARED]["runtime"] = 2
        with self.assertRaisesRegex(
                RuntimeError, "names-uncompared: runtime: uncompared units grew: 2 > 1"):
            check(actual, self.baseline)

    def test_record_writes_the_uncompared_units(self):
        results = {stage: self.baseline[stage] for stage in coverage.STAGES}
        naming = {"runtime": {"compared": 9, "uncompared": 3, "adopted_nodes": 0,
                              "differences": 0}}
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "ratchet.txt"
            coverage.write_record(path, results, naming)
            recorded = json.loads(path.read_text())
        self.assertEqual(recorded[coverage.UNCOMPARED], {"runtime": 3})
        self.assertEqual({key: recorded[key] for key in coverage.STAGES}, results)
        check(coverage.ratchet(results, naming), recorded)

    def test_new_reason_fails(self):
        actual = copy.deepcopy(self.baseline)
        actual["lambda-bridge"]["runtime"]["unsupported"] = {"different": 2}
        with self.assertRaisesRegex(RuntimeError, "fallback reason grew"):
            check(actual, self.baseline)


if __name__ == "__main__":
    unittest.main()
