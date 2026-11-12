"""Unit tests for the signature oracle collector (no compiler needed)."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import test_signature_equality as oracle


class SignatureEqualityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.report = {"unit": "/corpus/Unit.res", "stage": "signature-equality"}
        self.report.update({kind: {"status": "equal"} for kind in oracle.KINDS})

    def write(self, name="outcome", report=None):
        (self.directory / f"{name}.json").write_text(json.dumps(report or self.report))

    def result(self):
        return {"corpus": oracle.summarize(self.directory)}

    def test_equal_and_duplicate_reports(self):
        self.write()
        self.write("duplicate")
        actual = self.result()
        oracle.check(actual, {"corpus": 1})
        self.assertEqual(actual["corpus"]["units"], 1)
        for kind in oracle.KINDS:
            self.assertEqual(actual["corpus"][kind]["equal"], 1)

    def test_zero_reports_fails(self):
        with self.assertRaisesRegex(RuntimeError, "zero reports"):
            oracle.check(self.result(), {"corpus": 1})

    def test_below_minimum_fails(self):
        self.write()
        with self.assertRaisesRegex(RuntimeError, "below minimum"):
            oracle.check(self.result(), {"corpus": 2})

    def test_each_difference_survives_a_successful_retry(self):
        self.write()
        for kind in oracle.KINDS:
            report = copy.deepcopy(self.report)
            report[kind] = {"status": "different", "detail": "offset 12"}
            self.write(kind, report)
            actual = self.result()
            self.assertEqual(actual["corpus"][kind]["different"], 1)
            with self.assertRaisesRegex(RuntimeError, "offset 12"):
                oracle.check(actual, {"corpus": 1})

    def test_pending_is_not_not_applicable(self):
        self.report["fingerprint"] = {"status": "pending"}
        self.write()
        with self.assertRaisesRegex(RuntimeError, "not implemented"):
            oracle.check(self.result(), {"corpus": 1})

    def test_not_applicable_has_per_comparison_reason_counts(self):
        self.report["bytes"] = {"status": "not_applicable", "reason": "pool full"}
        self.write()
        actual = self.result()
        oracle.check(actual, {"corpus": 1})
        self.assertEqual(actual["corpus"]["bytes"]["not_applicable"], {"pool full": 1})
        self.assertEqual(actual["corpus"]["fingerprint"]["equal"], 1)

    def test_missing_reason_rejected(self):
        self.report["bytes"] = {"status": "not_applicable"}
        self.write()
        with self.assertRaisesRegex(RuntimeError, "without reason"):
            self.result()

    def test_invalid_stage_rejected(self):
        self.report["stage"] = "other-oracle"
        self.write()
        with self.assertRaisesRegex(RuntimeError, "unexpected report stage"):
            self.result()

    def test_invalid_status_rejected(self):
        self.report["bytes"] = {"status": "success"}
        self.write()
        with self.assertRaisesRegex(RuntimeError, "invalid status"):
            self.result()

    def test_corpus_filter_excludes_dependency_reports(self):
        self.write()
        self.assertEqual(oracle.summarize(self.directory, Path("/other"))["units"], 0)
        self.assertEqual(oracle.summarize(self.directory, Path("/corpus"))["units"], 1)


if __name__ == "__main__":
    unittest.main()
