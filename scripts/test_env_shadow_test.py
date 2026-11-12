"""Fail-closed report parsing tests (python3 -m unittest discover -s scripts -p test_env_shadow_test.py)."""
import json
import unittest

from test_env_shadow import PREFIX, summarize


def report(**changes):
    value = {"stage": "env-shadow", "unit": "Fixture.res",
             "counts": {"find_value": 2, "clone": 1}, "difference": None}
    value.update(changes)
    return PREFIX + json.dumps(value)


class ReportTests(unittest.TestCase):
    def test_sums_retries_instead_of_hiding_a_failure(self):
        self.assertEqual(summarize(report() + "\n" + report())["lookup_comparisons"], 4)
        with self.assertRaisesRegex(RuntimeError, "find_value"):
            summarize(report(difference="find_value(x) differs") + "\n" + report())

    def test_no_reports_and_no_lookups_fail(self):
        for output in ("Compiled 717 modules", report(counts={"add_value": 3})):
            with self.assertRaisesRegex(RuntimeError, "zero"):
                summarize(output)

    def test_invalid_count_fails(self):
        for count in (-1, True, "2"):
            with self.assertRaisesRegex(RuntimeError, "invalid count"):
                summarize(report(counts={"find_value": count}))

    def test_invalid_report_fails(self):
        with self.assertRaisesRegex(RuntimeError, "invalid environment"):
            summarize(report(stage="signature-equality"))


if __name__ == "__main__":
    unittest.main()
