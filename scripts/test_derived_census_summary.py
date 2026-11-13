import unittest
from derived_census_summary import PHASES, markdown, summarize


def row():
    item = {key: dict(derived=11, other=29, estimated=False)
            for key in (*PHASES, "js_bytes", "js_lines")}
    item.update(version=1, module="example.res", bindings=[3, 2],
                syntax_nodes=[30, 20], checker_counters=None)
    return item


class DerivedCensusSummaryTest(unittest.TestCase):
    def test_sums_ten_thousand_records_without_losing_integer_precision(self):
        item = row()
        item["typecheck"]["derived"] = 2**53 + 1
        result = summarize(item for _ in range(10_000))
        self.assertEqual(result["typecheck"]["derived"], (2**53 + 1) * 10_000)
        self.assertEqual(result["bindings"], [30_000, 20_000])
        self.assertEqual(result["counter_modules"], 0)

    def test_estimates_and_unavailable_counters_are_visible(self):
        item = row()
        item["printing"]["estimated"] = True
        result = summarize([item])
        text = markdown(result)
        self.assertIn("node-weighted estimate", text)
        self.assertIn("Counter availability: 0/1", text)

    def test_shape_columns_and_exact_template_identity(self):
        item = row()
        item.update(shape_classes=["record"] * 3, shape_nodes=[10, 10, 100],
                    shape_parameterised=[False, True, False], shape_recursive=[False] * 3,
                    templates=[[1, 2], [1, 2], [1, 3]])
        result = summarize([item])
        self.assertEqual(result["distinct_templates"], 2)
        self.assertEqual(result["duplicate_bindings"], 1)
        self.assertEqual(result["shapes"]["record"]["p50"], 10)
        self.assertEqual(result["shapes"]["parameterised (overlap)"]["count"], 1)
        item["templates"][0] = None
        partial = summarize([item])
        self.assertEqual(partial["distinct_templates"], 2)
        self.assertEqual(partial["unsupported_templates"], 1)
        self.assertEqual(partial["distinct_template_nodes"], 110)
        self.assertEqual(partial["template_body_nodes"], 120)
        self.assertEqual(partial["unsupported_template_nodes"], 10)
        item["shape_nodes"].pop()
        with self.assertRaises(ValueError):
            summarize([item])

    def test_path_timing_preserves_totals_and_counts(self):
        item = row()
        item.update(planned_typecheck_ns=7, planned_conversion_ns=3,
                    paths={"plan": 2, "not_yet_planned": 1})
        result = summarize(item for _ in range(10_000))
        self.assertEqual(result["planned_typecheck_ns"], 70_000)
        self.assertEqual(result["general_typecheck_ns"], 40_000)
        self.assertEqual(result["planned_conversion_ns"], 30_000)
        self.assertEqual(result["general_conversion_ns"], 80_000)
        self.assertEqual(result["paths"], {"plan": 20_000, "not_yet_planned": 10_000})
        self.assertIn("Bindings on a plan ms", markdown(result))

    def test_legacy_records_do_not_claim_general_timing(self):
        result = summarize([row()])
        self.assertEqual(result["path_timing_records"], 0)
        self.assertEqual(result["general_typecheck_ns"], 0)
        self.assertIn("Path timing availability: 0/1", markdown(result))

    def test_invalid_path_timing_and_counts(self):
        for value in (-1, 12, 1.5, True):
            item = row()
            item.update(planned_typecheck_ns=value, planned_conversion_ns=0)
            with self.assertRaises(ValueError):
                summarize([item])
        item = row()
        item["paths"] = {"plan": -1}
        with self.assertRaises(ValueError):
            summarize([item])

    def test_counter_sides(self):
        item = row()
        item["checker_counters"] = [[1, 2, 3, 4], [10, 20, 30, 40]]
        result = summarize([item, item])
        self.assertEqual(result["checker_counters"], [[2, 4, 6, 8], [20, 40, 60, 80]])

    def test_rejects_unknown_version_and_negative_time(self):
        item = row()
        item["version"] = 2
        with self.assertRaises(ValueError):
            summarize([item])
        item = row()
        item["printing"]["other"] = -1
        with self.assertRaises(ValueError):
            summarize([item])


if __name__ == "__main__":
    unittest.main()
