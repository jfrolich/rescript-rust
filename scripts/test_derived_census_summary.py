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
