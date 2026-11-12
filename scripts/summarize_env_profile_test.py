import unittest

from summarize_env_profile import summarize


PROFILE = """positions: line
events: Ir
summary: 1000
fn=(1) caller
cfn=(2) rescript_compiler::types::env::profile::table_entry::<255, (), calibration>
calls=10 0
0 100
cfn=(3) rescript_compiler::types::env::profile::log_entry::<255, (), calibration>
calls=10 0
0 120
cfn=(4) rescript_compiler::types::env::profile::table_entry::<12, (), write>
calls=2 0
0 80
cfn=(5) rescript_compiler::types::env::profile::table_entry::<140, (), cow>
calls=2 0
0 60
cfn=(6)
calls=2 0
0 100
fn=(6) rescript_compiler::types::env::profile::log_entry::<12, (), bind>
0 40
cfn=(7) helper
calls=2 0
0 60
fn=(7)
0 60
"""


class ProfileTests(unittest.TestCase):
    def test_inclusive_cost_is_counted_once_and_cow_is_added(self):
        result = summarize(PROFILE, {12: "add_value"})
        row = result["operations"][0]
        self.assertEqual(row["table"]["instructions"], 140)
        self.assertEqual(row["table"]["body_calls"], 2)
        self.assertEqual(row["table"]["cow_calls"], 2)
        self.assertEqual(row["log"]["instructions"], 100)
        self.assertEqual(result["paired_instructions"], {"table": 100, "log": 76})

    def test_folded_identical_calibration(self):
        folded = PROFILE.replace("summary: 1000", "summary: 1000000")
        folded = folded.replace("calls=10 0\n0 100", "calls=20000 0\n0 200000", 1)
        folded = folded.replace("cfn=(3) rescript_compiler::types::env::profile::log_entry::<255, (), calibration>\ncalls=10 0\n0 120\n", "")
        result = summarize(folded, {12: "add_value"})
        self.assertTrue(result["empty_entries_folded"])
        self.assertEqual(result["empty_entry_instructions"], {"table": 10, "log": 10})

    def test_missing_calibration_fails(self):
        with self.assertRaisesRegex(ValueError, "calibrated"):
            summarize(PROFILE.replace("::<255,", "::<254,"), {12: "add_value"})

    def test_incomplete_edge_fails(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            summarize(PROFILE + "cfn=(6)\ncalls=1 0\n", {12: "add_value"})

    def test_missing_side_is_not_silently_paired(self):
        with self.assertRaisesRegex(ValueError, "zero paired"):
            summarize(PROFILE.replace("log_entry::<12,", "log_entry::<19,"),
                      {12: "add_value", 19: "add_type"})


if __name__ == "__main__":
    unittest.main()
