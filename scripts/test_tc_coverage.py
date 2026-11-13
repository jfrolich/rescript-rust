#!/usr/bin/env python3
import unittest
from pathlib import Path
from tc_coverage import counts, increases


class CoverageTests(unittest.TestCase):
    def test_counts_ten_thousand_entries(self):
        output = "\n".join(f"debug: tc-declined NotBuilt unit{i}.res" for i in range(10000))
        self.assertEqual(counts(output), {"NotBuilt": 10000})

    def test_ratchet(self):
        base = {("test", "NotBuilt"): 3}
        self.assertEqual(increases(base, {("test", "NotBuilt"): 2}), [])
        self.assertEqual(increases(base, base), [])
        self.assertEqual(increases(base, {("test", "NotBuilt"): 4}), [("test", "NotBuilt", 3, 4)])
        self.assertEqual(increases({}, base), [("test", "NotBuilt", 0, 3)])

    def test_reruns_count_once(self):
        self.assertEqual(counts("debug: tc-declined NotBuilt a.res\ndebug: tc-declined NotBuilt a.res"), {"NotBuilt": 1})

    def test_runtime_snapshot_does_not_change_project_count(self):
        project = "debug: tc-declined NotBuilt /project/A.res"
        runtime = "debug: tc-declined NotBuilt /runtime/Int.res"
        self.assertEqual(counts(project, Path("/runtime")),
                         counts(project + "\n" + runtime, Path("/runtime")))
        self.assertEqual(counts(runtime), {"NotBuilt": 1})

    def test_fail_closed(self):
        for output in ("", "debug: tc-declined Unknown a.res"):
            with self.assertRaises(ValueError):
                counts(output)


if __name__ == "__main__":
    unittest.main()
