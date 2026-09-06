#!/usr/bin/env python3
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("env_ownership_candidate_measure.py")
spec = importlib.util.spec_from_file_location("env_candidate", SCRIPT)
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)


class CandidateMeasureTests(unittest.TestCase):
    def test_unknown_mode_and_missing_approval_fail_closed(self):
        for mode in ["unknown-mode", "screen"]:
            result = subprocess.run(
                ["python3", str(SCRIPT), mode], cwd=candidate.ROOT,
                capture_output=True, timeout=5,
            )
            self.assertNotEqual(result.returncode, 0)
        self.assertFalse((candidate.m.D / "screen-runs.jsonl").exists())

    def test_metadata_must_be_absent_before_and_exact_after(self):
        metadata = candidate.generated_metadata_paths()
        before = {"inputs": {"source.res": "a"}, "source": {"tracked": "x"}, "symlinks": {"link": "y"}}
        generated = {**before, "inputs": {**before["inputs"], **{path: "hash" for path in metadata}}}
        self.assertTrue(candidate.compare_inventory(before, before, False)["valid"])
        self.assertTrue(candidate.compare_inventory(before, generated, True)["valid"])
        removed = {**generated, "inputs": dict(generated["inputs"])}
        removed["inputs"].pop(next(iter(metadata)))
        self.assertFalse(candidate.compare_inventory(before, removed, True)["valid"])
        existing = {**before, "inputs": {**before["inputs"], next(iter(metadata)): "old"}}
        self.assertFalse(candidate.compare_inventory(existing, existing, False)["valid"])
        edited = {**before, "inputs": {"source.res": "changed"}}
        self.assertFalse(candidate.compare_inventory(before, edited, False)["valid"])

    def test_failed_build_still_appends_attempt_row(self):
        old_dir, old_command, old_env = candidate.m.D, candidate.m.command, candidate.m.env
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "bin").mkdir(); (root / "logs").mkdir()
            executable = root / "bin/rescript-X"
            executable.write_text("#!/bin/sh\nif [ \"$1\" = clean ]; then exit 0; fi\necho fake failure >&2\nexit 7\n")
            executable.chmod(0o755)
            candidate.m.D = root
            candidate.m.command = lambda variant: [str(executable), "build"]
            candidate.m.env = lambda variant, workers: os.environ.copy()
            try:
                with self.assertRaises(RuntimeError):
                    candidate.timed_attempt("paired", 1, 1, "X", 1)
                rows = [json.loads(line) for line in (root / "runs.jsonl").read_text().splitlines()]
                self.assertEqual(len(rows), 1)
                self.assertEqual(rows[0]["exit"], 7)
                self.assertIn("attempt_error", rows[0])
                self.assertTrue((root / "logs/paired-1-1-X-w1.process.json").is_file())
            finally:
                candidate.m.D, candidate.m.command, candidate.m.env = old_dir, old_command, old_env

    def test_output_failure_and_screen_failure_preserve_rows(self):
        old_dir, old_command, old_env, old_outputs = candidate.m.D, candidate.m.command, candidate.m.env, candidate.m.outputs
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "bin").mkdir(); (root / "logs").mkdir()
            executable = root / "bin/rescript-X"
            executable.write_text("#!/bin/sh\nif [ \"$1\" = clean ]; then exit 0; fi\necho 'Compiled 3248 modules'\nexit 0\n")
            executable.chmod(0o755)
            candidate.m.D = root
            candidate.m.command = lambda variant: [str(executable), "build"]
            candidate.m.env = lambda variant, workers: os.environ.copy()
            candidate.m.outputs = lambda: (_ for _ in ()).throw(OSError("hash failed"))
            try:
                with self.assertRaises(OSError):
                    candidate.timed_attempt("paired", 1, 1, "X", 1)
                row = json.loads((root / "runs.jsonl").read_text().splitlines()[0])
                self.assertEqual(row["phase"], "outputs")
                self.assertIn("hash failed", row["attempt_error"])
                driver = {"exit": 9, "timeout": False, "error": None}
                with self.assertRaises(RuntimeError):
                    candidate.finalize_screen("X", 1, 1, driver)
                screen = json.loads((root / "screen-runs.jsonl").read_text().splitlines()[0])
                self.assertEqual(screen["driver"]["exit"], 9)
                self.assertIn("attempt_error", screen)
            finally:
                candidate.m.D, candidate.m.command, candidate.m.env, candidate.m.outputs = old_dir, old_command, old_env, old_outputs

    def test_ordered_plan_rejects_reordering(self):
        plan = {"screen_order": [["D", 1, 1], ["C", 1, 1]], "paired_order": [[1, 1, 1, "D"]], "historical_order": [[1, 1, "A", 12]]}
        screens = [{"variant": "D", "workers": 1, "repetition": 1}, {"variant": "C", "workers": 1, "repetition": 1}]
        rows = [{"stage": "paired", "pair": 1, "position": 1, "variant": "D", "workers": 1}, {"stage": "historical", "pair": 1, "position": 1, "variant": "A", "workers": 12}]
        candidate.verify_ordered_rows(plan, screens, rows)
        with self.assertRaises(RuntimeError):
            candidate.verify_ordered_rows(plan, list(reversed(screens)), rows)
        with self.assertRaises(RuntimeError):
            candidate.verify_ordered_rows(plan, screens, list(reversed(rows)))

    def test_required_metrics_rejects_partial_time_output(self):
        with self.assertRaises(RuntimeError):
            candidate.parse_required_metrics("real 1.0\nuser 0.5\nsys 0.1\n")


if __name__ == "__main__":
    unittest.main()
