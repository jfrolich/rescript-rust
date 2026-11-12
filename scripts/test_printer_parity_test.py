"""Coverage gates use actual per-output reports, never build log guesses."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from test_printer_parity import check, summarize


class PrinterCoverageTests(unittest.TestCase):
    def setUp(self):
        self.baseline = {"runtime": {"outputs": 10, "emitted": 8, "unsupported": {"reason": 2}}}

    def test_unchanged_and_improved(self):
        check(self.baseline, self.baseline)
        check({"runtime": {"outputs": 10, "emitted": 9, "unsupported": {"reason": 1}}}, self.baseline)

    def test_regressions(self):
        for field, value, message in [("outputs", 9, "outputs missing"), ("emitted", 7, "emitted count fell"),
                                      ("emitted", 0, "zero oxc"), ("unsupported", {"new": 1}, "new fallback"),
                                      ("unsupported", {"reason": 3}, "fallback count grew")]:
            actual = copy.deepcopy(self.baseline)
            actual["runtime"][field] = value
            with self.assertRaisesRegex(RuntimeError, message):
                check(actual, self.baseline)

    def test_missing_baseline(self):
        with self.assertRaisesRegex(RuntimeError, "no baseline"):
            check(self.baseline, {})

    def test_duplicates_and_multiple_formats(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            outputs = [root / "a.mjs", root / "a.cjs", root / "b.mjs"]
            reports = root / "reports"
            reports.mkdir()
            for i, (output, reason) in enumerate([(outputs[0], None), (outputs[0], "reason"),
                                                 (outputs[1], None), (outputs[2], None)]):
                (reports / f"{i}.json").write_text(json.dumps({"source": str(root / "a.res"),
                    "output": str(output), "emitted": reason is None, "unsupported": reason}))
            # The unselected third output cannot inflate this corpus's evidence.
            self.assertEqual(summarize(reports, outputs[:2], root),
                             {"outputs": 2, "emitted": 1, "unsupported": {"reason": 1}})
            with self.assertRaisesRegex(RuntimeError, "no outputs emitted"):
                summarize(reports, outputs[:1], root)

    def test_missing_reports_and_wrong_corpus_fail(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaisesRegex(RuntimeError, "no outputs emitted"):
                summarize(root, [], root)
            (root / "report.json").write_text(json.dumps({"source": "/other/a.res", "output": str(root / "a.mjs"),
                "emitted": True, "unsupported": None}))
            with self.assertRaisesRegex(RuntimeError, "no outputs emitted"):
                summarize(root, [root / "a.mjs"], root)

    def test_contradictory_report_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "report.json").write_text(json.dumps({"source": str(root / "a.res"),
                "output": str(root / "a.mjs"), "emitted": True, "unsupported": "reason"}))
            with self.assertRaisesRegex(RuntimeError, "contradictory"):
                summarize(root, [root / "a.mjs"], root)

class PrinterOptionTests(unittest.TestCase):
    def parse(self, args, printer=None):
        import os
        import subprocess
        from test_printer_parity import ROOT
        env = {k: v for k, v in os.environ.items() if not k.startswith("PARITY_")}
        if printer:
            env["PARITY_JS_PRINTER"] = printer
        return subprocess.run(["bash", "-c", '''
            PARITY_PARSE_ONLY=1 source "$1/scripts/parity_lib.sh"
            shift
            parity_parse_printer_args "$@" || exit $?
            printf '%s:%s:%s' "$PARITY_JS_PRINTER" "$PARITY_RECORD" "${PARITY_ARGS[*]}"
        ''', "options", str(ROOT), *args], env=env, text=True, capture_output=True)

    def test_default_and_existing_arguments_unchanged(self):
        self.assertEqual(self.parse(["--quick", "--reformat"]).stdout, "legacy:0:--quick --reformat")

    def test_environment_option_and_explicit_override(self):
        self.assertEqual(self.parse([], "oxc").stdout, "oxc:0:")
        self.assertEqual(self.parse(["--printer", "legacy"], "oxc").stdout, "legacy:0:")
        self.assertEqual(self.parse(["--printer", "oxc", "--record"]).stdout, "oxc:1:")

    def test_invalid_options_fail(self):
        for args in [["--printer"], ["--printer", "unknown"], ["--record"]]:
            self.assertEqual(self.parse(args).returncode, 2)


if __name__ == "__main__":
    unittest.main()
