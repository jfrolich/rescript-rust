"""Test the exit-status guard of the res_parser JSX warning stage.

Runs the real test_error_output_parity.sh (`--parser-only`, limited to the
JSX warning fixtures) with fake OCaml and Rust parsers. The fakes print the
same stderr on both sides and exit with each fixture's expected status (2 for
the error fixtures, 0 for the valid ones) unless FAKE_STATUS overrides it for
both sides, so a status both parsers share but the fixture does not expect
(a timeout, a missing executable, a signal, a wrong 0 or 2) must fail.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("test_error_output_parity.sh")

# `-jsx-version 4 file`: a warning block, then the error line at status 2.
FAKE_PARSER = r'''
import os, sys
path = sys.argv[-1]
status = 0 if "with_props_payload_warning" in path else 2
status = int(os.environ.get("FAKE_STATUS") or status)
sys.stderr.write("\n  Warning number 3\n  " + path + ":2:1-25\n\n")
if status == 2:
    sys.stderr.write("fake uncaught error\n")
sys.exit(status)
'''


class JsxParserWarningStatusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        root = Path(cls.dir.name)
        (root / "fake_parser.py").write_text(FAKE_PARSER)
        cls.parser = root / "parser"
        cls.parser.write_text(f'#!/bin/sh\nexec python3 -I "{root}/fake_parser.py" "$@"\n')
        cls.parser.chmod(0o755)

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def run_stage(self, fixture, status=None):
        env = dict(os.environ, OCAML_PARSER=str(self.parser), RUST_PARSER=str(self.parser),
                   RUST_TARGET="none")
        env.pop("FAKE_STATUS", None)
        if status is not None:
            env["FAKE_STATUS"] = str(status)
        result = subprocess.run(["bash", str(SCRIPT), "--parser-only", "fixtures/" + fixture],
                                env=env, capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        self.assertIn("total:  1", output.replace("\x1b", ""), output)
        return result.returncode, output

    def test_expected_statuses_pass(self):
        for fixture in ("jsx_warning_then_error.res", "jsx_signature_error_then_warning.resi",
                        "jsx_with_props_payload_warning.res",
                        "jsx_signature_with_props_payload_warning.resi"):
            with self.subTest(fixture=fixture):
                code, output = self.run_stage(fixture)
                self.assertEqual(code, 0, output)

    def test_shared_unexpected_status_fails_an_error_fixture(self):
        # Timeout, cannot execute, not found, a signal, and a wrong success.
        for status in (124, 126, 127, 137, 0):
            with self.subTest(status=status):
                code, output = self.run_stage("jsx_warning_then_error.res", status)
                self.assertEqual(code, 1, output)
                self.assertIn(f"OCaml {status}, Rust {status}, expected 2", output)

    def test_shared_error_status_fails_a_valid_fixture(self):
        for status in (2, 124):
            with self.subTest(status=status):
                code, output = self.run_stage("jsx_signature_with_props_payload_warning.resi",
                                              status)
                self.assertEqual(code, 1, output)
                self.assertIn(f"OCaml {status}, Rust {status}, expected 0", output)


if __name__ == "__main__":
    unittest.main()
