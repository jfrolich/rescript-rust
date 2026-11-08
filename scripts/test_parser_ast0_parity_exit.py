"""Test that the AST0 parity script counts failed parser commands.

Runs the real script on one file with a fake parser for each side. The fake
prints the same output for both sides unless told to fail, time out or
differ in one stage, so every case isolates one stage of one parser.
"""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("test_parser_ast0_parity.sh")
BASELINES = Path(__file__).resolve().parent.parent / "tests" / "parity_baselines"

FAKE_PARSER = r'''
import os, sys, time
side, args = sys.argv[1], sys.argv[2:]
fmt = args[args.index("-print") + 1]
if "-test-ast-conversion" in args:
    stage = {"sexp": "roundtrip-structure", "sexp-locs": "roundtrip-locs"}[fmt]
else:
    stage = {"sexp": "parse", "sexp0-locs": "sexp0-locs", "binary0": "binary0"}[fmt]
want_side, want_stage, mode = (os.environ.get("FAKE_FAIL") or "::").split(":")
if (side, stage) == (want_side, want_stage):
    if mode == "exit":
        print("fake failure", file=sys.stderr)
        sys.exit(3)
    if mode == "timeout":
        time.sleep(30)
    if mode == "differ":
        print("(" + stage + " " + side + ")")
        sys.exit(0)
print("(" + stage + ")")
'''

ANSI = re.compile(r"\x1b\[[0-9;]*m|\\033\[[0-9;]*m")


def baseline_digest():
    digest = hashlib.sha256()
    for path in sorted(BASELINES.glob("*.txt")):
        digest.update(path.name.encode() + path.read_bytes())
    return digest.hexdigest()


class Ast0ParityStageFailureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        root = Path(cls.dir.name)
        (root / "fake_parser.py").write_text(FAKE_PARSER)
        for side in ("ocaml", "rust"):
            wrapper = root / side
            wrapper.write_text(
                f'#!/bin/sh\nexec python3 -I "{root}/fake_parser.py" {side} "$@"\n')
            wrapper.chmod(0o755)
        cls.input = root / "Input.res"
        cls.input.write_text("let x = 1\n")
        cls.root = root

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def run_script(self, fake_fail=""):
        env = dict(os.environ, OCAML_PARSER=str(self.root / "ocaml"),
                   RUST_PARSER=str(self.root / "rust"), FAKE_FAIL=fake_fail,
                   TELLA_DIR=str(self.root / "no-corpus"))
        before = baseline_digest()
        result = subprocess.run(["bash", str(SCRIPT), str(self.input)], env=env,
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(baseline_digest(), before, "baselines must not change")
        return result.returncode, ANSI.sub("", result.stdout + result.stderr)

    def test_full_parity_succeeds(self):
        code, out = self.run_script()
        self.assertEqual(code, 0, out)
        self.assertIn("Stage failures:           0", out)
        self.assertIn("SUCCESS", out)

    def test_failed_command_in_any_stage_is_a_counted_failure(self):
        stages = ["parse", "sexp0-locs", "roundtrip-structure", "roundtrip-locs", "binary0"]
        for side in ("ocaml", "rust"):
            for stage in stages:
                with self.subTest(side=side, stage=stage):
                    code, out = self.run_script(f"{side}:{stage}:exit")
                    self.assertEqual(code, 2, out)
                    self.assertIn("Stage failures:           1", out)
                    self.assertIn(f"{self.input} / {stage} / {side} / exit 3: fake failure", out)
                    self.assertIn("FAILED: 1 parser command(s) in 1 file(s)", out)
                    self.assertNotIn("SUCCESS", out)
                    self.assertIn("Location differences:     0", out)

    def test_timeout_in_a_secondary_stage_is_a_counted_failure(self):
        for side in ("ocaml", "rust"):
            with self.subTest(side=side):
                code, out = self.run_script(f"{side}:roundtrip-locs:timeout")
                self.assertEqual(code, 2, out)
                self.assertIn(
                    f"{self.input} / roundtrip-locs / {side} / timed out after 5s (exit 124)", out)
                self.assertIn("Location differences:     0", out)

    def test_location_difference_stays_a_difference(self):
        code, out = self.run_script("rust:roundtrip-locs:differ")
        self.assertEqual(code, 1, out)
        self.assertIn("Location differences:     1", out)
        self.assertIn("Stage failures:           0", out)


if __name__ == "__main__":
    unittest.main()
