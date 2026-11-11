"""Test that the AST parity script counts failed commands.

Runs the real script on one file with fake parsers, compilers and value
comparison for each side. The fakes print the same output for both sides
unless told to fail, time out, reject, differ or skip writing their output
in one stage, so every case isolates one stage of one side. The spice,
parser warning and parse error stages run on one fixture each in a temporary
directory.
"""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("test_parser_ast_parity.sh")
BASELINES = Path(__file__).resolve().parent.parent / "tests" / "parity_baselines"

# A res_parser (`-print FMT file` or `-jsx-version 4 file`) or a bsc
# (`[-ppx P] -bs-ast file -o out`). FAKE_FAIL is "side:stage:mode", where
# side is ocaml, rust or both.
FAKE_TOOL = r'''
import os, sys, time
side, args = sys.argv[1], sys.argv[2:]
out = None
if "-bs-ast" in args:
    stage = "spice-ppx" if "-ppx" in args else "bsc-ast"
    out = args[args.index("-o") + 1]
elif "-print" in args:
    stage = args[args.index("-print") + 1]
else:
    stage = "parser-warning"
want_side, want_stage, mode = (os.environ.get("FAKE_FAIL") or "::").split(":")
text = "(" + stage + ")\n"
if want_side in (side, "both") and want_stage == stage:
    if mode == "exit":
        print("fake failure", file=sys.stderr)
        sys.exit(3)
    if mode == "reject":
        print("fake rejection", file=sys.stderr)
        sys.exit(2)
    if mode == "reject-split":
        # Both reject, the OCaml side with status 2 and Rust with 1.
        print("fake rejection", file=sys.stderr)
        sys.exit(2 if side == "ocaml" else 1)
    if mode in ("reject-msg", "reject1-msg"):
        # Both reject with the same status and different stderr.
        print("fake rejection by " + side, file=sys.stderr)
        sys.exit(2 if mode == "reject-msg" else 1)
    if mode == "reject-stdout":
        # Both reject with the same status and stderr, and different stdout.
        print("partial output of " + side)
        print("fake rejection", file=sys.stderr)
        sys.exit(2)
    if mode == "stream":
        # The output goes to stderr instead of stdout.
        sys.stderr.write(text)
        sys.exit(0)
    if mode == "timeout":
        time.sleep(30)
    if mode == "differ":
        text = "(" + stage + " " + side + ")\n"
    if mode == "nofile":
        sys.exit(0)
if out is None:
    sys.stdout.write(text)
else:
    with open(out, "w") as f:
        f.write(text)
'''

# inspect_binary_ast.py: `same-values a b`, `compare a b`, and the module
# interface the spice comparison loads. FAKE_INSPECT=crash makes every
# comparison fail.
FAKE_INSPECT = r'''
import os, sys

def _crash():
    if os.environ.get("FAKE_INSPECT") == "crash":
        raise RuntimeError("fake comparison crash")

class BinaryAstFile:
    def __init__(self, path):
        with open(path, "rb") as f:
            self.data = f.read()

    def decode_ast(self):
        _crash()
        return self.data, None

def compare_value_trees(a, b, dec_a, dec_b):
    return [] if a == b else ["values differ"]

if __name__ == "__main__":
    command, a, b = sys.argv[1:4]
    _crash()
    same = open(a, "rb").read() == open(b, "rb").read()
    if not same:
        print("values differ")
    sys.exit(0 if same or command == "compare" else 1)
'''

ANSI = re.compile(r"\x1b\[[0-9;]*m|\\033\[[0-9;]*m")


def baseline_digest():
    digest = hashlib.sha256()
    for path in sorted(BASELINES.glob("*.txt")):
        digest.update(path.name.encode() + path.read_bytes())
    return digest.hexdigest()


class AstParityStageFailureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        root = Path(cls.dir.name)
        (root / "fake_tool.py").write_text(FAKE_TOOL)
        (root / "fake_inspect.py").write_text(FAKE_INSPECT)
        for side in ("ocaml", "rust"):
            wrapper = root / side
            wrapper.write_text(
                f'#!/bin/sh\nexec python3 -I "{root}/fake_tool.py" {side} "$@"\n')
            wrapper.chmod(0o755)
        spice_ppx = root / "spice_ppx"
        spice_ppx.write_text("#!/bin/sh\nexit 0\n")
        spice_ppx.chmod(0o755)
        (root / "spice").mkdir()
        cls.spice_file = root / "spice" / "Spice.res"
        cls.spice_file.write_text("let x = 1\n")
        (root / "warnings" / "expected").mkdir(parents=True)
        cls.warning_file = root / "warnings" / "Warning.res"
        cls.warning_file.write_text("let x = 1\n")
        (root / "warnings" / "expected" / "Warning.res.txt").write_text("(parser-warning)\n")
        (root / "errors").mkdir()
        cls.parse_error_file = root / "errors" / "Broken.res"
        cls.parse_error_file.write_text("let = \n")
        cls.input = root / "Input.res"
        cls.input.write_text("let x = 1\n")
        cls.root = root

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def run_script(self, fake_fail="", fake_inspect=""):
        root = self.root
        env = dict(os.environ, OCAML_PARSER=str(root / "ocaml"), RUST_PARSER=str(root / "rust"),
                   OCAML_BSC=str(root / "ocaml"), RUST_BSC=str(root / "rust"),
                   SPICE_PPX=str(root / "spice_ppx"), SPICE_TEST_DIR=str(root / "spice"),
                   PARSER_WARNING_DIR=str(root / "warnings"),
                   PARSE_ERROR_DIRS=str(root / "errors"),
                   INSPECT_SCRIPT=str(root / "fake_inspect.py"),
                   FAKE_FAIL=fake_fail, FAKE_INSPECT=fake_inspect,
                   TELLA_DIR=str(root / "no-corpus"))
        before = baseline_digest()
        result = subprocess.run(["bash", str(SCRIPT), str(self.input)], env=env,
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(baseline_digest(), before, "baselines must not change")
        return result.returncode, ANSI.sub("", result.stdout + result.stderr)

    def stage_file(self, stage):
        return {"spice-ppx": self.spice_file,
                "parser-warning": self.warning_file,
                "ml": self.parse_error_file}.get(stage, self.input)

    def assert_one_stage_failure(self, out, line):
        self.assertIn("Stage failures:           1", out)
        self.assertIn(line, out)
        self.assertIn("FAILED: 1 command(s) in 1 file(s)", out)
        self.assertNotIn("SUCCESS", out)

    def test_full_parity_succeeds(self):
        code, out = self.run_script()
        self.assertEqual(code, 0, out)
        self.assertIn("Stage failures:           0", out)
        self.assertIn("SUCCESS", out)

    def test_failed_command_is_a_counted_failure(self):
        cases = [(side, stage) for side in ("ocaml", "rust")
                 for stage in ("sexp-locs", "spice-ppx", "parser-warning")]
        # The parse error stage compares any exit status, so only a killed or
        # timed out command is a failure (see the timeout test).
        # Where the OCaml reference may reject a file, a failing Rust command
        # after an OCaml success is a failure.
        cases += [("rust", "sexp-locs-ppx"), ("rust", "bsc-ast")]
        for side, stage in cases:
            with self.subTest(side=side, stage=stage):
                code, out = self.run_script(f"{side}:{stage}:exit")
                self.assertEqual(code, 2, out)
                self.assert_one_stage_failure(
                    out, f"{self.stage_file(stage)} / {stage} / {side} / exit 3: fake failure")

    def test_timeout_is_a_counted_failure(self):
        for stage in ("sexp-locs", "sexp-locs-ppx", "bsc-ast", "spice-ppx", "parser-warning"):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"ocaml:{stage}:timeout")
                self.assertEqual(code, 2, out)
                self.assert_one_stage_failure(
                    out, f"{self.stage_file(stage)} / {stage} / ocaml / timed out after 5s (exit 124)")

    def test_parse_error_timeout_is_a_counted_failure(self):
        code, out = self.run_script("rust:ml:timeout")
        self.assertEqual(code, 2, out)
        self.assertIn("Stage failures:           2", out)
        for mode in ("plain", "recover"):
            self.assertIn(
                f"{self.parse_error_file} / parse-error-{mode} / rust / timed out after 5s (exit 124)", out)

    def test_missing_ast_file_is_a_counted_failure(self):
        for stage in ("bsc-ast", "spice-ppx"):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"rust:{stage}:nofile")
                self.assertEqual(code, 2, out)
                self.assert_one_stage_failure(
                    out, f"{self.stage_file(stage)} / {stage} / rust / exit 0 without writing the AST file")

    def test_failed_value_comparison_is_a_counted_failure(self):
        code, out = self.run_script(fake_inspect="crash")
        self.assertEqual(code, 2, out)
        self.assertIn("Stage failures:           2", out)
        self.assertIn(f"{self.input} / bsc-ast-compare / inspect_binary_ast.py / exit 1:", out)
        self.assertIn(f"{self.spice_file} / spice-ppx-compare / inspect_binary_ast.py / exit 1:", out)

    def test_rejection_by_both_sides_is_listed(self):
        # bsc reproduces OCaml's diagnostics, so its stderr is compared; the
        # text of res_parser's uncaught exception is not.
        for stage, streams in (("sexp-locs-ppx", "stdout identical, stderr not compared (uncaught exception)"),
                               ("bsc-ast", "stdout identical, stderr identical")):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"both:{stage}:reject")
                self.assertEqual(code, 0, out)
                self.assertIn("Stage failures:           0", out)
                self.assertIn("Rejected by both the OCaml reference and Rust (1):", out)
                self.assertIn(
                    f"{self.input} / {stage} / ocaml exit 2: fake rejection / rust exit 2: fake rejection / {streams}",
                    out)

    def test_rejection_with_other_compared_streams_is_a_difference(self):
        cases = [("bsc-ast", "reject-msg", "bsc-ast value differences: 1"),
                 ("bsc-ast", "reject-stdout", "bsc-ast value differences: 1"),
                 ("sexp-locs-ppx", "reject-stdout", "sexp-locs-ppx differences: 1"),
                 # Status 1 is res_cli's own report, so its stderr is compared.
                 ("sexp-locs-ppx", "reject1-msg", "sexp-locs-ppx differences: 1")]
        for stage, mode, summary in cases:
            with self.subTest(stage=stage, mode=mode):
                code, out = self.run_script(f"both:{stage}:{mode}")
                self.assertEqual(code, 1, out)
                self.assertIn(summary, out)
                self.assertIn("Stage failures:           0", out)
                self.assertNotIn("Rejected by both", out)

    def test_uncaught_exception_text_is_not_compared(self):
        code, out = self.run_script("both:sexp-locs-ppx:reject-msg")
        self.assertEqual(code, 0, out)
        self.assertIn(
            f"{self.input} / sexp-locs-ppx / ocaml exit 2: fake rejection by ocaml / "
            "rust exit 2: fake rejection by rust / stdout identical, stderr not compared (uncaught exception)",
            out)

    def test_parse_error_streams_are_compared_separately(self):
        code, out = self.run_script()
        self.assertIn("parse error checks:       2", out)
        self.assertIn("parse error passes:       2", out)
        code, out = self.run_script("rust:ml:stream")
        self.assertEqual(code, 1, out)
        self.assertIn("parse error differences:  2", out)
        self.assertIn(f"{self.parse_error_file} (parse-error-plain: stdout differs,stderr differs)", out)
        self.assertIn("FAILED: Parse error streams have 2 difference(s)", out)

    def test_reference_rejection_accepted_by_rust_is_a_difference(self):
        for stage, summary in (("sexp-locs-ppx", "sexp-locs-ppx differences: 1"),
                               ("bsc-ast", "bsc-ast value differences: 1")):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"ocaml:{stage}:reject")
                self.assertEqual(code, 1, out)
                self.assertIn(summary, out)
                self.assertIn("Stage failures:           0", out)

    def test_rejection_with_another_status_is_a_difference(self):
        for stage, summary in (("sexp-locs-ppx", "sexp-locs-ppx differences: 1"),
                               ("bsc-ast", "bsc-ast value differences: 1")):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"both:{stage}:reject-split")
                self.assertEqual(code, 1, out)
                self.assertIn(summary, out)
                self.assertIn("Stage failures:           0", out)
                self.assertNotIn("Rejected by both", out)

    def test_difference_stays_a_difference(self):
        for stage, summary in (("sexp-locs", "sexp-locs differences:    1"),
                               ("sexp-locs-ppx", "sexp-locs-ppx differences: 1"),
                               ("bsc-ast", "bsc-ast value differences: 1"),
                               ("spice-ppx", "spice differences:        1"),
                               ("parser-warning", "warning differences:      1")):
            with self.subTest(stage=stage):
                code, out = self.run_script(f"rust:{stage}:differ")
                self.assertEqual(code, 1, out)
                self.assertIn(summary, out)
                self.assertIn("Stage failures:           0", out)


if __name__ == "__main__":
    unittest.main()
