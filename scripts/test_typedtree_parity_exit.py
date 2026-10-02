"""Test the parity report's exit status without compiling the corpus."""

import os
from pathlib import Path
import subprocess
import unittest


class TypedtreeParityExitTests(unittest.TestCase):
    def test_report_fails_on_compiler_errors_or_mismatches(self):
        script = Path(__file__).with_name("test_typedtree_parity.sh").read_text()
        # Execute the real terminal reporting block with synthetic counters.
        report = script.split("# Calculate and display parity percentage\n", 1)[1]
        for ocaml_fail, rust_fail, parity_fail in (
            (0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0),
        ):
            with self.subTest(ocaml=ocaml_fail, rust=rust_fail, parity=parity_fail):
                env = dict(os.environ, OCAML_FAIL=str(ocaml_fail),
                           RUST_FAIL=str(rust_fail), PARITY_FAIL=str(parity_fail),
                           RUST_AVAILABLE="true", PARITY_PASS="609",
                           GREEN="", BOLD="", RESET="", YELLOW="")
                result = subprocess.run(["bash", "-c", report], env=env,
                                        capture_output=True, text=True, timeout=5)
                expected = int(bool(ocaml_fail or rust_fail or parity_fail))
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                self.assertEqual("SUCCESS" in result.stdout, expected == 0)


if __name__ == "__main__":
    unittest.main()
