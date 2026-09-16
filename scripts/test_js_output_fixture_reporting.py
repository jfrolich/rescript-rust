"""Exercise failure reporting without running a compiler or changing fixtures."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class FixtureFailureReportingTests(unittest.TestCase):
    def test_many_missing_outputs_keep_first_diff_and_exit_failure(self):
        script = Path(__file__).with_name("test_js_output_parity_fixtures.sh")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copyfile(script, scripts / script.name)
            fixtures = root / "tests/js_output_parity/fixtures"
            fixtures.mkdir(parents=True)
            sources = []
            # Forty sources across eight modes exceed a pipe buffer, exposing
            # reporting pipelines that exit early under `set -o pipefail`.
            for index in range(40):
                source = fixtures / f"probe_{index:02}.res"
                source.write_text("let value = 1\n")
                sources.append(str(source.relative_to(root)))
            (fixtures.parent / "cases.tsv").write_text("\n".join(sources) + "\n")
            stub = root / "no-output-compiler"
            stub.write_text("#!/bin/sh\nexit 0\n")
            stub.chmod(0o755)
            runtime = root / "runtime"
            runtime.mkdir()
            env = dict(os.environ, RESCRIPT_RUNTIME=str(runtime))
            for name in ("OCAML_BSC", "RUST_BSC", "REWATCH_BIN", "RESCRIPT_CLI"):
                env[name] = str(stub)
            result = subprocess.run(
                [os.environ.get("BASH_TEST_BIN", "bash"), str(scripts / script.name)],
                env=env, capture_output=True, text=True, timeout=90,
            )
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("total:  320", result.stdout)
            self.assertIn("First diff:", result.stdout)
            self.assertIn("Generated files in output and source directories", result.stdout)
            self.assertIn("probe_00.res", result.stdout)
            self.assertNotIn("Broken pipe", result.stderr)


if __name__ == "__main__":
    unittest.main()
