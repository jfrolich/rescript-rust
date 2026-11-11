#!/usr/bin/env python3
"""Run with a real rescript binary: python3 scripts/test_bench_project.py BINARY."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import bench_project


class OutputTests(unittest.TestCase):
    def test_only_written_outputs_and_path_sensitive_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Path(tmp)
            (project / "handwritten.ts").write_text("unchanged")
            before = bench_project.snapshot(project)
            (project / "generated.mjs").write_text("export const x = 1;")
            outputs = bench_project.generated(project, before)
            self.assertEqual(list(outputs), ["generated.mjs"])
            self.assertNotEqual(bench_project.digest(outputs), bench_project.digest({"other.mjs": outputs["generated.mjs"]}))

    def test_cli_errors_and_mismatch(self):
        script = Path(__file__).with_name("bench_project.sh").resolve()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            project = root / "project"
            project.mkdir()
            (project / "rescript.json").write_text('{}')
            checkout = root / "checkout"
            for name in ("runtime", "belt"):
                (checkout / "packages/@rescript" / name).mkdir(parents=True)
            binaries = []
            for name in ("base", "candidate"):
                binary = root / name
                binary.write_text("#!/usr/bin/env python3\nimport pathlib, sys\n"
                                  "p = pathlib.Path(sys.argv[2]) / 'output.js'\n"
                                  "if sys.argv[1] == 'clean': p.unlink(missing_ok=True)\n"
                                  f"else: p.write_text({name!r})\n")
                binary.chmod(0o755)
                binaries.append(str(binary))
            command = [str(script), str(project), *binaries,
                       "--runtime-from", str(checkout), "--no-instructions"]
            result = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn('"status": "different"', result.stdout.splitlines()[-1])
            self.assertIn('"output.js"', result.stdout)
            Path(binaries[1]).write_text('#!/bin/sh\necho "error: deliberate failure"\nexit 7\n')
            result = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertIn('error: deliberate failure', result.stderr)
            self.assertEqual(result.stdout.splitlines()[-1], 'BENCH_PROJECT {"status":"error"}')
            result = subprocess.run([str(script)], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout.splitlines()[-1], 'BENCH_PROJECT {"status":"error"}')

    def test_digest_is_order_independent(self):
        self.assertEqual(bench_project.digest({"b": "2", "a": "1"}),
                         bench_project.digest({"a": "1", "b": "2"}))


def fixture(binary):
    script = Path(__file__).with_name("bench_project.sh").resolve()
    with tempfile.TemporaryDirectory(prefix="bench-fixture-") as tmp:
        project = Path(tmp)
        (project / "src").mkdir()
        (project / "src/Main.res").write_text("let answer = Belt.Array.length([1, 2, 3])\n")
        (project / "handwritten.ts").write_text("// must not enter the digest\n")
        (project / "rescript.json").write_text(json.dumps({
            "name": "bench-fixture", "sources": ["src"],
            "dependencies": ["@rescript/belt"],
            "package-specs": {"module": "esmodule", "in-source": True},
            "suffix": ".mjs",
        }))
        command = [str(script), str(project), str(binary), str(binary), "--no-instructions"]
        # Repeat to exercise replacement of managed copies and the Belt link.
        for _ in range(2):
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            print(result.stdout, end="")
            assert result.returncode == 0, result.stderr
            summary = json.loads(result.stdout.splitlines()[-1].removeprefix("BENCH_PROJECT "))
            assert summary["status"] == "identical", summary
            assert summary["base"]["files"] > 0, summary
            assert summary["base"]["sha256"] == summary["candidate"]["sha256"], summary
            assert (project / "src/Main.mjs").is_file()


if __name__ == "__main__":
    binary = Path(sys.argv.pop(1)).resolve() if len(sys.argv) > 1 else None
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(OutputTests)
    if not unittest.TextTestRunner().run(suite).wasSuccessful():
        sys.exit(1)
    if binary:
        fixture(binary)
