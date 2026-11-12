#!/usr/bin/env python3
"""Abort a debug build during persistence; require a full, correct recovery."""
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
exe = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root / "rewatch/target/debug/rescript"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
with tempfile.TemporaryDirectory(prefix="interrupted-store-") as tmp:
    project = Path(tmp)
    (project / "rescript.json").write_text('{"name":"interrupted-store","sources":["src"],"package-specs":[{"module":"esmodule","in-source":true,"suffix":".mjs"}]}')
    (project / "src").mkdir()
    (project / "src/A.res").write_text('let value = 42\n')
    (project / "src/B.res").write_text('let value = A.value\n')

    def build(extra=None, succeeds=True):
        result = subprocess.run([str(exe), "build", str(project)],
                                env=env | (extra or {}), capture_output=True, text=True, timeout=30)
        output = result.stdout + result.stderr
        assert result.returncode == (0 if succeeds else -signal.SIGABRT), output
        return output

    assert "Compiled 2 modules" in build()
    expected = {p.relative_to(project): p.read_bytes() for p in project.rglob("*.mjs")}
    assert expected
    assert "Compiled 0 modules" in build()
    aborted = build({"RESCRIPT_FULL_BUILD": "1", "RESCRIPT_TEST_ABORT_RECORD_WRITE": "interrupted-store"}, False)
    assert "Finished compilation" in aborted, aborted
    recovered = build()
    assert "Compiled 2 modules" in recovered, recovered
    actual = {p.relative_to(project): p.read_bytes() for p in project.rglob("*.mjs")}
    assert actual == expected
    assert "Compiled 0 modules" in build()
    print("Aborted after result; recovery compiled both modules with identical JS; next build compiled zero modules")
