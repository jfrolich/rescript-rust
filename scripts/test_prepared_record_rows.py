#!/usr/bin/env python3
"""Compare worker-prepared fresh rows with the final-state fallback and edit recovery."""
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
exe = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root / "rewatch/target/debug/rescript"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"))
with tempfile.TemporaryDirectory(prefix="prepared-record-") as tmp:
    project = Path(tmp).resolve()
    (project / "src").mkdir()
    (project / "rescript.json").write_text(json.dumps({
        "name": "prepared-record", "namespace": True, "sources": ["src"],
        "package-specs": [{"module": "esmodule", "in-source": True, "suffix": ".mjs"}],
    }))
    for name, text in {
        "A.res": "let n = 1\nlet f = x => x + n\n",
        "B.res": "let f = x => A.f(x)\n",
        "C.resi": "let value: int\n",
        "C.res": "let value = B.f(2)\n",
        "D.res": "let value = C.value + B.f(3)\n",
    }.items():
        (project / "src" / name).write_text(text)

    def build(full=False):
        result = subprocess.run([str(exe), "build"], cwd=project,
                                env=env | ({"RESCRIPT_FULL_BUILD": "1"} if full else {}),
                                capture_output=True, text=True, timeout=10)
        assert result.returncode == 0, result.stdout + result.stderr
        return result.stdout

    def rows():
        with sqlite3.connect(project / "lib/rescript/rescript.sqlite") as db:
            tables = {table: sorted(db.execute(f"SELECT * FROM {table}")) for table in
                      ("sources", "deps", "parse_warnings", "reads", "items", "interfaces", "interface_extras")}
            tables["modules"] = list(db.execute(
                "SELECT module, implementation_warnings, interface_warnings, interface_digest, imports "
                "FROM modules ORDER BY module"))
            return tables

    def outputs():
        return {str(p.relative_to(project)): p.read_bytes() for p in project.rglob("*.mjs")}

    build()
    fresh = rows()
    build(full=True)  # Existing records disable fresh-build preparation.
    assert fresh == rows(), "fresh preparation and final-state fallback differ"
    assert "Compiled 0 modules" in build()
    (project / "src/C.res").write_text("let value = B.f(4)\n")
    build()
    incremental = outputs()
    build(full=True)
    assert incremental == outputs(), "incremental edit and full build differ"
    assert "Compiled 0 modules" in build()
    print("Prepared/fallback rows identical; incremental edit matches full build; unchanged builds compile zero modules")
