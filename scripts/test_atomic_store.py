#!/usr/bin/env python3
"""Kill whole-record publication at each boundary; never expose a partial image."""
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
exe = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else root / "rewatch/target/debug/rescript"
env = dict(os.environ, RESCRIPT_RUNTIME=str(root / "packages/@rescript/runtime"))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for stage in ("progressive", "before-commit", "after-commit", "after-close",
              "after-lock", "before-rename", "after-rename"):
    with tempfile.TemporaryDirectory(prefix="atomic-store-") as tmp:
        project = Path(tmp)
        (project / "src").mkdir()
        (project / "rescript.json").write_text(json.dumps({
            "name": "atomic-store", "sources": ["src"],
            "package-specs": [{"module": "esmodule", "in-source": True, "suffix": ".mjs"}],
        }))
        source = project / "src/A.res"
        source.write_text("let value = 1\n")
        (project / "src/B.res").write_text("let unrelated = 2\n")

        def build(extra=None, killed=False):
            result = subprocess.run([str(exe), "build", str(project)], env=env | (extra or {}),
                                    capture_output=True, text=True, timeout=10)
            assert result.returncode == (-signal.SIGABRT if killed else 0), result.stdout + result.stderr
            return result.stdout

        build()
        db = project / "lib/rescript/rescript.sqlite"
        old = db.read_bytes()
        source.write_text("let value = 3\n")
        # A changed source inventory forces whole-record replacement even
        # though the previous complete database is still present.
        (project / "src/C.res").write_text("let added = 4\n")
        build({"RESCRIPT_FULL_BUILD": "1", "RESCRIPT_STORE_BATCH_MODULES": "1",
               "RESCRIPT_TEST_ABORT_PUBLICATION": f"atomic-store:{stage}"}, True)
        leftovers = list(db.parent.glob(".rescript-record-*.sqlite"))
        assert len(leftovers) == (0 if stage == "after-rename" else 1), leftovers
        sidecars = list(db.parent.glob(".rescript-record-*.sqlite.lock"))
        assert len(sidecars) == len(leftovers), sidecars
        assert (db.read_bytes() == old) == (stage != "after-rename"), stage
        with sqlite3.connect(db) as conn:
            assert conn.execute("PRAGMA integrity_check").fetchone() == ("ok",)
            assert conn.execute("SELECT value FROM meta WHERE key='record_complete'").fetchone() == ("1",)
        for suffix in ("-journal", "-wal"):
            assert not Path(str(db) + suffix).exists()
        build()
        assert not list(db.parent.glob(".rescript-record-*")), "next build must remove abandoned private files"
        expected = (project / "src/A.mjs").read_bytes()
        assert b"3" in expected
        assert "Compiled 0 modules" in build()
        build({"RESCRIPT_FULL_BUILD": "1"})
        assert (project / "src/A.mjs").read_bytes() == expected
        print(f"{stage}: complete image; recovery matches full build; unchanged rebuild compiles zero modules")
        if stage == "after-rename":
            # No sources change: recovery must remove the abandoned private
            # file even when the next build takes the zero-module fast path.
            old = db.read_bytes()
            build({"RESCRIPT_FULL_BUILD": "1", "RESCRIPT_STORE_BATCH_MODULES": "1",
                   "RESCRIPT_TEST_ABORT_PUBLICATION": "atomic-store:progressive"}, True)
            assert db.read_bytes() == old
            assert list(db.parent.glob(".rescript-record-*.sqlite"))
            assert "Compiled 0 modules" in build()
            assert not list(db.parent.glob(".rescript-record-*"))
            print("killed unchanged rebuild: old record intact; zero-module startup removes leftover")
