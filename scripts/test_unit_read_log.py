#!/usr/bin/env python3
"""T3 migration gate: compare the checker log and typed-tree walk on both corpora.

Run at the comparison commit, before deleting the reference collector.
"""

import argparse
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rescript", type=Path, default=ROOT / "rewatch/target/debug/rescript")
    args = parser.parse_args()
    env = dict(os.environ, RESCRIPT_CHECK_UNIT_READS="1",
               RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"),
               RAYON_NUM_THREADS="1")
    for corpus in ("packages/@rescript/runtime", "tests/tests"):
        for command in ("clean", "build"):
            result = subprocess.run([str(args.rescript.resolve()), command, str(ROOT / corpus)],
                                    env=env, text=True, capture_output=True, timeout=300)
            if result.returncode:
                raise SystemExit(result.stdout + result.stderr)
        rows = re.findall(r"unit-read-check: (.*): (\d+) reads, zero differences", result.stderr)
        if not rows:
            raise SystemExit(f"{corpus}: no set comparisons ran")
        print(f"{corpus}: {len(rows)} compilation units (implementations and interfaces), "
              f"{sum(int(count) for _, count in rows)} reads, zero differences")


if __name__ == "__main__":
    main()
