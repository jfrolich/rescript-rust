#!/usr/bin/env python3
"""Measure declined units from full builds; fail if any corpus/reason count rises.

  python3 scripts/tc_coverage.py --rescript rewatch/target/debug/rescript --write
  python3 scripts/tc_coverage.py --rescript rewatch/target/debug/rescript
  python3 scripts/tc_coverage.py --corpus application=/path/to/project --write

Counts are actual checker entries, not a source-file census. Dependencies compiled
by a corpus count in that corpus, except the runtime, measured separately.
Only labels and counts are stored: private source paths never enter the ratchet.
"""
import argparse
from collections import Counter
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
RECORD = re.compile(r"^debug: tc-declined (\w+) (.+)$", re.MULTILINE)
REASONS = {"NotBuilt"}


def counts(output, exclude=None):
    """O(log bytes); reject unrecognized reasons; count diagnostic reruns once."""
    result = Counter()
    seen = set()
    for reason, unit in RECORD.findall(output):
        if reason not in REASONS:
            raise ValueError(f"unknown decline reason: {reason}")
        if (reason, unit) in seen:
            continue
        seen.add((reason, unit))
        if exclude is None or not Path(unit).resolve().is_relative_to(exclude):
            result[reason] += 1
    if not seen:
        raise ValueError("no checker entries: check executable and verbose logging")
    return result


def read_baseline(path):
    result = {}
    for line in path.read_text().splitlines():
        corpus, reason, count = line.split()
        key = (corpus, reason)
        if key in result or reason not in REASONS or int(count) < 0:
            raise ValueError("invalid coverage baseline")
        result[key] = int(count)
    return result


def increases(baseline, measured):
    return [(corpus, reason, baseline.get((corpus, reason), 0), count)
            for (corpus, reason), count in sorted(measured.items())
            if count > baseline.get((corpus, reason), 0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rescript", type=Path, default=ROOT / "rewatch/target/release/rescript")
    parser.add_argument("--runtime", type=Path, default=ROOT / "packages/@rescript/runtime")
    parser.add_argument("--file", type=Path, default=ROOT / "compiler-rust/tc_coverage.txt")
    parser.add_argument("--corpus", action="append", metavar="LABEL=PATH")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    corpora = [entry.split("=", 1) for entry in args.corpus] if args.corpus else [
        ("runtime", str(args.runtime)), ("tests/tests", str(ROOT / "tests/tests"))]
    executable = str(args.rescript.resolve())
    env = dict(os.environ, RESCRIPT_CHECKER="new", RESCRIPT_FULL_BUILD="1",
               RESCRIPT_RUNTIME=str(args.runtime.resolve()), NO_COLOR="1")
    measured = {}
    for label, project in corpora:
        if not label or any(c.isspace() for c in label):
            raise ValueError("corpus label must be a nonempty word")
        build = subprocess.run([executable, "-vv", "build", str(Path(project).resolve())],
                               env=env, capture_output=True, text=True, timeout=300)
        if build.returncode:
            # Do not echo private source paths or diagnostics into a public report.
            raise ValueError(f"{label}: build failed with exit {build.returncode}")
        # Embedded runtime snapshots are optional. Do not let their availability
        # change a project count; runtime has its own measured corpus.
        runtime = args.runtime.resolve()
        exclude = None if Path(project).resolve() == runtime else runtime
        for reason, count in counts(build.stdout + build.stderr, exclude).items():
            measured[label, reason] = count
            print(f"{label} {reason} {count}")
    baseline = read_baseline(args.file) if args.file.exists() else {}
    if args.write:
        # Updating one corpus preserves the others, including an unavailable private corpus.
        labels = {label for label, _ in corpora}
        baseline = {key: n for key, n in baseline.items() if key[0] not in labels}
        baseline.update(measured)
        args.file.write_text("".join(f"{c} {r} {n}\n" for (c, r), n in sorted(baseline.items())))
        return 0
    regressions = increases(baseline, measured)
    for corpus, reason, before, after in regressions:
        print(f"coverage regression: {corpus} {reason} {before} -> {after}", file=sys.stderr)
    return int(bool(regressions))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(2)
