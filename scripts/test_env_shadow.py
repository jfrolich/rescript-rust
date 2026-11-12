#!/usr/bin/env python3
"""Clean-build runtime and tests/tests with environment shadow comparisons.

Run after building rewatch. Intended for the existing compiler validation job,
after its runtime/test dependencies are installed; no workflow changes needed
for local use. Extra projects can be supplied with --project.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PREFIX = "RESCRIPT_ENV_SHADOW "


def summarize(output):
    counts = Counter()
    units = set()
    failures = []
    reports = 0
    for line in output.splitlines():
        if not line.startswith(PREFIX):
            continue
        report = json.loads(line[len(PREFIX):])
        if report.get("stage") != "env-shadow" or not report.get("unit"):
            raise RuntimeError("invalid environment shadow report")
        reports += 1
        units.add(report["unit"])
        if report.get("difference"):
            failures.append(report["difference"])
        for kind, count in report["counts"].items():
            if not isinstance(count, int) or isinstance(count, bool) or count < 0:
                raise RuntimeError(f"invalid count for {kind}: {count!r}")
            counts[kind] += count
    if failures:
        raise RuntimeError("\n".join(failures))
    # Binds alone are not proof that lookup comparison ran.
    lookups = sum(count for kind, count in counts.items()
                  if kind.startswith(("find_", "lookup_", "normalize_", "iter_", "fold_")))
    if not reports or not lookups:
        raise RuntimeError("zero environment lookup comparisons")
    return {"units": len(units), "reports": reports,
            "lookup_comparisons": lookups, "operations": dict(sorted(counts.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", type=Path,
                        default=ROOT / "rewatch/target/release/rescript")
    parser.add_argument("--project", type=Path, action="append", default=[])
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    executable = args.executable.resolve()
    env = dict(os.environ, RESCRIPT_ENV_SHADOW="1",
               RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"))
    projects = [ROOT / "packages/@rescript/runtime", ROOT / "tests/tests", *args.project]
    for project in projects:
        output = ""
        for command in ("clean", "build"):
            run = subprocess.run([str(executable), command, str(project.resolve())],
                                 cwd=project.resolve(), env=env, capture_output=True, text=True,
                                 timeout=args.timeout)
            if command == "build":
                output = run.stderr + run.stdout
            if run.returncode:
                print(run.stdout + run.stderr, flush=True)
                raise RuntimeError(f"{project}: {command} failed ({run.returncode})")
        result = summarize(output)
        print(f"{project.name}: {json.dumps(result, sort_keys=True)}", flush=True)
    print("Environment shadow comparisons passed", flush=True)


if __name__ == "__main__":
    main()
