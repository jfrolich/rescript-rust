#!/usr/bin/env python3
"""Run the S2.2 shadow oracle and enforce its per-corpus coverage ratchet."""
import argparse
import collections
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
RATCHET = ROOT / "compiler-rust/tests/backend_coverage.txt"


def summarize(directory, prefix=None):
    reasons = collections.Counter()
    identical = 0
    units = {}
    for path in sorted(directory.rglob("*.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["stage"] != "lambda-bridge":
            raise RuntimeError(f"unexpected report stage: {report['stage']}")
        if report["unsupported"] is None:
            if not report["identical"]:
                raise RuntimeError("unclassified shadow result")
            units.setdefault(report["unit"], set())
        else:
            if report["identical"]:
                raise RuntimeError("contradictory shadow result")
            units.setdefault(report["unit"], set()).add(report["unsupported"])
    for outcomes in units.values():
        if outcomes:
            reasons[min(outcomes)] += 1
        else:
            identical += 1
    return {"units": identical + sum(reasons.values()), "identical": identical,
            "unsupported": dict(sorted(reasons.items()))}


def check(actual, baseline):
    for corpus, old in baseline.items():
        new = actual[corpus]
        fallback = sum(new["unsupported"].values())
        old_fallback = sum(old["unsupported"].values())
        if new["units"] < old["units"]:
            raise RuntimeError(f"{corpus}: missing units: {new['units']} < {old['units']}")
        if fallback > old_fallback:
            raise RuntimeError(f"{corpus}: fallback count grew: {fallback} > {old_fallback}")
        if new["identical"] * old["units"] < old["identical"] * new["units"]:
            raise RuntimeError(f"{corpus}: supported share fell")
        for reason, count in new["unsupported"].items():
            if count > old["unsupported"].get(reason, 0):
                raise RuntimeError(f"{corpus}: fallback reason grew: {reason}: {count}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=["debug", "release"], default="release")
    parser.add_argument("--record", action="store_true", help="explicitly update the committed baseline")
    args = parser.parse_args()
    binary = ROOT / "rewatch/target" / args.target / "rescript"
    env = dict(os.environ, RESCRIPT_BACKEND="check",
               RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"),
               RUST_TARGET=args.target, REWATCH_TARGET=args.target,
               REWATCH_BIN=str(binary))
    results = {}
    with tempfile.TemporaryDirectory(prefix="bir-shadow-") as temporary:
        for corpus, folder in [("runtime", "packages/@rescript/runtime"),
                               ("tests/tests", "tests/tests"), ("fixtures", None)]:
            reports = Path(temporary) / corpus.replace("/", "-")
            reports.mkdir()
            env["RESCRIPT_BACKEND_STATS"] = str(reports)
            command = ([str(binary), "build", str(ROOT / folder)] if folder else
                       ["bash", "scripts/test_js_output_parity_fixtures.sh"])
            log = Path(temporary) / (corpus.replace("/", "-") + ".log")
            with log.open("w") as output:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                        stderr=subprocess.STDOUT, timeout=600)
            if result.returncode:
                print(log.read_text())
                raise RuntimeError(f"{corpus}: oracle command failed ({result.returncode})")
            results[corpus] = summarize(reports, ROOT / folder if folder else None)
            if not results[corpus]["units"]:
                raise RuntimeError(f"{corpus}: no shadow reports (mode was not exercised)")
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    print(text, end="")
    if args.record:
        RATCHET.write_text(text)
    else:
        check(results, json.loads(RATCHET.read_text()))
        print("Backend coverage ratchet passed")


if __name__ == "__main__":
    main()
