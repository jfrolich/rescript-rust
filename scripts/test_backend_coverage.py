#!/usr/bin/env python3
"""Run the backend shadow oracles and enforce their per-corpus coverage ratchet.

Stages: `lambda-bridge` (S2.2, the Lambda/Bir bridge round trip) and
`lambda-norm` (S4.1, the Bir normalising rules against LamArena's smart
constructors). Each stage has its own entry in the ratchet file.
"""
import argparse
import collections
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
RATCHET = ROOT / "compiler-rust/tests/backend_coverage.txt"


STAGES = ("lambda-bridge", "lambda-norm", "lambda-flatten")


def summarize(directory, stage, prefix=None):
    reasons = collections.Counter()
    identical = 0
    units = {}
    for path in sorted(directory.rglob("*.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["stage"] not in STAGES:
            raise RuntimeError(f"unexpected report stage: {report['stage']}")
        if report["stage"] != stage:
            continue
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


def rule_counts(directory, prefix=None):
    """Rows of the normalising-rule table fired per corpus (not ratcheted)."""
    totals = {"calls": 0, "replayed": collections.Counter(),
              "renormalised": collections.Counter(), "compared": 0}
    seen = set()
    for path in sorted(directory.rglob("lambda-norm.identical.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["unit"] in seen:
            continue
        seen.add(report["unit"])
        norm = report["norm"]
        totals["calls"] += norm["calls"]
        totals["compared"] += norm["compared"]
        totals["replayed"].update(norm["replayed"])
        totals["renormalised"].update(norm["renormalised"])
    return {"calls": totals["calls"], "compared": totals["compared"],
            "replayed": dict(sorted(totals["replayed"].items())),
            "renormalised": dict(sorted(totals["renormalised"].items()))}


def flatten_counts(directory, prefix=None):
    totals = collections.Counter()
    seen = set()
    for path in sorted(directory.rglob("lambda-flatten.identical.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["unit"] in seen:
            continue
        seen.add(report["unit"])
        totals.update(report["norm"].get("rules", {}))
    return dict(sorted(totals.items()))


def check(actual, baseline):
    for stage in STAGES:
        check_stage(stage, actual[stage], baseline[stage])


def check_stage(stage, actual, baseline):
    for name, old in baseline.items():
        corpus = f"{stage}: {name}"
        new = actual[name]
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
    results = {stage: {} for stage in STAGES}
    rules = {}
    flatten_rules = {}
    with tempfile.TemporaryDirectory(prefix="bir-shadow-") as temporary:
        for corpus, folder in [("runtime", "packages/@rescript/runtime"),
                               ("tests/tests", "tests/tests"), ("fixtures", None)]:
            reports = Path(temporary) / corpus.replace("/", "-")
            reports.mkdir()
            env["RESCRIPT_BACKEND_STATS"] = str(reports)
            # prepare-parity has already built these packages. A warm build
            # can reuse every module and never reach the shadow oracle. Clean
            # through the public CLI first; building the runtime package then
            # compiles its sources even when embedded interfaces are available.
            commands = ([[str(binary), "clean", str(ROOT / folder)],
                         [str(binary), "build", str(ROOT / folder)]] if folder else
                        [["bash", "scripts/test_js_output_parity_fixtures.sh"]])
            log = Path(temporary) / (corpus.replace("/", "-") + ".log")
            with log.open("w") as output:
                for command in commands:
                    result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                            stderr=subprocess.STDOUT, timeout=600)
                    if result.returncode:
                        output.flush()
                        print(log.read_text())
                        raise RuntimeError(f"{corpus}: oracle command failed ({result.returncode})")
            prefix = ROOT / folder if folder else None
            for stage in STAGES:
                results[stage][corpus] = summarize(reports, stage, prefix)
                if not results[stage][corpus]["units"]:
                    raise RuntimeError(
                        f"{stage}: {corpus}: no shadow reports (mode was not exercised)")
            rules[corpus] = rule_counts(reports, prefix)
            flatten_rules[corpus] = flatten_counts(reports, prefix)
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    print(text, end="")
    print("lambda-norm rule firings (not ratcheted):")
    print(json.dumps(rules, indent=2, sort_keys=True))
    print("lambda-flatten rule firings (not ratcheted):")
    print(json.dumps(flatten_rules, indent=2, sort_keys=True))
    if args.record:
        RATCHET.write_text(text)
    else:
        check(results, json.loads(RATCHET.read_text()))
        print("Backend coverage ratchet passed")


if __name__ == "__main__":
    main()
