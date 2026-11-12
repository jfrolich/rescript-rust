#!/usr/bin/env python3
"""Clean-build both signature corpora and fail closed on incomplete comparisons."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MINIMUM = ROOT / "compiler-rust/tests/signature_equality_minimum.json"
KINDS = ("fingerprint", "item_hashes", "bytes")


def summarize(directory, prefix=None):
    """Keep every outcome: success never hides a failed/retried compilation."""
    units = {}
    for path in sorted(directory.rglob("*.json")):
        report = json.loads(path.read_text())
        unit = report["unit"]
        if not isinstance(unit, str) or not unit:
            raise RuntimeError(f"{path}: missing unit")
        if prefix and not Path(unit).resolve().is_relative_to(prefix.resolve()):
            continue
        if report["stage"] != "signature-equality":
            raise RuntimeError(f"{unit}: unexpected report stage")
        outcomes = units.setdefault(unit, {kind: [] for kind in KINDS})
        for kind in KINDS:
            outcome = report[kind]
            status = outcome["status"]
            if status not in ("equal", "different", "not_applicable", "pending"):
                raise RuntimeError(f"{unit}: {kind}: invalid status {status}")
            if status == "different" and not outcome.get("detail"):
                raise RuntimeError(f"{unit}: {kind}: difference without detail")
            if status == "not_applicable" and not outcome.get("reason"):
                raise RuntimeError(f"{unit}: {kind}: not applicable without reason")
            outcomes[kind].append(outcome)
    result = {"units": len(units)}
    for kind in KINDS:
        counts = Counter()
        reasons = Counter()
        differences = []
        for unit, outcomes in units.items():
            values = outcomes[kind]
            failures = [v for v in values if v["status"] == "different"]
            unavailable = {v["reason"] for v in values if v["status"] == "not_applicable"}
            if failures:
                counts["different"] += 1
                differences.extend(f"{unit}: {v['detail']}" for v in failures)
            elif any(v["status"] == "pending" for v in values):
                counts["pending"] += 1
            elif unavailable:
                # One count per unit; preserve all reasons rather than picking
                # an arbitrary lexicographically first reason.
                reasons["; ".join(sorted(unavailable))] += 1
            else:
                counts["equal"] += 1
        result[kind] = {
            "compared": counts["equal"] + counts["different"],
            "equal": counts["equal"], "different": counts["different"],
            "pending": counts["pending"],
            "not_applicable": dict(sorted(reasons.items())),
            "differences": differences,
        }
    return result


def check(results, minimum):
    for corpus, floor in minimum.items():
        actual = results[corpus]
        if not actual["units"]:
            raise RuntimeError(f"{corpus}: zero reports (check mode was not exercised)")
        if actual["units"] < floor:
            raise RuntimeError(f"{corpus}: unit count {actual['units']} below minimum {floor}")
        for kind in KINDS:
            outcome = actual[kind]
            if outcome["different"]:
                raise RuntimeError(f"{corpus}: {kind}: {outcome['differences']}")
            if outcome["pending"]:
                raise RuntimeError(f"{corpus}: {kind}: {outcome['pending']} comparisons not implemented")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", type=Path, default=ROOT / "rewatch/target/release/rescript")
    args = parser.parse_args()
    executable = args.executable.resolve()
    env = dict(os.environ, RESCRIPT_SIGNATURE_CHECK="1",
               RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"))
    results = {}
    failed = []
    with tempfile.TemporaryDirectory(prefix="signature-equality-") as temporary:
        for corpus, folder in [("runtime", "packages/@rescript/runtime"), ("tests/tests", "tests/tests")]:
            reports = Path(temporary) / corpus.replace("/", "-")
            reports.mkdir()
            env["RESCRIPT_SIGNATURE_CHECK_REPORTS"] = str(reports)
            for command in ("clean", "build"):
                run = subprocess.run([str(executable), command, str(ROOT / folder)],
                                     cwd=ROOT, env=env, capture_output=True, text=True, timeout=60)
                if run.returncode:
                    print(run.stdout + run.stderr)
                    failed.append(f"{corpus}: {command} failed ({run.returncode})")
                    break
            results[corpus] = summarize(reports, ROOT / folder)
    print(json.dumps(results, indent=2, sort_keys=True), flush=True)
    if failed:
        raise RuntimeError("; ".join(failed))
    check(results, json.loads(MINIMUM.read_text()))
    print("Signature equality passed")


if __name__ == "__main__":
    main()
