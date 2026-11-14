#!/usr/bin/env python3
"""Run the backend shadow oracles and enforce their per-corpus coverage ratchet.

Stages: `lambda-bridge` (S2.2), `lambda-norm` and `lambda-flatten` (S4),
and `js-bridge` (S3.1a, the post-pass JS/Bir round trip). Each stage has
its own entry in the ratchet file.
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


STAGES = ("lambda-bridge", "lambda-norm", "lambda-flatten", "lambda-exits", "lambda-alias",
          "js-bridge", "lower")


def summarize(directory, stage, prefix=None):
    reasons = collections.Counter()
    identical = 0
    units = {}
    shared_catch_only = set()
    for path in sorted(directory.rglob("*.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["stage"] not in STAGES:
            raise RuntimeError(f"unexpected report stage: {report['stage']}")
        if report["stage"] != stage:
            continue
        if report.get("shared_catch_only", False):
            shared_catch_only.add(report["unit"])
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
    result = {"units": identical + sum(reasons.values()), "identical": identical,
              "unsupported": dict(sorted(reasons.items()))}
    if stage == "lower":
        result["shared_catch_only"] = len(shared_catch_only)
    return result


def lower_counts(directory, prefix=None):
    """Work of successful lowering invocations, deduplicated by unit path."""
    totals = collections.Counter()
    seen = set()
    for path in sorted(directory.rglob("lower.identical.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["unit"] in seen:
            continue
        seen.add(report["unit"])
        totals["units"] += 1
        totals.update(report.get("lower", {}))
    return dict(sorted(totals.items()))


# THREE_TREES 11.4, "T5 part B as redesigned" (d): what the naming log's
# replay gets wrong against the naming pass. The gate requires zero.
NAME_DIFFERENCES = ("name_differences", "finish_differences", "free_differences",
                    "ambiguous_orders", "unnamed_references")


def naming_counts(work):
    """The naming gate of one corpus from its summed lowering work."""
    return {"compared": work.get("names_compared", 0),
            "uncompared": work.get("names_uncompared", 0),
            "adopted_nodes": work.get("adopted_nodes", 0),
            "differences": sum(work.get(key, 0) for key in NAME_DIFFERENCES)}


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


def flatten_counts(directory, prefix=None, stage="lambda-flatten"):
    totals = collections.Counter()
    seen = set()
    for path in sorted(directory.rglob(f"{stage}.identical.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["unit"] in seen:
            continue
        seen.add(report["unit"])
        totals.update(report["norm"].get("rules", {}))
    return dict(sorted(totals.items()))


def fact_counts(directory, prefix=None):
    """Binders whose fact was compared with the legacy table, per kind."""
    totals = collections.Counter()
    seen = set()
    for path in sorted(directory.rglob("lambda-alias.*.json")):
        report = json.loads(path.read_text())
        if prefix and not Path(report["unit"]).resolve().is_relative_to(prefix):
            continue
        if report["unit"] in seen or "facts" not in report:
            continue
        seen.add(report["unit"])
        totals.update(report["facts"])
    return dict(sorted(totals.items()))


# The ratchet entry for the units the naming pass rejects, per corpus: those
# units have no oracle, so their number may fall and never rise.
UNCOMPARED = "names-uncompared"


def ratchet(results, naming):
    """The ratchet file's content: the stages and the uncompared units."""
    recorded = dict(results)
    recorded[UNCOMPARED] = {corpus: counts["uncompared"] for corpus, counts in naming.items()}
    return recorded


def write_record(path, results, naming):
    path.write_text(json.dumps(ratchet(results, naming), indent=2, sort_keys=True) + "\n")


def check(actual, baseline):
    for stage in STAGES:
        check_stage(stage, actual[stage], baseline[stage])
    check_uncompared(actual[UNCOMPARED], baseline[UNCOMPARED])


def check_uncompared(actual, baseline):
    for corpus, old in baseline.items():
        new = actual[corpus]
        if new > old:
            raise RuntimeError(f"{UNCOMPARED}: {corpus}: uncompared units grew: {new} > {old}")


def check_stage(stage, actual, baseline):
    for name, old in baseline.items():
        corpus = f"{stage}: {name}"
        new = actual[name]
        fallback = sum(new["unsupported"].values())
        old_fallback = sum(old["unsupported"].values())
        if new["units"] < old["units"]:
            raise RuntimeError(f"{corpus}: missing units: {new['units']} < {old['units']}")
        # A corpus grows when tests are added. A unit added to a corpus that
        # already has fallbacks may be one more. No existing unit may become
        # one: units are identical plus fallbacks, so fallbacks growing by at
        # most the units added means the identical count did not fall. A
        # corpus without fallbacks keeps none.
        added = new["units"] - old["units"]
        if fallback > old_fallback + added:
            raise RuntimeError(f"{corpus}: fallback count grew: {fallback} > {old_fallback}")
        if fallback and not old_fallback:
            raise RuntimeError(f"{corpus}: a fully supported corpus gained a fallback")
        for reason, count in new["unsupported"].items():
            if count > old["unsupported"].get(reason, 0) + added:
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
    lowering_work = {}
    flatten_rules = {}
    exits_rules = {}
    alias_rules = {}
    alias_facts = {}
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
            lowering_work[corpus] = lower_counts(reports, prefix)
            for stage in STAGES:
                results[stage][corpus] = summarize(reports, stage, prefix)
                if not results[stage][corpus]["units"]:
                    raise RuntimeError(
                        f"{stage}: {corpus}: no shadow reports (mode was not exercised)")
            rules[corpus] = rule_counts(reports, prefix)
            flatten_rules[corpus] = flatten_counts(reports, prefix)
            exits_rules[corpus] = flatten_counts(reports, prefix, "lambda-exits")
            alias_rules[corpus] = flatten_counts(reports, prefix, "lambda-alias")
            alias_facts[corpus] = fact_counts(reports, prefix)
    print(json.dumps(results, indent=2, sort_keys=True))
    print("lambda-norm rule firings (not ratcheted):")
    print(json.dumps(rules, indent=2, sort_keys=True))
    print("lambda-flatten rule firings (not ratcheted):")
    print(json.dumps(flatten_rules, indent=2, sort_keys=True))
    print("lambda-exits rule firings (not ratcheted):")
    print(json.dumps(exits_rules, indent=2, sort_keys=True))
    print("lambda-alias rule firings (not ratcheted):")
    print(json.dumps(alias_rules, indent=2, sort_keys=True))
    print("lambda-alias binders compared with the legacy table, per kind (not ratcheted):")
    print(json.dumps(alias_facts, indent=2, sort_keys=True))
    print("Lowering work (successful units only): " + json.dumps(lowering_work, indent=2, sort_keys=True))
    naming = {corpus: naming_counts(work) for corpus, work in lowering_work.items()}
    for corpus, counts in naming.items():
        print(f"Naming log against the pass: {corpus}: compared {counts['compared']}, "
              f"uncompared {counts['uncompared']}, adopted_nodes {counts['adopted_nodes']}, "
              f"sum of (d) {counts['differences']}")
    if args.record:
        write_record(RATCHET, results, naming)
    else:
        check(ratchet(results, naming), json.loads(RATCHET.read_text()))
        print("Backend coverage ratchet passed")
    differing = {corpus: counts["differences"] for corpus, counts in naming.items() if counts["differences"]}
    if differing:
        raise RuntimeError(f"the naming log differs from the pass: {differing}")


if __name__ == "__main__":
    main()
