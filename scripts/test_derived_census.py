#!/usr/bin/env python3
"""Integration gate: census-only enablement, phase reconciliation and codec errors.

Run after building rewatch: python3 scripts/test_derived_census.py [--rescript BIN]
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from derived_census_summary import summarize

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rescript", type=Path, default=ROOT / "rewatch/target/debug/rescript")
    args = parser.parse_args()
    binary = args.rescript.resolve()
    project = ROOT / "tests/ppx_spice"
    env = dict(os.environ, RESCRIPT_RUNTIME=str(ROOT / "packages/@rescript/runtime"),
               RAYON_NUM_THREADS="1", NO_COLOR="1")
    for key in ("RESCRIPT_PHASE_TIMINGS", "RESCRIPT_MODULE_TIMINGS", "RESCRIPT_RUNTIME_TIMINGS",
                "RESCRIPT_COMPILER_COUNTERS", "RESCRIPT_DERIVED_CENSUS"):
        env.pop(key, None)

    def run(*args, environment=env, ok=True):
        result = subprocess.run([str(binary), *map(str, args)], env=environment,
                                capture_output=True, text=True, timeout=30)
        if ok and result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        return result

    with tempfile.TemporaryDirectory(prefix="derived-census-") as temporary:
        temporary = Path(temporary)
        only_switch = temporary / "only-switch.jsonl"
        run("clean", project)
        run("build", project, environment=dict(env, RESCRIPT_DERIVED_CENSUS=str(only_switch)))
        records = [json.loads(line) for line in only_switch.read_text().splitlines()]
        totals = summarize(records)
        for phase in ("lambda_lowering", "lambda_passes", "lowering"):
            assert totals[phase]["derived"] > 0, phase
        assert all("/" not in row["module"] and "\\" not in row["module"] for row in records)
        assert totals["unsupported_templates"] == 0
        print("census-only backend timers and module-name privacy: passed")

        reconcile = temporary / "reconcile.jsonl"
        run("clean", project)
        built = run("build", project, environment=dict(env, RESCRIPT_DERIVED_CENSUS=str(reconcile),
                                                       RESCRIPT_PHASE_TIMINGS="1"))
        totals = summarize(json.loads(line) for line in reconcile.read_text().splitlines())
        mapping = dict(parse=("parse_other", "generation", "frontend"), env_setup=("environment",),
                       typecheck=("typecheck",), signature_publish=("signature",),
                       **{"lambda": ("conversion", "lambda_lowering")},
                       lambda_optimization=("lambda_passes",), codegen=("lowering", "printing"))
        for phase, fields in mapping.items():
            match = re.search(r"phase=" + phase + r" ms=([0-9.]+)", built.stdout + built.stderr)
            assert match, phase
            reported = float(match[1])
            measured = sum(totals[field][side] for field in fields for side in ("derived", "other")) / 1e6
            error = abs(measured - reported) / reported if reported else 0
            assert error <= .02, (phase, measured, reported)
            print(f"{phase}: census={measured:.3f} ms phase={reported:.3f} ms delta={error:.3%}")

        # Checker census attribution remains single-worker until equality of
        # shared-world work across worker counts has been established.
        for workers in (1, 4):
            counted = temporary / f"checker-{workers}.jsonl"
            run("clean", project)
            run("build", project, environment=dict(env,
                RAYON_NUM_THREADS=str(workers), RESCRIPT_COMPILER_COUNTERS="1",
                RESCRIPT_DERIVED_CENSUS=str(counted)))
            records = [json.loads(line) for line in counted.read_text().splitlines()]
            assert records
            assert all((record["checker_counters"] is not None) == (workers == 1)
                       for record in records)
            print(f"checker census: workers={workers} enabled={workers == 1}")

        for case in ("missing-codec", "wrong-codec-type"):
            error_project = temporary / case
            error_project.mkdir()
            (error_project / "rescript.json").write_text(json.dumps(dict(
                name="derived-error", sources=["."], **{"ppx-flags": ["ppx-spice"],
                "compiler-flags": ["-warn-error -A"]})))
            for helper in ("Spice.res", "Spice_Codecs.res"):
                shutil.copyfile(project / "src" / helper, error_project / helper)
            shutil.copyfile(project / f"errors/{case}.res", error_project / "Case.res")
            failed = run("build", error_project, ok=False)
            diagnostic = failed.stdout + failed.stderr
            assert failed.returncode != 0, case
            assert "Case.res" in diagnostic, diagnostic
            if case == "missing-codec":
                assert "encode" in diagnostic and "Custom" in diagnostic, diagnostic
            else:
                assert "string" in diagnostic and "int" in diagnostic, diagnostic
            print(f"{case}: checker rejects derived binding")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
