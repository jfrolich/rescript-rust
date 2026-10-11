#!/usr/bin/env python3
"""Build a project with the OCaml reference compiler.

`rescript build` compiles in-process and writes no .ast/.cmi/.cmj/.cmt files.
The parity scripts compare against the OCaml `bsc`, which needs them, so this
runs the file-backed build that `rescript build-plan` prints: each module's
`bsc` commands in dependency order, copying its artifacts into lib/ocaml
after each command.

Usage: build_ocaml_reference.py [--bsc PATH] [--rescript PATH] [--jobs N]
                                [--prod] [PROJECT]

Run it after any `rescript build` of the same project: a build with a
different compiler identity cleans lib/bs and lib/ocaml, including these
artifacts. Exits non-zero when a module fails; the modules depending on it
are skipped.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def default_bsc():
    """The dune-built OCaml bsc, or its copy in the platform npm package."""
    dune = ROOT / "_build/install/default/bin/bsc"
    if dune.exists():
        return dune
    platform = subprocess.run(
        [ROOT / "scripts/platform.sh"], stdout=subprocess.PIPE, text=True, check=True
    ).stdout.strip()
    return ROOT / "packages/@rescript" / platform / "bin/bsc.exe"


def run_step(bsc, step):
    for directory in [step["cwd"], *step["mkdirs"]]:
        os.makedirs(directory, exist_ok=True)
    for args in step["commands"]:
        result = subprocess.run(
            [bsc, *args], cwd=step["cwd"], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        if result.returncode != 0:
            output = (result.stderr + result.stdout).decode("utf-8", "replace")
            return f"{step['package']}: {step['module']}\n{output}"
        # Publish what each command wrote before the next one runs: an
        # implementation compile finds its interface's .cmi in lib/ocaml.
        for source, target in step["copies"]:
            if os.path.exists(source):
                shutil.copyfile(source, target)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("project", nargs="?", default=".")
    parser.add_argument("--bsc", default=os.environ.get("OCAML_BSC", default_bsc()))
    parser.add_argument(
        "--rescript",
        default=os.environ.get("RESCRIPT_CLI", ROOT / "rewatch/target/release/rescript"),
    )
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    parser.add_argument("--prod", action="store_true")
    args = parser.parse_args()

    args.bsc = os.path.abspath(args.bsc)
    plan_cmd = [os.path.abspath(args.rescript), "build-plan", args.project]
    if args.prod:
        plan_cmd.append("--prod")
    plan = subprocess.run(plan_cmd, stdout=subprocess.PIPE, check=True)
    steps = json.loads(plan.stdout)["steps"]

    by_module = {step["module"]: step for step in steps}
    pending = {step["module"]: {d for d in step["deps"] if d in by_module} for step in steps}
    dependents = {}
    for module, deps in pending.items():
        for dep in deps:
            dependents.setdefault(dep, []).append(module)

    ready = [m for m, deps in pending.items() if not deps]
    failed, skipped = [], set()
    running = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while ready or running:
            while ready and len(running) < args.jobs:
                module = ready.pop()
                running[pool.submit(run_step, str(args.bsc), by_module[module])] = module
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                error = future.result()
                blocked = []
                if error is not None:
                    failed.append(error)
                    blocked = dependents.get(module, [])
                for dependent in dependents.get(module, []):
                    pending[dependent].discard(module)
                    if dependent in blocked:
                        skipped.add(dependent)
                    elif not pending[dependent] and dependent not in skipped:
                        ready.append(dependent)

    # Modules whose dependencies failed never ran; report them.
    for module, deps in pending.items():
        if deps or module in skipped:
            skipped.add(module)
    built = len(steps) - len(failed) - len(skipped)
    print(f"OCaml reference build: {built} of {len(steps)} modules built")
    for error in failed:
        print(error, file=sys.stderr)
    if skipped:
        print(f"skipped {len(skipped)} modules after failures", file=sys.stderr)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
