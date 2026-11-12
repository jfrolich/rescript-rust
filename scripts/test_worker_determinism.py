#!/usr/bin/env python3
"""Compare four clean builds: 1 worker, 8 workers, and 8 with shuffle seeds 1/2.

Compare generated files outside lib/ (paths and SHA256), ordered diagnostics
per source file, canonical signatures and stored interface bytes. Exit 0 for
identical output, 1 for differences, 2 for build or collection failures.
Builds run sequentially in the same project; snapshots are kept separately.
"""

import argparse
import hashlib
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile

from compare_checker_builds import Side, compare_diagnostics, compare_files, fail, report, walk
from test_stored_interface_determinism import ROOT, compare, read_interfaces


class Build(Side):
    def run(self, *args):
        return subprocess.run(
            [self.executable, *args], env=self.env, capture_output=True,
            text=True, errors="replace", timeout=300,
        )


def output_candidates(project):
    """All possible outputs, not just known JavaScript/TypeScript suffixes.

    Comparing the post-clean and post-build metadata excludes unchanged
    sources and configuration. ctime also catches an output whose mtime was
    preserved by a generator. Side copies each changed file before the next
    clean so no comparison ever reads a later build's output.
    """
    result = {}
    for path in walk(project):
        relative = path.relative_to(project)
        if "lib" not in relative.parts:
            stat = path.stat()
            result[relative] = (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
    return result


def generated_hashes(side):
    return {name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in side.generated.items()}


def interfaces(project):
    """Include databases of installed ReScript packages, not just the root."""
    result = {}
    for path in sorted(walk(project)):
        if path.name == "rescript.sqlite" and path.parent.name in ("rescript", "bs"):
            prefix = path.relative_to(project).as_posix()
            for (table, module), data in read_interfaces(path).items():
                result[(f"{prefix}/{table}", module)] = data
    if not result:
        fail("build produced no stored interfaces")
    return result


def compare_generated(base, candidate):
    different = [(name, f"generated: {name}: SHA256 {base.get(name)} != {candidate.get(name)}")
                 for name in sorted(base.keys() | candidate.keys())
                 if base.get(name) != candidate.get(name)]
    report("generated", different, len(base.keys() | candidate.keys()), 3)
    return len(different)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path, default=ROOT / "tests/tests")
    parser.add_argument("--rescript", type=Path,
                        default=Path(os.environ.get("RESCRIPT_EXECUTABLE",
                                                    ROOT / "rewatch/target/release/rescript")))
    parser.add_argument("--runtime", type=Path,
                        default=Path(os.environ.get("RESCRIPT_RUNTIME",
                                                    ROOT / "packages/@rescript/runtime")))
    parser.add_argument("--work-dir", type=Path, help="where to retain build snapshots")
    args = parser.parse_args(argv)
    project = args.project.resolve()
    work = (args.work_dir or Path(tempfile.mkdtemp(prefix="worker-determinism-"))).resolve()
    work.mkdir(parents=True, exist_ok=True)
    snapshots = []
    try:
        for workers, seed in ((1, None), (8, None), (8, "1"), (8, "2")):
            name = f"workers-{workers}-shuffle-{seed or 'off'}"
            side = Build(name, args.rescript, args.runtime, project, work, [])
            side.env["RAYON_NUM_THREADS"] = str(workers)
            side.env.pop("RESCRIPT_WORLD_SHUFFLE", None)
            if seed is not None:
                side.env["RESCRIPT_WORLD_SHUFFLE"] = seed
            if not side.has_signatures:
                fail("executable does not support canonical signature dumps")
            side.build(True, candidates=output_candidates)
            if side.exit_code != 0:
                fail(f"{name}: build failed; see {side.directory / 'build.log'}")
            if not side.signatures:
                fail(f"{name}: build produced no canonical signatures")
            snapshots.append((side, generated_hashes(side), interfaces(project)))
        base, base_hashes, base_interfaces = snapshots[0]
        differences = 0
        for candidate, hashes, stored in snapshots[1:]:
            print(f"\n{base.name} versus {candidate.name}:")
            differences += compare_generated(base_hashes, hashes)
            differences += compare_diagnostics(base.diagnostics, candidate.diagnostics, 3, 40)
            differences += compare_files("signatures", base.signatures, candidate.signatures, 3, 40)
            print("stored interfaces:")
            differences += not compare(base_interfaces, stored)
        print(f"\nBuild snapshots: {work}")
        return 1 if differences else 0
    except (OSError, ValueError, sqlite3.Error, subprocess.SubprocessError) as error:
        fail(str(error))


if __name__ == "__main__":
    sys.exit(main())
