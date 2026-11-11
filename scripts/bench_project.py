#!/usr/bin/env python3
"""Implementation of bench_project.sh (all paths in digests are project-relative)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


EXTENSIONS = {".js", ".mjs", ".cjs", ".ts", ".tsx"}


def files(root):
    # Follow linked dependencies, but visit each physical directory only once
    # (including the copied Belt), also preventing symlink cycles.
    visited = set()
    for directory, dirs, names in os.walk(root, followlinks=True):
        real = Path(directory).resolve()
        if real in visited:
            dirs[:] = []
            continue
        visited.add(real)
        dirs[:] = sorted(d for d in dirs if d != ".git")
        for name in sorted(names):
            yield Path(directory) / name


def snapshot(project):
    return {
        p.relative_to(project).as_posix(): (p.stat().st_mtime_ns, p.stat().st_ctime_ns, p.stat().st_size)
        for p in files(project) if p.suffix in EXTENSIONS
    }


def generated(project, before):
    after = snapshot(project)
    return {
        name: hashlib.sha256((project / name).read_bytes()).hexdigest()
        for name in sorted(after) if before.get(name) != after[name]
    }


def digest(outputs):
    # NUL framing makes paths with whitespace/newlines unambiguous.
    h = hashlib.sha256()
    for name, content in sorted(outputs.items()):
        h.update(os.fsencode(name) + b"\0" + content.encode("ascii") + b"\0")
    return h.hexdigest()


def run(command, project, env):
    start = time.monotonic()
    result = subprocess.run([str(c) for c in command], cwd=project, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    if result.returncode:
        output = result.stdout.decode(errors="replace")
        # Start at the first compiler error where possible, retaining context.
        lines = output.splitlines()
        first = next((i for i, line in enumerate(lines)
                      if re.search(r"error|We've found a bug", line, re.I)), 0)
        print("\n".join(lines[first:first + 40]), file=sys.stderr)
        raise RuntimeError(f"{Path(command[0]).name} {' '.join(map(str, command[1:2]))} failed (exit {result.returncode})")
    return elapsed


def source_lines(project):
    # All physical .res/.resi files, including dependencies and build copies.
    return sum(len(p.read_bytes().splitlines()) for p in files(project)
               if p.suffix in {".res", ".resi"})


def prepare(project, checkout, work):
    packages = project / ".rescript-pkgs"
    packages.mkdir(exist_ok=True)
    link = project / "node_modules/@rescript/belt"
    if link.exists() and not link.is_symlink():
        raise RuntimeError("node_modules/@rescript/belt is a real directory; move it aside before benchmarking")
    for name in ("runtime", "belt"):
        source = checkout / "packages/@rescript" / name
        target = packages / name
        if not source.is_dir():
            raise RuntimeError(f"missing compiler package: {source}")
        if target.resolve() == source.resolve():
            raise RuntimeError("runtime source and destination must differ")
        # Fresh source-only copies: never import stale build artifacts.
        staged = work / (name + "-source")
        shutil.copytree(source, staged, ignore=shutil.ignore_patterns("lib", "node_modules", ".git"))
        if target.exists() or target.is_symlink():
            target.rename(work / (name + "-previous"))
        shutil.move(str(staged), target)
    link.parent.mkdir(parents=True, exist_ok=True)
    if link.is_symlink():
        link.unlink()
    link.symlink_to(packages / "belt", target_is_directory=True)
    return packages / "runtime"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project_dir", type=Path)
    parser.add_argument("base_rescript", type=Path)
    parser.add_argument("candidate_rescript", type=Path)
    parser.add_argument("--runtime-from", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--no-instructions", action="store_true")
    args = parser.parse_args()
    project = args.project_dir.resolve()
    if not (project / "rescript.json").is_file():
        raise RuntimeError("PROJECT_DIR must contain rescript.json")
    binaries = [p.resolve() for p in (args.base_rescript, args.candidate_rescript)]
    for binary in binaries:
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise RuntimeError(f"not an executable: {binary}")
    if not args.no_instructions and not shutil.which("valgrind"):
        raise RuntimeError("valgrind is required; install it or pass --no-instructions")
    results, outputs = {}, []
    # Same filesystem permits moving previous managed package copies aside.
    with tempfile.TemporaryDirectory(prefix=".bench-project-", dir=project.parent) as tmp:
        work = Path(tmp)
        runtime = prepare(project, args.runtime_from.resolve(), work)
        env = dict(os.environ, RESCRIPT_RUNTIME=str(runtime))
        for label, binary in zip(("base", "candidate"), binaries):
            run([binary, "clean", project], project, env)
            run([binary, "clean", runtime], project, env)
            run([binary, "build", runtime], project, env)
            before = snapshot(project)
            seconds = run([binary, "build", project], project, env)
            output = generated(project, before)
            if not output:
                raise RuntimeError(f"{label} build generated no output files")
            outputs.append(output)
            result = {"files": len(output), "sha256": digest(output), "seconds": seconds}
            print(f"{label}: files={len(output)} sha256={result['sha256']} seconds={seconds:.6f}", flush=True)
            if not args.no_instructions:
                run([binary, "clean", project], project, env)
                cg = work / f"{label}.cachegrind"
                seconds = run(["valgrind", "--tool=cachegrind", "--cache-sim=no",
                               f"--cachegrind-out-file={cg}", binary, "build", project],
                              project, dict(env, RAYON_NUM_THREADS="1"))
                match = re.search(r"^summary:\s+(\d+)\s*$", cg.read_text(), re.M)
                if not match or int(match[1]) == 0:
                    raise RuntimeError("missing or invalid Cachegrind instruction summary")
                lines = source_lines(project)
                if not lines:
                    raise RuntimeError("no source lines found")
                result.update(instructions=int(match[1]), source_lines=lines,
                              instructions_per_line=int(match[1]) / lines, cachegrind_seconds=seconds)
                print(f"{label}: instructions={match[1]} source_lines={lines} "
                      f"instructions_per_line={result['instructions_per_line']:.3f} seconds={seconds:.6f}", flush=True)
            results[label] = result
    identical = outputs[0] == outputs[1]
    print("Outputs identical" if identical else "Outputs differ (first 20 paths):")
    if not identical:
        different = sorted(name for name in outputs[0].keys() | outputs[1].keys()
                           if outputs[0].get(name) != outputs[1].get(name))
        for name in different[:20]:
            print(json.dumps(name))
    if not args.no_instructions:
        delta = 100 * (results["candidate"]["instructions"] / results["base"]["instructions"] - 1)
        results["instructions_delta_percent"] = delta
        print(f"Instructions difference: {delta:+.4f}%")
    print("BENCH_PROJECT " + json.dumps(dict(status="identical" if identical else "different", **results), sort_keys=True))
    return 0 if identical else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as error:
        if error.code == 2:
            print('BENCH_PROJECT {"status":"error"}')
        raise
    except (OSError, RuntimeError, ValueError) as error:
        print(f"bench_project: {error}", file=sys.stderr)
        print('BENCH_PROJECT {"status":"error"}')
        sys.exit(2)
