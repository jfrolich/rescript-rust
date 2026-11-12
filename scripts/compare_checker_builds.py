#!/usr/bin/env python3
"""Compare what two `rescript` executables make of one project.

Builds PROJECT from clean with BASE, then with CANDIDATE, and compares:

  signatures   each module's exported signature in canonical form
               (`rescript build --dump sig`), which does not depend on type
               node identity or identifier stamps
  diagnostics  every warning and error of the compiler logs, with its
               location, per source file and in order
  javascript   every file the build generates outside `lib/rescript`,
               `lib/bs` and `lib/ocaml`: JavaScript, genType output, source maps

It prints the first differences of each kind and exits with 1 when there is
any, 0 when there is none, 2 when it could not run. It works on any ReScript
project. Compiler logs are read from `lib/rescript` (or the older `lib/bs`);
a build with no compiler log is an error, not an empty diagnostics comparison.
Signature dumps use an explicit temporary `--dump-dir`, outside the build layout.

  scripts/compare_checker_builds.py PROJECT BASE_RESCRIPT CANDIDATE_RESCRIPT

The builds run one after the other in PROJECT itself, so the project is left
as the candidate built it. A project whose JavaScript is generated next to
its sources has those files removed by the clean and written again by the
build.

Only what is under PROJECT is read: the diagnostics and generated files of a
dependency installed outside it (in a parent's `node_modules`) are not
compared, its signatures are.

`RESCRIPT_RUNTIME` is passed on to both executables. Give `--base-runtime`
and `--candidate-runtime` when each has its own runtime package; a runtime
named either way is built by its executable before the project.

Both builds are full builds (`RESCRIPT_FULL_BUILD`): the state one executable
leaves in the project does not decide what the other compiles.

When an executable does not know the `sig` dump (one older than this script),
both are built without it and signatures are not compared.
"""

import argparse
import difflib
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

GENERATED_SUFFIXES = (".js", ".mjs", ".cjs", ".jsx", ".ts", ".tsx", ".map")
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
# `  <path>:<line>:<column>`, optionally `-<column>` or `-<line>:<column>`.
LOCATION = re.compile(r"^  (\S.*?):(\d+)(:\d+)?(-\d+(:\d+)?)?$")


def fail(message):
    print(f"error: {message}", file=sys.stderr)
    raise SystemExit(2)


def is_rescript_package(directory):
    return (directory / "rescript.json").is_file() or (directory / "bsconfig.json").is_file()


def walk(project):
    """The files of the project and of the ReScript packages installed in it.

    Symbolic links are not followed, version control is skipped, and under
    `node_modules` only packages with a ReScript configuration are entered.
    """
    stack = [project]
    while stack:
        directory = stack.pop()
        try:
            entries = sorted(os.scandir(directory), key=lambda entry: entry.name)
        except OSError:
            continue
        in_node_modules = directory.name == "node_modules"
        in_scope = in_node_modules or (
            directory.name.startswith("@") and directory.parent.name == "node_modules"
        )
        for entry in entries:
            path = Path(entry.path)
            if entry.is_symlink():
                continue
            if entry.is_dir():
                if entry.name == ".git":
                    continue
                if in_scope and not entry.name.startswith("@") and not is_rescript_package(path):
                    continue
                stack.append(path)
            elif entry.is_file():
                yield path


def is_build_internal(relative):
    parts = relative.parts
    return any(
        parts[index] == "lib" and parts[index + 1] in ("rescript", "bs", "ocaml")
        for index in range(len(parts) - 1)
    )


def generated_candidates(project):
    """Path -> (size, mtime) of every file that could be a build output."""
    found = {}
    for path in walk(project):
        relative = path.relative_to(project)
        if path.name.endswith(GENERATED_SUFFIXES) and not is_build_internal(relative):
            stat = path.stat()
            found[relative] = (stat.st_size, stat.st_mtime_ns)
    return found


def compiler_logs(project):
    return [path for path in walk(project)
            if path.name == ".compiler.log"
            and path.parent.name in ("rescript", "bs")
            and path.parent.parent.name == "lib"]


def diagnostics_of(project, text):
    """Source file -> the diagnostics reported in it, in order.

    A diagnostic is its heading line, the location line under it, and what
    follows up to the next heading. Paths are made relative to the project.
    """
    root = str(project)
    lines = [ANSI.sub("", line.rstrip()) for line in text.splitlines()]
    lines = [line for line in lines if not line.startswith(("#Start(", "#Done("))]
    starts = [
        index - 1
        for index, line in enumerate(lines)
        if index > 0 and LOCATION.match(line) and lines[index - 1].strip()
    ]
    by_file = {}
    if starts and starts[0] > 0:
        preamble = "\n".join(lines[: starts[0]]).strip()
        if preamble:
            by_file.setdefault("(no location)", []).append(preamble)
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        block = "\n".join(lines[start:end]).strip("\n").replace(root, "<project>")
        source = LOCATION.match(lines[start + 1]).group(1)
        if source.startswith(root):
            source = os.path.relpath(source, root)
        by_file.setdefault(source, []).append(block)
    if not starts:
        rest = "\n".join(lines).strip()
        if rest:
            by_file.setdefault("(no location)", []).append(rest.replace(root, "<project>"))
    return by_file


class Side:
    def __init__(self, name, executable, runtime, project, work_dir, build_args):
        self.name = name
        self.executable = str(Path(executable).resolve())
        if not os.access(self.executable, os.X_OK):
            fail(f"{executable} is not an executable")
        self.project = project
        # A new directory every run: nothing of an earlier run is read or
        # removed.
        self.directory = Path(tempfile.mkdtemp(prefix=f"{name}-", dir=work_dir))
        self.sig_directory = self.directory / "sig"
        self.generated_directory = self.directory / "generated"
        self.build_args = build_args
        self.env = dict(os.environ, RESCRIPT_FULL_BUILD="1")
        self.runtime = runtime
        if runtime:
            self.env["RESCRIPT_RUNTIME"] = str(Path(runtime).resolve())
        # Without `--dump-dir` the command line is rejected before anything
        # is built, for the unknown dump kind or for the missing directory.
        probe = self.run("build", str(project), "--dump", "sig")
        self.has_signatures = "unknown dump kind" not in probe.stderr
        self.exit_code = None
        self.signatures = {}
        self.diagnostics = {}
        self.generated = {}

    def run(self, *args):
        return subprocess.run(
            [self.executable, *args], env=self.env, capture_output=True, text=True, errors="replace"
        )

    def build(self, with_signatures, candidates=generated_candidates):
        if self.runtime:
            result = self.run("build", self.env["RESCRIPT_RUNTIME"])
            if result.returncode != 0:
                sys.stderr.write(result.stdout + result.stderr)
                fail(f"{self.name}: building the runtime package failed")
        result = self.run("clean", str(self.project))
        if result.returncode != 0:
            sys.stderr.write(result.stdout + result.stderr)
            fail(f"{self.name}: `rescript clean` failed")
        before = candidates(self.project)

        build = ["build", str(self.project), *self.build_args]
        if with_signatures:
            build += ["--dump", "sig", "--dump-dir", str(self.sig_directory)]
        result = self.run(*build)
        self.exit_code = result.returncode
        (self.directory / "build.log").write_text(result.stdout + result.stderr)

        for path in sorted(self.sig_directory.rglob("*.sig")) if with_signatures else []:
            self.signatures[str(path.relative_to(self.sig_directory))[: -len(".sig")]] = path
        logs = compiler_logs(self.project)
        if not logs:
            fail(f"{self.name}: build produced no compiler log under {self.project}; "
                 "expected lib/rescript/.compiler.log or lib/bs/.compiler.log "
                 "in a ReScript package")
        for log in logs:
            text = log.read_text(errors="replace")
            for source, blocks in diagnostics_of(self.project, text).items():
                self.diagnostics.setdefault(source, []).extend(blocks)
        for relative, stat in candidates(self.project).items():
            if before.get(relative) == stat:
                continue
            copy = self.generated_directory / relative
            copy.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.project / relative, copy)
            self.generated[str(relative)] = copy
        print(
            f"{self.name}: exit code {self.exit_code}, "
            f"{len(self.signatures) if with_signatures else 'no'} signatures, "
            f"{sum(map(len, self.diagnostics.values()))} diagnostics in {len(self.diagnostics)} files, "
            f"{len(self.generated)} generated files",
            file=sys.stderr,
        )


def digest(path):
    return hashlib.blake2b(path.read_bytes(), digest_size=16).digest()


def unified(base_text, candidate_text, name, limit):
    lines = list(
        difflib.unified_diff(
            base_text.splitlines(),
            candidate_text.splitlines(),
            f"base/{name}",
            f"candidate/{name}",
            lineterm="",
            n=2,
        )
    )
    if len(lines) > limit:
        lines = lines[:limit] + [f"... {len(lines) - limit} more lines"]
    return "\n".join(lines)


def read(path):
    return path.read_text(errors="replace")


def compare_files(kind, base, candidate, max_diffs, diff_lines):
    """Compare two name -> file maps. Returns the names that differ."""
    different = []
    for name in sorted(base.keys() | candidate.keys()):
        if name not in candidate:
            different.append((name, f"{kind}: {name}: only the base has it"))
        elif name not in base:
            different.append((name, f"{kind}: {name}: only the candidate has it"))
        elif digest(base[name]) != digest(candidate[name]):
            shown = unified(read(base[name]), read(candidate[name]), name, diff_lines)
            different.append((name, f"{kind}: {name} differs\n{shown}"))
    report(kind, different, len(base.keys() | candidate.keys()), max_diffs)
    return len(different)


def compare_diagnostics(base, candidate, max_diffs, diff_lines):
    different = []
    for source in sorted(base.keys() | candidate.keys()):
        base_blocks = base.get(source, [])
        candidate_blocks = candidate.get(source, [])
        if base_blocks == candidate_blocks:
            continue
        shown = unified(
            "\n\n".join(base_blocks), "\n\n".join(candidate_blocks), source, diff_lines
        )
        different.append(
            (
                source,
                f"diagnostics: {source}: {len(base_blocks)} in the base, "
                f"{len(candidate_blocks)} in the candidate\n{shown}",
            )
        )
    report("diagnostics", different, len(base.keys() | candidate.keys()), max_diffs)
    return len(different)


def report(kind, different, total, max_diffs):
    if not different:
        print(f"{kind}: no difference ({total} compared)")
        return
    print(f"{kind}: {len(different)} of {total} differ")
    for _, text in different[:max_diffs]:
        print(text)
        print()
    if len(different) > max_diffs:
        rest = ", ".join(name for name, _ in different[max_diffs : max_diffs + 20])
        print(f"{kind}: and {len(different) - max_diffs} more: {rest}")
        print()


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("project", help="the project directory, built in place")
    parser.add_argument("base", help="the base `rescript` executable")
    parser.add_argument("candidate", help="the candidate `rescript` executable")
    parser.add_argument("--base-runtime", help="RESCRIPT_RUNTIME for the base")
    parser.add_argument("--candidate-runtime", help="RESCRIPT_RUNTIME for the candidate")
    parser.add_argument(
        "--build-arg",
        action="append",
        default=[],
        help="an extra argument for both `rescript build` commands (repeatable)",
    )
    parser.add_argument("--max-diffs", type=int, default=3, help="differences shown per kind")
    parser.add_argument("--diff-lines", type=int, default=40, help="lines shown per difference")
    parser.add_argument("--work-dir", help="where to keep what each side produced")
    args = parser.parse_args()

    project = Path(args.project).resolve()
    if not is_rescript_package(project):
        fail(f"{project} has no rescript.json")
    work_dir = Path(args.work_dir or tempfile.mkdtemp(prefix="compare-checker-builds-")).resolve()
    work_dir.mkdir(parents=True, exist_ok=True)

    base = Side("base", args.base, args.base_runtime, project, work_dir, args.build_arg)
    candidate = Side(
        "candidate", args.candidate, args.candidate_runtime, project, work_dir, args.build_arg
    )
    with_signatures = base.has_signatures and candidate.has_signatures
    base.build(with_signatures)
    candidate.build(with_signatures)

    differences = 0
    if base.exit_code != candidate.exit_code:
        differences += 1
        print(f"outcome: the base exits with {base.exit_code}, the candidate with {candidate.exit_code}")
    else:
        print(f"outcome: both exit with {base.exit_code}")
    if with_signatures:
        differences += compare_files(
            "signatures", base.signatures, candidate.signatures, args.max_diffs, args.diff_lines
        )
    else:
        without = " and ".join(side.name for side in (base, candidate) if not side.has_signatures)
        print(f"signatures: not compared, the {without} executable has no `sig` dump")
    differences += compare_diagnostics(
        base.diagnostics, candidate.diagnostics, args.max_diffs, args.diff_lines
    )
    differences += compare_files(
        "javascript", base.generated, candidate.generated, args.max_diffs, args.diff_lines
    )

    print(f"what each side produced is in {work_dir}", file=sys.stderr)
    if differences:
        print(f"{differences} differences")
        return 1
    print("no differences")
    return 0


if __name__ == "__main__":
    sys.exit(main())
