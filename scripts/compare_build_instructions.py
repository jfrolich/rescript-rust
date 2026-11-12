#!/usr/bin/env python3
"""Compare the instructions two `rescript` executables execute in a clean build.

Each side is an executable and a checkout: the executable builds the
checkout's runtime package, then cleans and builds the project
(`tests/tests` by default) under Valgrind's cachegrind, which counts the
instructions the process executes. The build runs on one worker thread, so
the count barely moves between runs of the same executable (about 0.1% from
run to run); the smallest of `--runs` builds (five by default) is the side's count.

Both sides run at the same time, each in its own checkout, so the two
projects must be separate directories.

  scripts/compare_build_instructions.py \\
      --base BASE_RESCRIPT BASE_CHECKOUT --head HEAD_RESCRIPT HEAD_CHECKOUT

Prints a Markdown report (also appended to --summary) and exits with 1 when
the head executes more than --threshold percent more instructions than the
base, unless --allow-increase is given.
"""

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

SUMMARY_LINE = re.compile(r"^summary:\s+(\d+)", re.MULTILINE)
COMPILED_LINE = re.compile(r"Compiled (\d+) modules")


def run(cmd, env, cwd=None):
    result = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True)
    if result.returncode != 0:
        sys.stderr.write(f"$ {' '.join(map(str, cmd))}\n{result.stdout}{result.stderr}")
        raise SystemExit(f"command failed with exit code {result.returncode}")
    return result.stdout + result.stderr


class Side:
    def __init__(self, name, exe, checkout, project, work_dir):
        self.name = name
        self.exe = str(Path(exe).resolve())
        self.checkout = Path(checkout).resolve()
        self.project = self.checkout / project
        self.runtime = self.checkout / "packages" / "@rescript" / "runtime"
        self.work_dir = work_dir
        self.counts = []
        self.modules = None
        self.env = dict(os.environ, RESCRIPT_RUNTIME=str(self.runtime), RAYON_NUM_THREADS="1")

    def prepare(self):
        # Builds of versions before the flat lib/rescript read the runtime's
        # lib/ocaml folder, which only a build of the runtime writes; later
        # ones read the runtime's sources. Not measured.
        run([self.exe, "build", str(self.runtime)], self.env)

    def measure(self, index):
        run([self.exe, "clean", str(self.project)], self.env)
        out_file = self.work_dir / f"{self.name}-{index}.cachegrind"
        output = run(
            [
                "valgrind",
                "--tool=cachegrind",
                "--cache-sim=no",
                f"--cachegrind-out-file={out_file}",
                self.exe,
                "build",
                str(self.project),
            ],
            self.env,
        )
        modules = COMPILED_LINE.findall(output)
        self.modules = int(modules[-1]) if modules else None
        count = int(SUMMARY_LINE.search(out_file.read_text()).group(1))
        self.counts.append((count, out_file))
        return count

    def best(self):
        return min(self.counts)


def function_diff(base_file, head_file, limit):
    """The functions whose counts moved most, from cg_annotate --diff."""
    result = subprocess.run(
        ["cg_annotate", "--diff", str(base_file), str(head_file)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        return f"cg_annotate failed: {result.stderr.strip()}"
    lines = result.stdout.splitlines()
    try:
        start = next(i for i, line in enumerate(lines) if "File:function summary" in line)
    except StopIteration:
        return result.stdout
    body = []
    for line in lines[start + 3 :]:
        if line.startswith("----"):
            break
        if line.strip():
            body.append(line)
    return "\n".join(body[:limit])


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", nargs=2, metavar=("RESCRIPT", "CHECKOUT"), required=True)
    parser.add_argument("--head", nargs=2, metavar=("RESCRIPT", "CHECKOUT"), required=True)
    parser.add_argument("--project", default="tests/tests", help="project to build, relative to each checkout")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--threshold", type=float, default=0.1, help="allowed increase, in percent")
    parser.add_argument("--allow-increase", action="store_true", help="report an increase without failing")
    parser.add_argument("--summary", help="file to append the Markdown report to")
    parser.add_argument("--work-dir", help="where to keep the cachegrind files")
    args = parser.parse_args()

    work_dir = Path(args.work_dir or tempfile.mkdtemp(prefix="instruction-count-"))
    work_dir.mkdir(parents=True, exist_ok=True)
    base = Side("base", *args.base, args.project, work_dir)
    head = Side("head", *args.head, args.project, work_dir)
    if base.project == head.project:
        raise SystemExit("the base and head projects must be separate checkouts")

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(Side.prepare, (base, head)))
        for index in range(args.runs):
            base_count, head_count = pool.map(lambda side: side.measure(index), (base, head))
            print(f"run {index + 1}: base {base_count:,}  head {head_count:,}", file=sys.stderr)

    (base_count, base_file), (head_count, head_file) = base.best(), head.best()
    delta = head_count - base_count
    percent = 100.0 * delta / base_count
    regressed = percent > args.threshold

    def runs(side):
        return ", ".join(f"{count / 1e6:,.1f}" for count, _ in side.counts)

    if regressed and args.allow_increase:
        verdict = f"More instructions than the threshold of +{args.threshold}%, accepted by the pull request."
    elif regressed:
        verdict = f"**More instructions than the threshold of +{args.threshold}%: this change makes the compiler slower.**"
    elif percent < -args.threshold:
        verdict = "Fewer instructions."
    else:
        verdict = f"Within the threshold of +{args.threshold}%."

    report = [
        f"### Instructions of a clean `{args.project}` build",
        "",
        verdict,
        "",
        "| | instructions | runs (millions) | modules |",
        "| --- | ---: | --- | ---: |",
        f"| base | {base_count:,} | {runs(base)} | {base.modules} |",
        f"| head | {head_count:,} | {runs(head)} | {head.modules} |",
        f"| change | {delta:+,} ({percent:+.3f}%) | | |",
        "",
        "One worker thread, counted by cachegrind; the smallest run of each side.",
        "",
        "<details><summary>Functions that changed most</summary>",
        "",
        "```",
        function_diff(base_file, head_file, 40),
        "```",
        "",
        "</details>",
        "",
    ]
    text = "\n".join(report)
    print(text)
    if args.summary:
        with open(args.summary, "a") as summary:
            summary.write(text)
    if base.modules != head.modules:
        print(f"::warning::base compiled {base.modules} modules and head {head.modules}", file=sys.stderr)
    return 1 if regressed and not args.allow_increase else 0


if __name__ == "__main__":
    sys.exit(main())
