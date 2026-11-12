#!/usr/bin/env python3
"""Opt-in oxc parity, output-based coverage, and per-corpus coverage ratchet.

Each corpus is rebuilt by OCaml and Rust. JavaScript is batch-reformatted by
S0's existing tool; genType TypeScript and source maps remain byte comparisons.
--suite external compares legacy and oxc with the SAME Rust binary instead of
OCaml and uses bench_project's package preparation and generated-file inventory.
No external source or path is written to the committed coverage baseline.
"""
import argparse
import collections
from contextlib import contextmanager
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

import bench_project

ROOT = Path(__file__).resolve().parent.parent
RATCHET = ROOT / "compiler-rust/tests/printer_coverage.json"
JS = {".js", ".mjs", ".cjs", ".jsx"}
GENERATED = JS | {".ts", ".tsx", ".map"}


def summarize(directory, outputs, source_root):
    """Deduplicate by actual output file (not module or compilation attempt).

    Any fallback wins if the same output was attempted more than once. Source
    roots exclude dependency outputs from in-repo corpus ratchets; external
    builds use the entire project including its private dependency copies.
    """
    source_root = Path(source_root).resolve()
    outputs = {Path(p).resolve() for p in outputs}
    units = {}
    for path in sorted(directory.rglob("*.json")):
        report = json.loads(path.read_text())
        output = Path(report["output"]).resolve()
        source = report["source"]
        if output not in outputs or not source or not Path(source).resolve().is_relative_to(source_root):
            continue
        emitted, reason = report["emitted"], report["unsupported"]
        if not isinstance(emitted, bool) or emitted != (reason is None):
            raise RuntimeError("contradictory printer report")
        if reason is not None and (not isinstance(reason, str) or not reason):
            raise RuntimeError("invalid printer fallback reason")
        reasons = units.setdefault(output, set())
        if reason is not None:
            reasons.add(reason)
    reasons = collections.Counter(min(reasons) for reasons in units.values() if reasons)
    emitted = sum(not reasons for reasons in units.values())
    if not emitted:
        raise RuntimeError("no outputs emitted by oxc (missing reports or legacy-only build)")
    return {"outputs": len(units), "emitted": emitted, "unsupported": dict(sorted(reasons.items()))}


def check(actual, baseline):
    for name, new in actual.items():
        if not new["emitted"]:
            raise RuntimeError(f"{name}: zero oxc outputs")
        if name not in baseline:
            raise RuntimeError(f"{name}: no baseline; use --record after reviewing coverage")
        old = baseline[name]
        if new["outputs"] < old["outputs"]:
            raise RuntimeError(f"{name}: outputs missing")
        if new["emitted"] < old["emitted"]:
            raise RuntimeError(f"{name}: emitted count fell")
        for reason, count in new["unsupported"].items():
            if reason not in old["unsupported"]:
                raise RuntimeError(f"{name}: new fallback reason: {reason}")
            if count > old["unsupported"][reason]:
                raise RuntimeError(f"{name}: fallback count grew: {reason}")


def inventory(project):
    return {p.relative_to(project).as_posix(): (p.stat().st_mtime_ns, p.stat().st_ctime_ns, p.stat().st_size)
            for p in bench_project.files(project) if p.suffix in GENERATED}


def capture(project, before, destination, include_types):
    after = inventory(project)
    generated = {name for name, stamp in after.items() if before.get(name) != stamp
                 and (include_types or Path(name).suffix in JS | {".map"})}
    if not generated:
        raise RuntimeError("build produced no generated output")
    for name in generated:
        dest = destination / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(project / name, dest)
    return generated


def run(command, env, log, cwd=ROOT):
    start = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log.read_text()[-12000:], file=sys.stderr)
        raise RuntimeError(f"{Path(command[0]).name} failed ({result.returncode}); log: {log}")
    return time.monotonic() - start


@contextmanager
def restore_tracked(project, work):
    """Preserve the user's tracked snapshots, including uncommitted edits."""
    result = subprocess.run(["git", "-C", str(project), "ls-files", "-z"], capture_output=True)
    saved = []
    if result.returncode == 0:
        for relative in result.stdout.decode().split("\0"):
            path = project / relative
            if relative and path.is_file() and path.suffix in GENERATED:
                backup = work / "original" / relative
                backup.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, backup)
                saved.append((path, backup))
    try:
        yield
    finally:
        for path, backup in saved:
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(backup, path)


def compare(reference, candidate, tool, work, env):
    # TS and map bytes are not passed through a JS parser. The complete file
    # sets are checked as well: neither missing nor extra files can be hidden.
    left = {p.relative_to(reference) for p in reference.rglob("*") if p.is_file()}
    right = {p.relative_to(candidate) for p in candidate.rglob("*") if p.is_file()}
    if left != right:
        raise RuntimeError(f"generated file sets differ: missing={sorted(map(str, left - right))[:20]}, extra={sorted(map(str, right - left))[:20]}")
    for name in sorted(left):
        if name.suffix not in JS and (reference / name).read_bytes() != (candidate / name).read_bytes():
            raise RuntimeError(f"non-JavaScript output differs: {name}")
    seconds = run([tool, "compare", reference, candidate, "--split-file", "--drop-decoration-comments"],
                  env, work / "reformat.log")
    print((work / "reformat.log").read_text().strip())
    print(f"Reformat comparison: {seconds:.3f}s; {len(left)} total generated files")
    return seconds


def corpus(name, project, binary, bsc, runtime, tool, work, external=False):
    project = project.resolve()
    reports = work / "reports"
    reports.mkdir()
    outputs = {}
    build_seconds = {}
    for label in ("reference", "candidate"):
        env = dict(os.environ, RESCRIPT_RUNTIME=str(runtime), RESCRIPT_FULL_BUILD="1",
                   RESCRIPT_JS_PRINTER="legacy" if label == "reference" else "oxc",
                   RESCRIPT_JS_PRINTER_SOURCE_MAPS="legacy")
        env.pop("RESCRIPT_JS_PRINTER_STATS", None)
        if label == "candidate":
            env["RESCRIPT_JS_PRINTER_STATS"] = str(reports)
        run([binary, "clean", project], env, work / f"{label}-clean.log")
        def build(folder, suffix):
            command = [binary, "build", folder] if label == "candidate" or external else [binary, "build-reference", "--bsc", bsc, folder]
            return run(command, env, work / f"{label}-{suffix}.log")
        if project != runtime.resolve():
            run([binary, "clean", runtime], env, work / f"{label}-runtime-clean.log")
            build(runtime, "runtime")
            if not external:
                build(ROOT / "packages/@rescript/belt", "belt")
        before = inventory(project)
        build_seconds[label] = build(project, "build")
        outputs[label] = capture(project, before, work / label, external or name.startswith("gentype-"))
    result = summarize(reports, [project / n for n in outputs["candidate"]], project)
    js_count = sum(Path(n).suffix in JS for n in outputs["candidate"])
    result_display = {**result, "generated_files": len(outputs["candidate"]), "javascript_files": js_count,
                      "build_seconds": build_seconds}
    print(f"PRINTER_COVERAGE {name} " + json.dumps(result_display, sort_keys=True))
    print(f"{name}: {result['emitted']} oxc; {sum(result['unsupported'].values())} fallbacks")
    for reason, count in result["unsupported"].items():
        print(f"{count}\t{reason}")
    coverage_path = work.parent / f"{name.replace('/', '-')}.json"
    coverage_path.write_text(json.dumps(result_display, indent=2) + "\n")
    comparison_start = time.monotonic()
    try:
        compare(work / "reference", work / "candidate", tool, work, env)
        result_display["equal"] = True
    except RuntimeError:
        result_display["equal"] = False
        raise
    finally:
        result_display["reformat_seconds"] = time.monotonic() - comparison_start
        print(f"Comparison elapsed: {result_display['reformat_seconds']:.3f}s", flush=True)
        coverage_path.write_text(json.dumps(result_display, indent=2) + "\n")
        if (work / "reformat.log").exists():
            shutil.copy2(work / "reformat.log", work.parent / f"{name.replace('/', '-')}-reformat.log")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=["javascript", "stdlib", "gentype", "external"], required=True)
    parser.add_argument("--target", choices=["debug", "release"], default="debug")
    parser.add_argument("--project", type=Path, help="external corpus, never recorded in the baseline")
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    if args.suite == "external" and (not args.project or args.record):
        parser.error("external requires --project and does not support --record")
    binary = Path(os.environ.get("REWATCH_BIN", ROOT / f"rewatch/target/{args.target}/rescript")).resolve()
    bsc = Path(os.environ.get("OCAML_BSC", ROOT / "_build/install/default/bin/bsc")).resolve()
    runtime = ROOT / "packages/@rescript/runtime"
    tool = Path(os.environ.get("PARITY_REFORMAT_BIN", ROOT / "scripts/js-reformat/target/debug/js-reformat")).resolve()
    cache = ROOT / ".parity-cache/printer"
    cache.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    env = dict(os.environ, RESCRIPT_JS_PRINTER="oxc", RESCRIPT_JS_PRINTER_SOURCE_MAPS="legacy",
               PARITY_COMPARE_MODE="reformat", PARITY_JS_PRINTER="oxc", PARITY_PRINTER_INNER="1", RESCRIPT_FULL_BUILD="1",
               RESCRIPT_CLI=str(binary), REWATCH_BIN=str(binary), RUST_TARGET=args.target,
               REWATCH_TARGET=args.target, RESCRIPT_RUNTIME=str(runtime), OCAML_BSC=str(bsc),
               RUST_BSC=os.environ.get("RUST_BSC", str(ROOT / f"rewatch/target/{args.target}/bsc")))
    env.pop("RESCRIPT_JS_PRINTER_STATS", None)
    run([ROOT / "scripts/rust_compiler_shims.sh", args.target], env, cache / "shims.log")
    if "PARITY_REFORMAT_BIN" not in os.environ:
        run(["cargo", "build", "--locked", "--manifest-path", ROOT / "scripts/js-reformat/Cargo.toml",
             "--target-dir", tool.parent.parent], env, cache / "reformat-build.log")
    env["PARITY_REFORMAT_BIN"] = str(tool)
    corpora = {"javascript": [("tests/tests", ROOT / "tests/tests")],
               "stdlib": [("runtime", runtime)],
               "gentype": [("gentype-example", ROOT / "tests/gentype_tests/typescript-react-example"),
                            ("gentype-stdlib", ROOT / "tests/gentype_tests/stdlib-no-shims")],
               "external": [("external", args.project)]}[args.suite]
    actual = {}
    for name, project in corpora:
        project = project.resolve()
        # Fresh report directories are essential: warm/stale evidence must not
        # let a legacy build satisfy the zero-oxc or coverage gates.
        with tempfile.TemporaryDirectory(prefix=name.replace("/", "-") + "-", dir=cache) as temp:
            work = Path(temp)
            with restore_tracked(project, work):
                if args.suite == "external":
                    with tempfile.TemporaryDirectory(prefix=".printer-packages-", dir=project.parent) as packages:
                        external_runtime = bench_project.prepare(project, ROOT, Path(packages))
                        actual[name] = corpus(name, project, binary, bsc, external_runtime, tool, work, True)
                else:
                    actual[name] = corpus(name, project, binary, bsc, runtime, tool, work)
    if args.suite == "javascript":
        run([ROOT / "scripts/test_js_output_parity_fixtures.sh"], env, cache / "fixtures.log")
        print("Focused JavaScript fixture suite: passed (reformat comparison)")
    if args.suite == "gentype":
        # Retain the original suite's exact .gen.ts/.gen.tsx checks and matching
        # typecheck outcomes. The batch runs above additionally compare JS.
        projects = [p for _, p in corpora]
        with tempfile.TemporaryDirectory(prefix="gentype-preserve-", dir=cache) as temp:
            from contextlib import ExitStack
            with ExitStack() as stack:
                for i, project in enumerate(projects):
                    stack.enter_context(restore_tracked(project, Path(temp) / str(i)))
                run([ROOT / "scripts/test_gentype_output_parity.sh"], env, cache / "gentype.log")
        print("Original genType byte comparisons and typechecks: passed")
    if args.suite != "external":
        baseline = json.loads(RATCHET.read_text()) if RATCHET.exists() else {}
        if args.record:
            baseline.update(actual)
            RATCHET.write_text(json.dumps(baseline, indent=2, sort_keys=True) + "\n")
            print("Recorded printer coverage baseline")
        else:
            check(actual, baseline)
            print("Printer coverage ratchet: passed")
    print("Suite printer coverage (unique corpus outputs):")
    for name, row in actual.items():
        print(f"{name}: {row['emitted']} emitted / {row['outputs']} outputs")
        for reason, count in row["unsupported"].items():
            print(f"  {count}  {reason}")
    print(f"Printer parity suite ({args.suite}, oxc): {time.monotonic() - start:.3f}s")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        print(f"printer parity: {error}", file=sys.stderr)
        sys.exit(1)
