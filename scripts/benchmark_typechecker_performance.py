#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


@dataclass
class FileResult:
    file: str
    status: str
    ocaml_ms: float | None
    rust_ms: float | None
    ratio: float | None
    delta_ms: float | None
    ocaml_error: str | None
    rust_error: str | None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Benchmark parser-free OCaml vs Rust compilation on the canonical "
            "recursive tests/tests/src corpus using checked-in .ast files."
        )
    )
    parser.add_argument(
        "selector",
        nargs="?",
        help=(
            "Optional source file path or regex pattern. Defaults to all "
            "tests/tests/src/**/*.res files in the canonical 657-file corpus."
        ),
    )
    parser.add_argument("--warmup", type=int, default=1, help="Warmup runs per compiler")
    parser.add_argument("--runs", type=int, default=1, help="Measured runs per compiler")
    parser.add_argument(
        "--timeout",
        type=int,
        default=20,
        help="Per-compile timeout in seconds",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=20,
        help="How many slower files to print in the summary",
    )
    parser.add_argument(
        "--material-ratio",
        type=float,
        default=1.10,
        help="Ratio threshold for 'materially slower' classification",
    )
    parser.add_argument(
        "--material-delta-ms",
        type=float,
        default=5.0,
        help="Absolute delta threshold for 'materially slower' classification",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help=(
            "Directory for latest CSV/JSON output. Defaults to "
            ".performance-cache/typechecker"
        ),
    )
    parser.add_argument(
        "--typedtree-only",
        action="store_true",
        help=(
            "Benchmark through typedtree serialization and skip Lambda/JS lowering. "
            "Uses RESCRIPT_TYPEDTREE_ONLY for OCaml and RUST_TYPEDTREE_ONLY for Rust."
        ),
    )
    return parser.parse_args()


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def default_paths(root: Path) -> dict[str, Path]:
    platform = subprocess.check_output(
        [str(root / "scripts" / "platform.sh")],
        text=True,
    ).strip()
    return {
        "project_root": root,
        "test_project": root / "tests" / "tests",
        "workdir": root / "tests" / "tests" / "lib" / "bs",
        "rescript_cli": root / "packages" / "@rescript" / platform / "bin" / "rescript.exe",
        "ocaml_bsc": root / "_build" / "install" / "default" / "bin" / "bsc",
        "rust_bsc": root / "compiler-rust" / "target" / "release" / "bsc",
        "output_dir": root / ".performance-cache" / "typechecker",
    }


def ensure_exists(path: Path, description: str) -> None:
    if not path.exists():
        raise SystemExit(f"{description} not found: {path}")


def source_files(test_project: Path, selector: str | None) -> list[Path]:
    files = sorted((test_project / "src").rglob("*.res"))
    if selector is None:
        return files

    selector_path = Path(selector)
    if selector_path.is_absolute() and selector_path.exists():
        return [selector_path]

    candidate = Path.cwd() / selector
    if candidate.exists():
        return [candidate.resolve()]

    candidate = test_project / selector
    if candidate.exists():
        return [candidate.resolve()]

    pattern = re.compile(selector)
    matched = [path for path in files if pattern.search(path.as_posix())]
    if not matched:
        raise SystemExit(f"No files matched selector: {selector}")
    return matched


def compiler_args_for_file(
    rescript_cli: Path,
    test_project: Path,
    source_file: Path,
) -> list[str]:
    rel_path = source_file.resolve().relative_to(test_project.resolve()).as_posix()
    proc = subprocess.run(
        [str(rescript_cli), "compiler-args", rel_path],
        cwd=test_project,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "compiler-args failed")
    data = json.loads(proc.stdout)
    args = data.get("compiler_args")
    if not isinstance(args, list) or not args:
        raise RuntimeError("compiler-args returned no compiler_args")
    return [str(arg) for arg in args]


def summarize_error(stderr: bytes | str) -> str:
    text = stderr.decode("utf-8", errors="replace") if isinstance(stderr, bytes) else stderr
    text = text.strip()
    if not text:
        return "no stderr output"
    return text.splitlines()[0][:300]


def measure_compiler(
    compiler: Path,
    base_args: list[str],
    workdir: Path,
    output_file: Path,
    warmup: int,
    runs: int,
    timeout_seconds: int,
    env: dict[str, str] | None = None,
    discard_stderr: bool = False,
) -> tuple[float | None, str | None]:
    times: list[float] = []
    total_runs = warmup + runs
    for run_idx in range(total_runs):
        if output_file.exists():
            output_file.unlink()
        start = time.perf_counter()
        stderr_target = subprocess.DEVNULL if discard_stderr else subprocess.PIPE
        try:
            proc = subprocess.run(
                [str(compiler), *base_args, "-o", str(output_file)],
                cwd=workdir,
                stdout=subprocess.PIPE,
                stderr=stderr_target,
                env=env,
                timeout=timeout_seconds,
            )
        except subprocess.TimeoutExpired:
            return None, f"timeout after {timeout_seconds}s"
        elapsed_ms = (time.perf_counter() - start) * 1000.0
        if proc.returncode != 0:
            if discard_stderr:
                return None, "compiler failed; stderr discarded for typedtree-only timing"
            return None, summarize_error(proc.stderr)
        if run_idx >= warmup:
            times.append(elapsed_ms)

    if not times:
        return None, "no measured runs"
    return min(times), None


def safe_ratio(rust_ms: float | None, ocaml_ms: float | None) -> float | None:
    if rust_ms is None or ocaml_ms is None:
        return None
    if ocaml_ms <= 0:
        return None
    return rust_ms / ocaml_ms


def safe_delta(rust_ms: float | None, ocaml_ms: float | None) -> float | None:
    if rust_ms is None or ocaml_ms is None:
        return None
    return rust_ms - ocaml_ms


def slower_results(results: Iterable[FileResult]) -> list[FileResult]:
    slower = [
        result
        for result in results
        if result.status == "ok"
        and result.rust_ms is not None
        and result.ocaml_ms is not None
        and result.rust_ms > result.ocaml_ms
    ]
    return sorted(
        slower,
        key=lambda result: (
            result.delta_ms if result.delta_ms is not None else float("-inf"),
            result.ratio if result.ratio is not None else float("-inf"),
        ),
        reverse=True,
    )


def write_outputs(
    output_dir: Path,
    args: argparse.Namespace,
    results: list[FileResult],
) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "latest.csv"
    json_path = output_dir / "latest.json"

    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "file",
                "status",
                "ocaml_ms",
                "rust_ms",
                "ratio",
                "delta_ms",
                "ocaml_error",
                "rust_error",
            ],
        )
        writer.writeheader()
        for result in results:
            writer.writerow(asdict(result))

    payload = {
        "generated_at_epoch_s": time.time(),
        "warmup": args.warmup,
        "runs": args.runs,
        "timeout_seconds": args.timeout,
        "selector": args.selector,
        "material_ratio": args.material_ratio,
        "material_delta_ms": args.material_delta_ms,
        "typedtree_only": args.typedtree_only,
        "results": [asdict(result) for result in results],
    }
    json_path.write_text(json.dumps(payload, indent=2) + "\n")
    return csv_path, json_path


def print_summary(args: argparse.Namespace, results: list[FileResult]) -> None:
    total = len(results)
    comparable = [result for result in results if result.status == "ok"]
    slower = slower_results(results)
    material = [
        result
        for result in slower
        if result.ratio is not None
        and result.delta_ms is not None
        and result.ratio >= args.material_ratio
        and result.delta_ms >= args.material_delta_ms
    ]
    rust_faster_or_equal = len(comparable) - len(slower)
    rust_failures = [result for result in results if result.status.startswith("rust_")]
    ocaml_failures = [result for result in results if result.status.startswith("ocaml_")]
    args_failures = [result for result in results if result.status == "compiler_args_fail"]

    title = "Typedtree-Only Performance Benchmark" if args.typedtree_only else "Typechecker Performance Benchmark"
    print(title)
    print("=" * len(title))
    print(f"Files tested:              {total}")
    print(f"Comparable files:         {len(comparable)}")
    print(f"Rust faster or equal:     {rust_faster_or_equal}")
    print(f"Rust slower:              {len(slower)}")
    print(f"Materially slower:        {len(material)}")
    print(f"OCaml failures:           {len(ocaml_failures)}")
    print(f"Rust failures:            {len(rust_failures)}")
    print(f"compiler-args failures:   {len(args_failures)}")
    print("")

    if comparable:
        total_ocaml = sum(result.ocaml_ms for result in comparable if result.ocaml_ms is not None)
        total_rust = sum(result.rust_ms for result in comparable if result.rust_ms is not None)
        ratio = total_rust / total_ocaml if total_ocaml > 0 else math.nan
        print("Aggregate Timing")
        print("----------------")
        print(f"OCaml total:              {total_ocaml:.1f}ms")
        print(f"Rust total:               {total_rust:.1f}ms")
        print(f"Rust / OCaml ratio:       {ratio:.2f}x")
        print("")

    if slower:
        print(f"Top {min(args.limit, len(slower))} Slower-Than-OCaml Files")
        print("--------------------------------")
        for result in slower[: args.limit]:
            assert result.ocaml_ms is not None
            assert result.rust_ms is not None
            assert result.ratio is not None
            assert result.delta_ms is not None
            print(
                f"{result.ratio:6.2f}x  +{result.delta_ms:8.1f}ms  "
                f"OCaml {result.ocaml_ms:8.1f}ms  Rust {result.rust_ms:8.1f}ms  "
                f"{result.file}"
            )
        print("")

    if rust_failures:
        print("Rust Failures")
        print("-------------")
        for result in rust_failures[: args.limit]:
            print(f"{result.file}: {result.rust_error}")
        print("")

    if ocaml_failures:
        print("OCaml Failures")
        print("--------------")
        for result in ocaml_failures[: args.limit]:
            print(f"{result.file}: {result.ocaml_error}")
        print("")

    if args_failures:
        print("compiler-args Failures")
        print("----------------------")
        for result in args_failures[: args.limit]:
            print(f"{result.file}: {result.ocaml_error}")
        print("")


def main() -> int:
    args = parse_args()
    root = repo_root()
    paths = default_paths(root)
    if args.output_dir is None:
        args.output_dir = paths["output_dir"]

    ensure_exists(paths["test_project"], "test project")
    ensure_exists(paths["workdir"], "benchmark workdir")
    ensure_exists(paths["rescript_cli"], "rescript CLI")
    ensure_exists(paths["ocaml_bsc"], "OCaml bsc")
    ensure_exists(paths["rust_bsc"], "Rust bsc")

    files = source_files(paths["test_project"], args.selector)

    with tempfile.TemporaryDirectory(prefix="typechecker-perf-") as tmp_dir:
        tmp_root = Path(tmp_dir)
        results: list[FileResult] = []

        for index, source_file in enumerate(files, start=1):
            rel_path = source_file.resolve().relative_to(paths["test_project"].resolve()).as_posix()
            print(f"[{index}/{len(files)}] {rel_path}", file=sys.stderr)

            try:
                compiler_args = compiler_args_for_file(
                    paths["rescript_cli"], paths["test_project"], source_file
                )
            except Exception as exc:  # noqa: BLE001
                results.append(
                    FileResult(
                        file=rel_path,
                        status="compiler_args_fail",
                        ocaml_ms=None,
                        rust_ms=None,
                        ratio=None,
                        delta_ms=None,
                        ocaml_error=str(exc),
                        rust_error=None,
                    )
                )
                continue

            compiler_base_args = compiler_args
            ocaml_env = None
            rust_env = None
            discard_stderr = False
            if args.typedtree_only:
                compiler_base_args = [*compiler_args, "-dtyped-sexp"]
                ocaml_env = os.environ.copy()
                ocaml_env["RESCRIPT_TYPEDTREE_ONLY"] = "1"
                rust_env = os.environ.copy()
                rust_env["RUST_TYPEDTREE_ONLY"] = "1"
                discard_stderr = True

            rel_output = Path(rel_path)
            ocaml_out = (tmp_root / rel_output).with_suffix(".ocaml.mjs")
            rust_out = (tmp_root / rel_output).with_suffix(".rust.mjs")
            ocaml_out.parent.mkdir(parents=True, exist_ok=True)
            rust_out.parent.mkdir(parents=True, exist_ok=True)

            ocaml_ms, ocaml_error = measure_compiler(
                paths["ocaml_bsc"],
                compiler_base_args,
                paths["workdir"],
                ocaml_out,
                args.warmup,
                args.runs,
                args.timeout,
                env=ocaml_env,
                discard_stderr=discard_stderr,
            )
            rust_ms, rust_error = measure_compiler(
                paths["rust_bsc"],
                compiler_base_args,
                paths["workdir"],
                rust_out,
                args.warmup,
                args.runs,
                args.timeout,
                env=rust_env,
                discard_stderr=discard_stderr,
            )

            if ocaml_ms is not None and rust_ms is not None:
                status = "ok"
            elif ocaml_ms is None and rust_ms is None:
                status = "both_fail"
            elif ocaml_ms is None:
                status = "ocaml_fail"
            else:
                status = "rust_fail"

            results.append(
                FileResult(
                    file=rel_path,
                    status=status,
                    ocaml_ms=ocaml_ms,
                    rust_ms=rust_ms,
                    ratio=safe_ratio(rust_ms, ocaml_ms),
                    delta_ms=safe_delta(rust_ms, ocaml_ms),
                    ocaml_error=ocaml_error,
                    rust_error=rust_error,
                )
            )

    csv_path, json_path = write_outputs(args.output_dir, args, results)
    print_summary(args, results)
    print(f"CSV:  {csv_path}")
    print(f"JSON: {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
