#!/usr/bin/env python3
"""
Repeated parser throughput benchmark (single-thread by default).

This wraps the existing Rust benchmark test:
  parser::benchmark::tests::benchmark_cold

It runs warmups, then measured iterations, and reports:
  - per-run elapsed ms
  - per-run KLOC/s
  - min / median / p95 / max KLOC/s
"""

from __future__ import annotations

import argparse
import math
import os
import re
import statistics
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


CORPUS_RE = re.compile(
    r"(?m)^(\d+)\s+files,\s+(\d+)\s+lines,\s+([0-9]+(?:\.[0-9]+)?)\s+KB\s*$"
)
ELAPSED_RE = re.compile(r"(?m)^\s*(\d+)\s+files parsed in\s+([0-9]+(?:\.[0-9]+)?)\s+ms\s*$")


@dataclass(frozen=True)
class RunResult:
    files: int
    lines: int
    kb: float
    elapsed_ms: float
    kloc_per_s: float
    mb_per_s: float


def percentile_nearest_rank(values: list[float], pct: float) -> float:
    if not values:
        raise ValueError("percentile on empty list")
    sorted_values = sorted(values)
    rank = max(1, math.ceil((pct / 100.0) * len(sorted_values)))
    return sorted_values[rank - 1]


def run_once(cmd: list[str], env: dict[str, str]) -> RunResult:
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        check=False,
    )
    if proc.returncode != 0:
        sys.stderr.write("Benchmark command failed.\n")
        sys.stderr.write(f"Command: {' '.join(cmd)}\n")
        if proc.stdout.strip():
            sys.stderr.write("\n--- stdout ---\n")
            sys.stderr.write(proc.stdout)
            sys.stderr.write("\n")
        if proc.stderr.strip():
            sys.stderr.write("\n--- stderr ---\n")
            sys.stderr.write(proc.stderr)
            sys.stderr.write("\n")
        raise RuntimeError("benchmark command failed")

    corpus_match = CORPUS_RE.search(proc.stdout)
    elapsed_match = ELAPSED_RE.search(proc.stdout)
    if not corpus_match or not elapsed_match:
        sys.stderr.write("Could not parse benchmark output.\n")
        sys.stderr.write("\n--- stdout ---\n")
        sys.stderr.write(proc.stdout)
        sys.stderr.write("\n")
        if proc.stderr.strip():
            sys.stderr.write("\n--- stderr ---\n")
            sys.stderr.write(proc.stderr)
            sys.stderr.write("\n")
        raise RuntimeError("failed to parse benchmark output")

    files = int(corpus_match.group(1))
    lines = int(corpus_match.group(2))
    kb = float(corpus_match.group(3))
    parsed_files = int(elapsed_match.group(1))
    elapsed_ms = float(elapsed_match.group(2))

    if parsed_files != files:
        raise RuntimeError(f"parsed files mismatch: header={files}, parsed={parsed_files}")
    if elapsed_ms <= 0:
        raise RuntimeError(f"invalid elapsed time: {elapsed_ms}ms")

    elapsed_s = elapsed_ms / 1000.0
    kloc_per_s = lines / elapsed_s / 1000.0
    mb_per_s = (kb * 1024.0) / elapsed_s / 1_000_000.0

    return RunResult(
        files=files,
        lines=lines,
        kb=kb,
        elapsed_ms=elapsed_ms,
        kloc_per_s=kloc_per_s,
        mb_per_s=mb_per_s,
    )


def parse_args() -> argparse.Namespace:
    root = Path(__file__).resolve().parents[1]
    default_manifest = root / "compiler-rust" / "Cargo.toml"

    parser = argparse.ArgumentParser(
        description="Repeat parser cold benchmark and summarize KLOC/s statistics."
    )
    parser.add_argument(
        "--runs",
        type=int,
        default=10,
        help="Measured runs (default: 10)",
    )
    parser.add_argument(
        "--warmup",
        type=int,
        default=2,
        help="Warmup runs before measurement (default: 2)",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=1,
        help="RAYON_NUM_THREADS for benchmark command (default: 1)",
    )
    parser.add_argument(
        "--manifest-path",
        default=str(default_manifest),
        help="Path to compiler-rust Cargo.toml",
    )
    parser.add_argument(
        "--test-name",
        default="benchmark_cold",
        help="Ignored benchmark test filter (default: benchmark_cold)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.runs <= 0:
        raise ValueError("--runs must be > 0")
    if args.warmup < 0:
        raise ValueError("--warmup must be >= 0")
    if args.threads <= 0:
        raise ValueError("--threads must be > 0")

    cmd = [
        "cargo",
        "test",
        "--manifest-path",
        args.manifest_path,
        "--release",
        "--lib",
        "--",
        args.test_name,
        "--ignored",
        "--nocapture",
    ]

    env = os.environ.copy()
    env["RAYON_NUM_THREADS"] = str(args.threads)
    env.setdefault("CARGO_TERM_COLOR", "never")

    print("Parser throughput benchmark")
    print("===========================")
    print(f"Command: {' '.join(cmd)}")
    print(f"RAYON_NUM_THREADS={env['RAYON_NUM_THREADS']}")
    print(f"Warmup runs: {args.warmup}")
    print(f"Measured runs: {args.runs}")
    print("")

    for i in range(args.warmup):
        run_once(cmd, env)
        print(f"Warmup {i + 1}/{args.warmup}: done")

    if args.warmup > 0:
        print("")

    results: list[RunResult] = []
    for i in range(args.runs):
        result = run_once(cmd, env)
        results.append(result)
        print(
            f"Run {i + 1:>2}/{args.runs}: "
            f"{result.elapsed_ms:>7.1f} ms  "
            f"{result.kloc_per_s:>8.1f} KLOC/s  "
            f"{result.mb_per_s:>6.2f} MB/s"
        )

    first = results[0]
    if any(
        r.files != first.files or r.lines != first.lines or abs(r.kb - first.kb) > 0.0001
        for r in results[1:]
    ):
        raise RuntimeError("corpus changed across runs; benchmark is not comparable")

    kloc_values = [r.kloc_per_s for r in results]
    ms_values = [r.elapsed_ms for r in results]
    mb_values = [r.mb_per_s for r in results]

    min_kloc = min(kloc_values)
    max_kloc = max(kloc_values)
    median_kloc = statistics.median(kloc_values)
    p95_kloc = percentile_nearest_rank(kloc_values, 95.0)

    min_ms = min(ms_values)
    max_ms = max(ms_values)
    median_ms = statistics.median(ms_values)
    p95_ms = percentile_nearest_rank(ms_values, 95.0)

    print("")
    print("Summary")
    print("=======")
    print(f"Corpus: {first.files} files, {first.lines} LOC, {first.kb:.1f} KB")
    print(
        "KLOC/s: "
        f"min {min_kloc:.1f}  median {median_kloc:.1f}  "
        f"p95 {p95_kloc:.1f}  max {max_kloc:.1f}"
    )
    print(
        "ms:     "
        f"min {min_ms:.1f}  median {median_ms:.1f}  "
        f"p95 {p95_ms:.1f}  max {max_ms:.1f}"
    )
    print(f"MB/s:   min {min(mb_values):.2f}  median {statistics.median(mb_values):.2f}")
    print("")
    print(
        "Best-case throughput (max KLOC/s / min ms): "
        f"{max_kloc:.1f} KLOC/s @ {min_ms:.1f} ms"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
