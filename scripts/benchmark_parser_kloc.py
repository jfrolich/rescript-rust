#!/usr/bin/env python3
"""
Repeated in-process parser throughput benchmark (single-thread by default).

This wraps parser::benchmark::tests::benchmark_cold_repeat, which runs all
iterations inside a single benchmark process (no repeated subprocess parser runs).
"""

from __future__ import annotations

import argparse
import os
import subprocess
from pathlib import Path


def parse_args() -> argparse.Namespace:
    root = Path(__file__).resolve().parents[1]
    default_manifest = root / "compiler-rust" / "Cargo.toml"

    parser = argparse.ArgumentParser(
        description="Run repeated in-process parser throughput benchmark."
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
        default="benchmark_cold_repeat",
        help="Ignored benchmark test filter (default: benchmark_cold_repeat)",
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
    env["PARSER_BENCH_WARMUP"] = str(args.warmup)
    env["PARSER_BENCH_RUNS"] = str(args.runs)
    env.setdefault("CARGO_TERM_COLOR", "never")

    print("In-process parser throughput benchmark", flush=True)
    print("======================================", flush=True)
    print(f"Command: {' '.join(cmd)}", flush=True)
    print(f"RAYON_NUM_THREADS={env['RAYON_NUM_THREADS']}", flush=True)
    print(f"PARSER_BENCH_WARMUP={env['PARSER_BENCH_WARMUP']}", flush=True)
    print(f"PARSER_BENCH_RUNS={env['PARSER_BENCH_RUNS']}", flush=True)
    print("", flush=True)

    proc = subprocess.run(cmd, env=env, check=False)
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
