#!/usr/bin/env python3
"""Summarize local Cachegrind named self instructions for three printer modes.

Use the same release binary for all three clean builds, from the project's own
working directory (build .), with RAYON_NUM_THREADS=1 and RESCRIPT_FULL_BUILD=1.
Prepare runtime artifacts outside measurement; unset printer/backend stats.
Run Cachegrind with --cache-sim=no --branch-sim=no. Pass the three resulting
profiles in legacy, oxc, oxc-bir order. Failed builds are not measurements.

Buckets are self attribution, not inclusive call-graph attribution. Shared
allocation/container work is not charged exclusively to import or emission.
Inlining can move work into the caller's bucket. Output contains aggregate
counts only, never source paths or function names.
"""
import argparse
import collections
import json
from pathlib import Path
import re
import subprocess


def category(symbol):
    if "PrinterStats" in symbol or "getenv" in symbol:
        return "Stats and environment"
    if "emit::naming" in symbol or "emit::bir_naming" in symbol:
        return "Naming"
    if "emit::build" in symbol or "oxc_allocator::" in symbol:
        return "AST construction / oxc arena"
    if "oxc_codegen::" in symbol:
        return "Oxc codegen"
    if "oxc_parser::" in symbol:
        return "Oxc parser"
    if "rescript_compiler::emit::" in symbol or "bir::emit_view" in symbol:
        return "Other emitter"
    if "rescript_compiler::bir::" in symbol:
        return "J import (named self)"
    if "js_ir::printer::" in symbol or "js_ir::program_printer::" in symbol:
        return "Legacy printer"
    if any(part in symbol for part in (
        "alloc::", "hashbrown::", "im_rc::", "bitmaps::", "_mi_", "mi_",
        "malloc", "calloc", "realloc", "memcpy", "memmove", "memset",
        "memcmp", "__rust_alloc", "__rust_dealloc",
    )):
        return "Shared allocation / containers"
    if symbol == "???":
        return "Unresolved"
    return "Other compiler/runtime"


def parse_annotation(text, total):
    counts = collections.Counter()
    for line in text.splitlines():
        row = re.match(r"^\s*([\d,]+)\s+(.+)$", line)
        if not row or row[2] == "PROGRAM TOTALS":
            continue
        # cg_annotate writes file:function; the function can contain Rust ::.
        if ":" not in row[2]:
            continue
        symbol = row[2].split(":", 1)[1]
        counts[category(symbol)] += int(row[1].replace(",", ""))
    if sum(counts.values()) != total:
        raise ValueError(f"function attribution sums to {sum(counts.values())}, expected {total}")
    return {"total": total, "self_instructions": dict(sorted(counts.items()))}


def summarize(profile):
    match = None
    with profile.open() as lines:
        for line in lines:
            if line.startswith("summary:"):
                match = re.fullmatch(r"summary:\s+(\d+)\s*", line)
    if not match or not int(match[1]):
        raise ValueError("expected a nonzero, instruction-only Cachegrind summary")
    annotated = subprocess.check_output([
        "cg_annotate", "--auto=no", "--threshold=0", "--show=Ir",
        "--show-percs=no", "--sort=Ir", str(profile),
    ], text=True)
    return parse_annotation(annotated, int(match[1]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("legacy", type=Path)
    parser.add_argument("oxc", type=Path)
    parser.add_argument("oxc_bir", type=Path)
    args = parser.parse_args()
    result = {mode: summarize(path) for mode, path in (
        ("legacy", args.legacy), ("oxc", args.oxc), ("oxc-bir", args.oxc_bir),
    )}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
