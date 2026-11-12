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
        return "Bir support / import (named self)"
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


def parse_profile(lines):
    """Read self costs directly; cg_annotate's report layout varies by version."""
    counts = collections.Counter()
    bucket = None
    total = None
    for line in lines:
        line = line.strip()
        if line.startswith("events:"):
            if line != "events: Ir":
                raise ValueError("expected an instruction-only Cachegrind profile")
        elif line.startswith("fn="):
            bucket = category(line[3:])
        elif line.startswith("summary:"):
            total = int(line.split()[1])
        elif row := re.fullmatch(r"\d+\s+(\d+)", line):
            if bucket is None:
                raise ValueError("instruction row without a function")
            counts[bucket] += int(row[1])
    if not total:
        raise ValueError("expected a nonzero Cachegrind summary")
    if sum(counts.values()) != total:
        raise ValueError(f"function attribution sums to {sum(counts.values())}, expected {total}")
    return {"total": total, "self_instructions": dict(sorted(counts.items()))}


def summarize(profile):
    with profile.open() as lines:
        return parse_profile(lines)


def callgrind_phases(lines):
    """Sum incoming physical call edges, excluding same-name inline file splits."""
    names = {}
    edges = collections.Counter()
    caller = callee = None
    call_cost = False
    total = None
    self_total = 0
    for raw in lines:
        line = raw.strip()
        if line.startswith("events:") and line != "events: Ir":
            raise ValueError("expected instruction-only Callgrind events")
        if line.startswith("summary:"):
            total = int(line.split()[1])
        elif match := re.fullmatch(r"(c?fn)=\((\d+)\)(?: (.*))?", line):
            ident = int(match[2])
            if match[3] is not None:
                names[ident] = match[3]
            if match[1] == "fn":
                caller = ident
            else:
                callee = ident
        elif line.startswith("calls="):
            call_cost = True
        elif match := re.fullmatch(r"(?:\d+|[+-]\d+|\*)\s+(\d+)", line):
            cost = int(match[1])
            if call_cost:
                edges[caller, callee] += cost
                call_cost = False
            else:
                self_total += cost
    if not total or total != self_total:
        raise ValueError(f"Callgrind self costs sum to {self_total}, expected {total}")
    targets = {
        "rescript_compiler::driver::render_js_program": "render",
        "rescript_compiler::bir::bridge_j::import_js": "import",
        "rescript_compiler::emit::emit_bir": "emit_bir",
        "rescript_compiler::emit::program::emit": "emit_oxc",
    }
    phases = dict.fromkeys(targets.values(), 0)
    for (caller, callee), cost in edges.items():
        source, target = names[caller], names[callee]
        if source != target and target in targets:
            phases[targets[target]] += cost
    return {"total": total, "inclusive_instructions": phases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--callgrind", action="store_true", help="report inclusive call-edge phase costs")
    parser.add_argument("legacy", type=Path)
    parser.add_argument("oxc", type=Path)
    parser.add_argument("oxc_bir", type=Path)
    args = parser.parse_args()
    def report(path):
        if args.callgrind:
            with path.open() as lines:
                return callgrind_phases(lines)
        return summarize(path)
    result = {mode: report(path) for mode, path in (
        ("legacy", args.legacy), ("oxc", args.oxc), ("oxc-bir", args.oxc_bir),
    )}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
