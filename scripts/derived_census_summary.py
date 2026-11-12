#!/usr/bin/env python3
"""Summarize RESCRIPT_DERIVED_CENSUS JSONL; estimates remain visibly labelled."""
import argparse
import json
import sys
import collections
import math

PHASES = (
    "parse_other", "generation", "frontend", "environment", "typecheck",
    "signature", "conversion", "lambda_lowering", "lambda_passes", "lowering",
    "printing", "gentype",
)


def summarize(rows):
    result = {key: {"derived": 0, "other": 0, "estimated": False}
              for key in (*PHASES, "js_bytes", "js_lines")}
    result.update(modules=0, bindings=[0, 0], syntax_nodes=[0, 0],
                  checker_counters=[[0] * 4, [0] * 4], counter_modules=0)
    shapes = collections.defaultdict(list)
    templates = []
    for row in rows:
        if row.get("version") != 1:
            raise ValueError(f"Unsupported census version: {row.get('version')!r}")
        result["modules"] += 1
        for key in (*PHASES, "js_bytes", "js_lines"):
            for side in ("derived", "other"):
                value = row[key][side]
                if not isinstance(value, int) or value < 0:
                    raise ValueError(f"Invalid {key}.{side}: {value!r}")
                result[key][side] += value
            result[key]["estimated"] |= row[key]["estimated"]
        for key in ("bindings", "syntax_nodes"):
            for side in range(2):
                result[key][side] += row[key][side]
        classes = row.get("shape_classes", [])
        sizes = row.get("shape_nodes", [])
        parameterised = row.get("shape_parameterised", [])
        recursive = row.get("shape_recursive", [])
        keys = row.get("templates", [])
        if len({len(classes), len(sizes), len(parameterised), len(recursive), len(keys)}) != 1:
            raise ValueError("Mismatched per-binding shape columns")
        for shape, size, parameter, rec in zip(classes, sizes, parameterised, recursive):
            shapes[shape].append(size)
            if parameter:
                shapes["parameterised (overlap)"].append(size)
            if rec:
                shapes["recursive group (overlap)"].append(size)
        templates.extend(None if key is None else bytes(key) for key in keys)
        if row["checker_counters"] is not None:
            result["counter_modules"] += 1
            for side in range(2):
                for counter in range(4):
                    result["checker_counters"][side][counter] += row["checker_counters"][side][counter]
    result["shapes"] = {}
    for shape, sizes in sorted(shapes.items()):
        sizes.sort()
        quantile = lambda p: sizes[max(0, math.ceil(len(sizes) * p) - 1)]
        result["shapes"][shape] = dict(count=len(sizes), min=sizes[0], p50=quantile(.5),
                                       p90=quantile(.9), p99=quantile(.99), max=sizes[-1])
    result["template_bindings"] = len(templates)
    result["unsupported_templates"] = templates.count(None)
    # Compare complete structural byte strings, not a lossy hash fingerprint.
    result["distinct_templates"] = None if None in templates else len(set(templates))
    result["duplicate_bindings"] = (None if None in templates else len(templates) - len(set(templates)))
    return result


def markdown(summary):
    lines = [f"Modules/interfaces: {summary['modules']}", "",
             "| Phase | Derived ms | Other ms | Attribution |",
             "|---|---:|---:|---|"]
    for phase in PHASES:
        pair = summary[phase]
        label = "node-weighted estimate" if pair["estimated"] else "measured"
        lines.append(f"| {phase} | {pair['derived'] / 1e6:.3f} | {pair['other'] / 1e6:.3f} | {label} |")
    lines += ["", "| Size | Derived | Other |", "|---|---:|---:|"]
    for key in ("bindings", "syntax_nodes"):
        lines.append(f"| {key} | {summary[key][0]} | {summary[key][1]} |")
    for key in ("js_bytes", "js_lines"):
        lines.append(f"| {key} (estimated split) | {summary[key]['derived']} | {summary[key]['other']} |")
    lines += ["", f"Counter availability: {summary['counter_modules']}/{summary['modules']} records."]
    if summary["counter_modules"]:
        lines += ["", "| Checker counter | Derived | Other |", "|---|---:|---:|"]
        for i, name in enumerate(("Fresh variables", "Top-level unifications", "Instance copied nodes", "Lazy environment lookups")):
            lines.append(f"| {name} | {summary['checker_counters'][0][i]} | {summary['checker_counters'][1][i]} |")
    if summary["shapes"]:
        lines += ["", "| Shape | Bindings | Min nodes | P50 | P90 | P99 | Max |",
                  "|---|---:|---:|---:|---:|---:|---:|"]
        for shape, stats in summary["shapes"].items():
            lines.append("| " + shape + " | " + " | ".join(str(stats[k]) for k in ("count", "min", "p50", "p90", "p99", "max")) + " |")
        lines += ["", f"Distinct templates: {summary['distinct_templates']}; duplicate bindings: {summary['duplicate_bindings']}; unsupported templates: {summary['unsupported_templates']}."]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census")
    parser.add_argument("--module-contains", help="Filter source paths, e.g. tests/ppx_spice/")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable totals")
    args = parser.parse_args()
    try:
        with open(args.census, encoding="utf-8") as source:
            rows = (json.loads(line) for line in source if line.strip())
            if args.module_contains:
                rows = (row for row in rows if args.module_contains in row["module"])
            summary = summarize(rows)
        print(json.dumps(summary, indent=2) if args.json else markdown(summary))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"derived census: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
