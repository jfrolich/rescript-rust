#!/usr/bin/env python3
"""Summarize RESCRIPT_DERIVED_CENSUS JSONL; estimates remain visibly labelled."""
import argparse
import json
import sys

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
        if row["checker_counters"] is not None:
            result["counter_modules"] += 1
            for side in range(2):
                for counter in range(4):
                    result["checker_counters"][side][counter] += row["checker_counters"][side][counter]
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
