#!/usr/bin/env python3
"""Summarize RESCRIPT_DERIVED_CENSUS JSONL; estimates remain visibly labelled."""
import argparse
import json
import sys
import collections
import math
from pathlib import Path

GENERAL_REASONS = ("custom_codec", "user_expression", "type_parameters", "recursive_group",
                   "shared_names", "unmeasured_shape", "unboxed", "not_yet_planned",
                   "unsupported_variant", "switch", "failed_obligation", "json_identity_argument")

UNPLANNED_FORMS = ("json_identity", "applied_user_codec", "applied_module_path",
                   "unsupported_type", "constant_fallback", "empty_record",
                   "template_literal", "declaration_shape")

PHASES = (
    "parse_other", "generation", "frontend", "environment", "typecheck",
    "signature", "conversion", "lambda_lowering", "lambda_passes", "lowering",
    "printing", "gentype",
)


def summarize(rows):
    result = {key: {"derived": 0, "other": 0, "estimated": False}
              for key in (*PHASES, "js_bytes", "js_lines")}
    result.update(modules=0, bindings=[0, 0], syntax_nodes=[0, 0],
                  checker_counters=[[0] * 4, [0] * 4], counter_modules=0, paths={}, path_timing_records=0,
                  planned_typecheck_ns=0, planned_conversion_ns=0, unplanned_forms={},
                  general_typecheck_ns=0, general_conversion_ns=0, general_costs={}, general_cost_records=0, failed_obligations={})
    shapes = collections.defaultdict(list)
    templates = []
    template_sizes = []
    for row in rows:
        if row.get("version") != 1:
            raise ValueError(f"Unsupported census version: {row.get('version')!r}")
        if row.get("event") == "failed_obligation":
            key = f"{row['obligation']} / {row['type_shape']}"
            result["failed_obligations"][key] = result["failed_obligations"].get(key, 0) + 1
            continue
        result["modules"] += 1
        for reason, count in row.get("paths", {}).items():
            if reason == "unplanned_forms":
                if len(count) != len(UNPLANNED_FORMS) or any(type(n) is not int or n < 0 for n in count):
                    raise ValueError("Invalid unplanned form counts")
                if sum(count) != row["paths"].get("not_yet_planned", 0):
                    raise ValueError("Unplanned form counts do not reconcile")
                for form, n in zip(UNPLANNED_FORMS, count):
                    result["unplanned_forms"][form] = result["unplanned_forms"].get(form, 0) + n
                continue
            if type(count) is not int or count < 0:
                raise ValueError(f"Invalid path count {reason}: {count!r}")
            result["paths"][reason] = result["paths"].get(reason, 0) + count
        if "general_syntax_nodes" in row or "general_typecheck_ns" in row:
            result["general_cost_records"] += 1
            for key in ("general_syntax_nodes", "general_typecheck_ns"):
                values = row[key]
                if len(values) not in (11, len(GENERAL_REASONS)) or any(type(n) is not int or n < 0 for n in values):
                    raise ValueError(f"Invalid {key}")
                for reason, n in zip(GENERAL_REASONS, values):
                    cost = result["general_costs"].setdefault(reason, {"general_syntax_nodes": 0, "general_typecheck_ns": 0})
                    cost[key] += n
        timing_keys = ("planned_typecheck_ns", "planned_conversion_ns")
        if any(key in row for key in timing_keys):
            result["path_timing_records"] += 1
            for phase, key in zip(("typecheck", "conversion"), timing_keys):
                planned = row[key]
                total = row[phase]["derived"]
                if type(planned) is not int or not 0 <= planned <= total:
                    raise ValueError(f"Invalid {key}: {planned!r}")
                result[key] += planned
                result[f"general_{phase}_ns"] += total - planned
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
        template_sizes.extend(sizes)
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
    supported = collections.Counter(key for key in templates if key is not None)
    unique_sizes = {}
    for key, size in zip(templates, template_sizes):
        if key is not None:
            if key in unique_sizes and unique_sizes[key] != size:
                raise ValueError("Identical template keys have different body sizes")
            unique_sizes[key] = size
    result["supported_templates"] = len(templates) - templates.count(None)
    result["distinct_templates"] = len(supported)
    result["duplicate_bindings"] = result["supported_templates"] - len(supported)
    result["singleton_templates"] = sum(count == 1 for count in supported.values())
    result["most_frequent_templates"] = sorted(supported.values(), reverse=True)[:6]
    result["template_body_nodes"] = sum(template_sizes)
    result["distinct_template_nodes"] = sum(unique_sizes.values())
    result["unsupported_template_nodes"] = sum(size for key, size in zip(templates, template_sizes) if key is None)
    result["distinct_template_node_share"] = (sum(unique_sizes.values()) / sum(template_sizes) if sum(template_sizes) else 0)
    return result


def markdown(summary):
    lines = [f"Modules/interfaces: {summary['modules']}", "",
             "| Phase | Derived ms | Other ms | Attribution |",
             "|---|---:|---:|---|"]
    for phase in PHASES:
        pair = summary[phase]
        label = "node-weighted estimate" if pair["estimated"] else "measured"
        lines.append(f"| {phase} | {pair['derived'] / 1e6:.3f} | {pair['other'] / 1e6:.3f} | {label} |")
    lines += ["", f"Path timing availability: {summary['path_timing_records']}/{summary['modules']} records."]
    if summary["path_timing_records"]:
        lines += ["", "| Phase | Bindings on a plan ms | General bindings ms |",
                  "|---|---:|---:|"]
        for phase in ("typecheck", "conversion"):
            lines.append(f"| {phase} | {summary[f'planned_{phase}_ns'] / 1e6:.3f} | {summary[f'general_{phase}_ns'] / 1e6:.3f} |")
    if summary["paths"]:
        lines += ["", "| Path | Bindings |", "|---|---:|"]
        for reason, count in sorted(summary["paths"].items()):
            lines.append(f"| {reason} | {count} |")
    if summary["failed_obligations"]:
        lines += ["", "| Failed obligation / expected type shape | Abandoned attempts |", "|---|---:|"]
        for key, count in sorted(summary["failed_obligations"].items()):
            lines.append(f"| {key} | {count} |")
    if summary["general_cost_records"]:
        lines += ["", f"General cost availability: {summary['general_cost_records']}/{summary['modules']} records.",
                  "", "| General reason | Bindings | Generated body syntax nodes | Typecheck ms |", "|---|---:|---:|---:|"]
        for reason, cost in summary["general_costs"].items():
            lines.append(f"| {reason} | {summary['paths'].get(reason, 0)} | {cost['general_syntax_nodes']} | {cost['general_typecheck_ns'] / 1e6:.3f} |")
    if summary["unplanned_forms"]:
        lines += ["", "| First unplanned form | Bindings |", "|---|---:|"]
        for form, count in summary["unplanned_forms"].items():
            lines.append(f"| {form} | {count} |")
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
        lines += ["", f"Distinct templates: {summary['distinct_templates']} among {summary['supported_templates']} supported bindings; duplicate bindings: {summary['duplicate_bindings']}; unsupported templates: {summary['unsupported_templates']}.",
                  f"Distinct-template body nodes: {summary['distinct_template_nodes']} / {summary['template_body_nodes']} ({summary['distinct_template_node_share']:.1%}); unsupported body nodes: {summary['unsupported_template_nodes']}.",
                  f"Singleton templates: {summary['singleton_templates']}; highest frequencies: {summary['most_frequent_templates']}."]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census")
    parser.add_argument("--module-contains", help="Filter module names by substring")
    parser.add_argument("--modules-from", type=Path, help="Select module basenames present in this fixture source directory")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable totals")
    args = parser.parse_args()
    try:
        with open(args.census, encoding="utf-8") as source:
            rows = (json.loads(line) for line in source if line.strip())
            if args.module_contains:
                rows = (row for row in rows if args.module_contains in row["module"])
            if args.modules_from:
                selected = {p.stem for p in args.modules_from.rglob("*.res")} | {p.stem for p in args.modules_from.rglob("*.resi")}
                rows = (row for row in rows if Path(row["module"]).stem in selected)
            summary = summarize(rows)
        print(json.dumps(summary, indent=2) if args.json else markdown(summary))
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"derived census: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
