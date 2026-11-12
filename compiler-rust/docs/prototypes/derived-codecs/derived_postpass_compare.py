#!/usr/bin/env python3
"""Measurement prototype: is the Lambda after the passes fixed per derive template?

Inputs: the census JSONL (RESCRIPT_DERIVED_CENSUS) and the post-pass dump
(RESCRIPT_DERIVED_POSTPASS) of one single-worker clean build made with
derived-postpass-dump.patch applied. For every template with two or more
bindings, each binding's post-pass Lambda is normalized by replacing the names
the derive declared (fields, constructors, own codec names, default keys) with
their template indices and renumbering the remaining identifier stamps by first
occurrence. A template is "fixed" when all its instances normalize to one text.
"""
import collections
import json
import re
import sys

IDENT = re.compile(r"([A-Za-z_][A-Za-z0-9_$']*)/(\d+)")
STRING = re.compile(r'"((?:[^"\\]|\\.)*)"')
CTOR = re.compile(r"\[([A-Za-z_][A-Za-z0-9_]*):")


def normalize(text, tables):
    by_kind = collections.defaultdict(dict)
    for kind, name, index in tables:
        by_kind[kind][name] = index
    text = re.sub(r"field:([A-Za-z_][A-Za-z0-9_']*)/(\d+)(?! global)",
                  lambda m: f"field:F{by_kind['f'].get(m[1], m[1])}/{m[2]}", text)

    def string(m):
        value = m[1]
        for kind in ("l", "c", "f"):
            if value in by_kind[kind]:
                return f'"{kind.upper()}{by_kind[kind][value]}"'
        # The passes fold `key ++ " missing"` into one literal.
        if value.endswith(" missing") and value[:-8] in by_kind["l"]:
            return f'"L{by_kind["l"][value[:-8]]} missing"'
        return m[0]
    text = STRING.sub(string, text)
    # Record blocks print their field names: `(makeblock [x y] ...)`.
    text = re.sub(r"makeblock \[([^\]]*)\]", lambda m: "makeblock [" + " ".join(
        f"F{by_kind['f'].get(n, n)}" for n in m[1].split()) + "]", text)
    text = CTOR.sub(lambda m: f"[C{by_kind['c'].get(m[1], m[1])}:", text)
    # Constant constructors print bare (`[Ok: Regular]`, `` `Left ``).
    text = re.sub(r"(?<=[:`\[] )([A-Za-z_][A-Za-z0-9_]*)(?=[\] ])|(?<=`)([A-Za-z_][A-Za-z0-9_]*)",
                  lambda m: f"C{by_kind['c'][m[0]]}" if m[0] in by_kind["c"] else m[0], text)
    # Static exit numbers come from one counter per module.
    exits = {}
    text = re.sub(r"\(exit (\d+)|with \((\d+)\)",
                  lambda m: (f"(exit #{exits.setdefault(m[1], len(exits))}" if m[1]
                             else f"with (#{exits.setdefault(m[2], len(exits))})"), text)
    stamps = {}

    def ident(m):
        name = by_kind["v"].get(m[1], m[1])
        key = (m[1], m[2])
        stamps.setdefault(key, len(stamps))
        return f"{name if isinstance(name, str) else 'V' + str(name)}/#{stamps[key]}"
    # The printer breaks lines by width, which depends on name lengths.
    return " ".join(IDENT.sub(ident, text).split())


def main(census_path, dump_path, contains):
    lambdas, module = {}, None
    for line in open(dump_path):
        parts = line.rstrip("\n").split("\t", 2)
        if parts[0] == "M":
            module = parts[1]
        elif parts[0] == "B":
            key = (module, parts[1])
            # A name bound twice in one unit (nested modules) is ambiguous: drop it.
            lambdas[key] = None if key in lambdas else parts[2]
    groups = collections.defaultdict(list)
    bindings = missing = 0
    for line in open(census_path):
        row = json.loads(line)
        if contains not in row["module"]:
            continue
        seen = collections.Counter()
        for name, template, tables, shape, nodes in zip(
                row["shape_names"], row["templates"], row["shape_name_tables"],
                row["shape_classes"], row["shape_nodes"]):
            bindings += 1
            seen[name] += 1
            text = lambdas.get((row["module"], name))
            # A nested module's bindings are not top-level lets of the unit, and a
            # name bound twice in one unit is ambiguous in the dump: skip both.
            if row["shape_names"].count(name) > 1:
                text = None
            if template is None or text is None:
                missing += 1
                continue
            groups[bytes(template)].append(
                (row["module"].rsplit("/", 1)[-1], name, shape, nodes, normalize(text, tables), seen[name]))
    shared = {k: v for k, v in groups.items() if len(v) > 1}
    fixed = [k for k, v in shared.items() if len({i[4] for i in v}) == 1]
    print(f"bindings {bindings}, joined {bindings - missing}, templates {len(groups)}, "
          f"templates with 2+ joined bindings {len(shared)}, of which fixed {len(fixed)}, "
          f"not fixed {len(shared) - len(fixed)}")
    for key, instances in shared.items():
        texts = collections.Counter(i[4] for i in instances)
        if len(texts) > 1:
            print(f"\nNOT FIXED: {len(instances)} bindings, {len(texts)} post-pass shapes ({instances[0][2]}, {instances[0][3]} nodes)")
            shown = set()
            for module, name, _, _, text, _ in instances:
                if text not in shown:
                    shown.add(text)
                    print(f"  {module} {name}: {text[:400]}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "")
