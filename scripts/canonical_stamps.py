#!/usr/bin/env python3
"""Renumber the local identifier stamps of a typed-tree or Lambda dump.

Usage: canonical_stamps.py FILE...   (rewrites each FILE in place)

Each `name/N` with N >= 1000 (a stamp from Ident.create; lower stamps are the
predefined identifiers) becomes `name/K`, K counting from 1000 in order of
first appearance. Two dumps then agree exactly when they bind and use the same
identifiers in the same places, whatever their first stamp was.

The in-process build does not spend the stamps OCaml's `.cmi` read spends when
it renames another unit's signature (see env_lazy.rs), so its stamps are offset
from OCaml's while the identifiers themselves line up.
"""
import re
import sys

STAMP = re.compile(rb"/([0-9]{4,})(?=[\")\s])")


def canonical(data):
    mapping = {}

    def renumber(match):
        stamp = int(match.group(1))
        if stamp < 1000:
            return match.group(0)
        if stamp not in mapping:
            mapping[stamp] = 1000 + len(mapping)
        return b"/%d" % mapping[stamp]

    return STAMP.sub(renumber, data)


for path in sys.argv[1:]:
    with open(path, "rb") as f:
        data = f.read()
    with open(path, "wb") as f:
        f.write(canonical(data))
