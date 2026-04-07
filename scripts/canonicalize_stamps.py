#!/usr/bin/env python3
"""Canonicalize ident stamps in sexp typed tree output.

Reads sexp text from stdin, replaces all "name/stamp" atoms (where stamp > 0)
with "name/N" where N is a sequential canonical number assigned per-name on
first occurrence in reading order.

Per-name canonicalization means each identifier name gets its own counter:
  "x/42" -> "x/1", "y/43" -> "y/1", "x/44" -> "x/2"

This makes comparison insensitive to stamp allocation order while preserving
the identity/sharing pattern — same binding gets same canonical stamp, different
bindings of the same name get different canonical stamps.
"""

import sys
import re

def canonicalize(text):
    # Match quoted "name/stamp" atoms where stamp is a positive integer
    pattern = re.compile(r'"([^"]*)/(\d+)"')

    # Per-name: maps (name, old_stamp) -> canonical_stamp
    stamp_map = {}
    # Per-name counters
    next_per_name = {}

    def replace(m):
        name = m.group(1)
        old_stamp = int(m.group(2))
        if old_stamp == 0:
            return m.group(0)  # persistent ident, leave as-is
        key = (name, old_stamp)
        if key not in stamp_map:
            counter = next_per_name.get(name, 1)
            stamp_map[key] = counter
            next_per_name[name] = counter + 1
        return f'"{name}/{stamp_map[key]}"'

    return pattern.sub(replace, text)

if __name__ == '__main__':
    # Read as Latin-1 (raw bytes) since OCaml sexp output may contain non-UTF-8
    data = sys.stdin.buffer.read().decode('latin-1')
    result = canonicalize(data)
    sys.stdout.buffer.write(result.encode('latin-1'))
