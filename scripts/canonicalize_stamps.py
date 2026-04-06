#!/usr/bin/env python3
"""Canonicalize ident stamps in sexp typed tree output.

Reads sexp text from stdin, replaces all "name/stamp" atoms (where stamp > 0)
with "name/N" where N is a sequential canonical number assigned on first
occurrence in reading order. Stamps <= 0 (persistent, hidden) are left as-is.

This makes comparison insensitive to stamp allocation order while preserving
the identity/sharing pattern — same binding gets same canonical stamp, different
bindings get different canonical stamps.
"""

import sys
import re

def canonicalize(text):
    # Match quoted "name/stamp" atoms where stamp is a positive integer
    # The sexp format has these as: "name/1042"
    pattern = re.compile(r'"([^"]*)/(\d+)"')

    next_canonical = [1]  # mutable counter in list for closure access
    stamp_map = {}  # old_stamp (int) -> canonical_stamp (int)

    def replace(m):
        name = m.group(1)
        old_stamp = int(m.group(2))
        if old_stamp == 0:
            return m.group(0)  # persistent ident, leave as-is
        if old_stamp not in stamp_map:
            stamp_map[old_stamp] = next_canonical[0]
            next_canonical[0] += 1
        return f'"{name}/{stamp_map[old_stamp]}"'

    return pattern.sub(replace, text)

if __name__ == '__main__':
    # Read as Latin-1 (raw bytes) since OCaml sexp output may contain non-UTF-8
    data = sys.stdin.buffer.read().decode('latin-1')
    result = canonicalize(data)
    sys.stdout.buffer.write(result.encode('latin-1'))
