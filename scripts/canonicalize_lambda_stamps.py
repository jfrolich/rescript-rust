#!/usr/bin/env python3
"""Canonicalize ident stamps in raw lambda (-drawlambda) output.

Reads raw lambda text from stdin, replaces all "name/stamp" occurrences
(where stamp >= 1000) with "name/N" where N is a sequential canonical
number assigned per-name on first occurrence in reading order.

Per-name canonicalization means each identifier name gets its own counter:
  "x/1042" -> "x/1", "y/1043" -> "y/1", "x/1044" -> "x/2"

This makes comparison insensitive to stamp allocation order while preserving
the identity/sharing pattern — same binding gets same canonical stamp, different
bindings of the same name get different canonical stamps.

Stamps < 1000 (field positions, tag numbers, predef stamps) are left unchanged.
"""

import sys
import re

def canonicalize(text):
    # Match name/stamp where stamp is a 4+ digit number (>= 1000).
    # Identifiers can contain letters, digits, underscores, *, and ' (e.g., *opt*/1234).
    # We use a lookbehind for a non-/ character (or start) to avoid matching inside paths,
    # and match the identifier name before the /stamp.
    # Stamps < 1000 are field positions, tag numbers, or predef stamps — left unchanged.
    pattern = re.compile(r'([a-zA-Z_*][a-zA-Z0-9_*\']*)/(\d{4,})')

    # Per-name: maps (name, old_stamp) -> canonical_stamp
    stamp_map = {}
    # Per-name counters
    next_per_name = {}

    def replace(m):
        name = m.group(1)
        old_stamp = int(m.group(2))
        key = (name, old_stamp)
        if key not in stamp_map:
            counter = next_per_name.get(name, 1)
            stamp_map[key] = counter
            next_per_name[name] = counter + 1
        return f'{name}/{stamp_map[key]}'

    return pattern.sub(replace, text)

if __name__ == '__main__':
    data = sys.stdin.buffer.read().decode('latin-1')
    result = canonicalize(data)
    sys.stdout.buffer.write(result.encode('latin-1'))
