#!/usr/bin/env python3
"""Canonicalize ident stamps in raw lambda (-drawlambda) output.

Reads raw lambda text from stdin, replaces all "name/stamp" occurrences
(where stamp >= 1000) with "name/N" where N is a sequential canonical
number assigned per-name on first occurrence in reading order.

For function bodies, both ident stamps and exit codes are canonicalized
per-function to handle different global allocation orders between compilers.

Stamps < 1000 (field positions, tag numbers, predef stamps) are left unchanged.
"""

import sys
import re

def canonicalize(text):
    # Split into lines for per-function processing
    lines = text.split('\n')

    # Match name/stamp where stamp is a 4+ digit number (>= 1000).
    stamp_pattern = re.compile(r'([a-zA-Z_*$~!@#%^&\-+=<>:?|.][a-zA-Z0-9_*\'$~!@#%^&\-+=<>:?|.()]*)/(\d{4,})')
    exit_pattern = re.compile(r'(?<=\(exit )(\d+)(?=[\s)])|(?<=with \()(\d+)(?=[\s)])')
    func_pattern = re.compile(r'\(function\b')

    # Per-name stamp maps and exit maps — reset at function boundaries
    stamp_map = {}
    next_per_name = {}
    exit_map = {}
    next_exit = [1]

    result_lines = []

    for line in lines:
        # Reset all maps at function boundaries
        if func_pattern.search(line):
            stamp_map = {}
            next_per_name = {}
            exit_map = {}
            next_exit[0] = 1

        def replace_stamp(m):
            name = m.group(1)
            old_stamp = int(m.group(2))
            key = (name, old_stamp)
            if key not in stamp_map:
                counter = next_per_name.get(name, 1)
                stamp_map[key] = counter
                next_per_name[name] = counter + 1
            return f'{name}/{stamp_map[key]}'

        def replace_exit(m):
            old_num = int(m.group(1) or m.group(2))
            if old_num not in exit_map:
                exit_map[old_num] = next_exit[0]
                next_exit[0] += 1
            return str(exit_map[old_num])

        line = stamp_pattern.sub(replace_stamp, line)
        line = exit_pattern.sub(replace_exit, line)
        result_lines.append(line)

    return '\n'.join(result_lines)

if __name__ == '__main__':
    data = sys.stdin.buffer.read().decode('latin-1')
    result = canonicalize(data)
    sys.stdout.buffer.write(result.encode('latin-1'))
