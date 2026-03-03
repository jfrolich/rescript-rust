#!/usr/bin/env python3
"""Expand #N type references in deduped sexp back to inline types for diffing.

The dedup format is:
  (types
    (0 <sexp>)
    (1 <sexp>)
    ...)
  (structure ...)

This script replaces every #N in the body with the corresponding type sexp,
producing output equivalent to the old inline format.
"""
import sys
import re


def parse_types_preamble(content):
    """Parse the (types ...) preamble into a dict of idx -> sexp_string."""
    # Find the preamble end: first line starting with (structure or (signature
    lines = content.split('\n')
    preamble_end = len(lines)
    for i, line in enumerate(lines):
        if line.startswith('(structure') or line.startswith('(signature'):
            preamble_end = i
            break

    preamble = '\n'.join(lines[:preamble_end])
    body = '\n'.join(lines[preamble_end:])

    # Parse entries using paren balancing
    type_map = {}
    entry_starts = [m.start() for m in re.finditer(r'\n  \((\d+)\n', preamble)]
    for i, start in enumerate(entry_starts):
        end = entry_starts[i + 1] if i + 1 < len(entry_starts) else len(preamble)
        chunk = preamble[start:end].strip()
        m = re.match(r'\((\d+)\n(.*)', chunk, re.DOTALL)
        if m:
            idx = m.group(1)
            rest = m.group(2).strip()
            # Find balanced close paren for the outer (N ...)
            depth = 1
            pos = len(rest)
            for j, ch in enumerate(rest):
                if ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
                    if depth == 0:
                        pos = j
                        break
            body_text = rest[:pos].strip()
            # Dedent 4 spaces
            dedented = '\n'.join(
                line[4:] if line.startswith('    ') else line
                for line in body_text.split('\n')
            )
            type_map[idx] = dedented

    return type_map, body


def expand_refs(text, type_map, depth=0):
    """Expand all #N references, handling recursive types (max depth)."""
    if depth > 100:
        return text
    def replacer(m):
        idx = m.group(1)
        if idx in type_map:
            return expand_refs(type_map[idx], type_map, depth + 1)
        return m.group(0)
    return re.sub(r'#(\d+)', replacer, text)


def main():
    with open(sys.argv[1], 'r') as f:
        content = f.read()

    # Check if this is dedup format
    if not content.startswith('(types'):
        sys.stdout.write(content)
        return

    type_map, body = parse_types_preamble(content)
    if not type_map:
        sys.stdout.write(content)
        return

    # Expand all references in the body
    expanded = expand_refs(body, type_map)
    sys.stdout.write(expanded)


if __name__ == '__main__':
    main()
