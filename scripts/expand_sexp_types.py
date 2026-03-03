#!/usr/bin/env python3
"""Expand #N type references in deduped sexp back to inline types for diffing."""
import sys
import re

def expand_sexp(input_file):
    with open(input_file, 'r') as f:
        content = f.read()
    
    # Split into types preamble and body
    # Find where (structure or (signature starts after (types ...)
    m = re.search(r'\n(\((?:structure|signature))', content)
    if not m:
        # No dedup format, output as-is
        sys.stdout.write(content)
        return
    
    types_section = content[:m.start()]
    body = content[m.start()+1:]  # +1 to skip the \n
    
    # Parse type definitions: (N <sexp>)
    type_map = {}
    # Match entries like:  (0\n    (Tvar None))
    for entry in re.finditer(r'\((\d+)\n(.*?)(?=\n  \(\d+\n|\n\)$)', types_section, re.DOTALL):
        idx = entry.group(1)
        sexp_body = entry.group(2).strip()
        type_map[idx] = sexp_body
    
    # Recursively expand #N references in type bodies first
    max_iterations = 50
    for _ in range(max_iterations):
        changed = False
        for idx in type_map:
            old = type_map[idx]
            new = re.sub(r'#(\d+)', lambda m: type_map.get(m.group(1), m.group(0)), old)
            if new != old:
                type_map[idx] = new
                changed = True
        if not changed:
            break
    
    # Expand #N references in body
    expanded = re.sub(r'#(\d+)', lambda m: type_map.get(m.group(1), m.group(0)), body)
    
    sys.stdout.write(expanded)

if __name__ == '__main__':
    expand_sexp(sys.argv[1])
