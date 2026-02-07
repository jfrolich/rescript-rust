#!/usr/bin/env python3
"""Fix Box::new((...)) in pattern positions.

The fix_all_boxing.py script incorrectly wrapped some patterns in Box::new((...)).
In match arm patterns, `Variant(Box::new((a, b)))` is invalid Rust.
It should be `Variant(inner)` with `let (ref a, ref b) = **inner;` inside.

This script finds all `Box::new((` in pattern positions and replaces them.
"""

import re
import sys
import os


def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    original = content
    changes = 0

    # Pattern: In a match arm, `Variant(Box::new((args...)))` is wrong
    # We need to detect these and replace with `Variant(inner)` + destructure
    #
    # The tricky part is identifying pattern vs constructor context.
    # Box::new((...)) in a `let ... =` left side is a pattern.
    # Box::new((...)) in a match arm left side (before =>) is a pattern.
    #
    # Simple approach: find `Box::new((` and check if it's in a pattern context.
    # A reliable indicator is whether there's a `=>` after the closing parens on the same logical line.

    lines = content.split('\n')
    new_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check for Box::new(( in what looks like a match pattern or let pattern
        m = re.search(r'(\w+)::(\w+)\(Box::new\(\(', line)
        if m:
            # Check if this is a pattern context
            # Indicators of pattern context:
            # 1. Line starts with | (or-pattern)
            # 2. Line is inside a match { } block (has => later)
            # 3. Line has `let ... =` before the variant

            stripped = line.strip()

            # Check if there's => on this line (match pattern for sure)
            # Also check if the line starts at an indentation level consistent with match arm
            is_pattern = False

            # Check if => appears after the Box::new((...)) closing
            # Or if this is in a `let ... else` pattern
            if '=>' in line[m.end():]:
                is_pattern = True
            elif line.strip().startswith('|'):
                is_pattern = True
            elif 'let ' in line[:m.start()] and '=' not in line[m.start():].split('Box::new')[0]:
                is_pattern = True
            # Check following lines for =>
            elif i + 1 < len(lines) and '=>' in lines[i + 1]:
                is_pattern = True
            elif i + 2 < len(lines) and '=>' in lines[i + 2]:
                is_pattern = True

            if is_pattern:
                # Find the full Box::new((...)) span
                box_start = line.find('Box::new((', m.start())
                if box_start >= 0:
                    # Count parens to find matching close
                    depth = 0
                    pos = box_start + len('Box::new(')
                    # Now at first ( of the inner tuple
                    args_start = pos + 1  # skip the (
                    j = i
                    full_text = line[pos:]
                    in_str = False

                    # Find matching ))
                    k = 0
                    paren_depth = 0
                    found = False
                    while k < len(full_text):
                        c = full_text[k]
                        if c == '(':
                            paren_depth += 1
                        elif c == ')':
                            paren_depth -= 1
                            if paren_depth == 0:
                                # Found the inner close
                                # Check if next char is also )
                                if k + 1 < len(full_text) and full_text[k + 1] == ')':
                                    # Found the )) closing Box::new((...))
                                    # The args are full_text[1:k] (between the inner parens)
                                    inner_args = full_text[1:k]

                                    # Replace Box::new((args)) with just inner
                                    # But we need to figure out what variable name to use
                                    # If the args are all simple (like `a, b`), we could use
                                    # a wildcard or `inner`. Let's use `inner`.
                                    prefix = m.group(1)
                                    variant = m.group(2)

                                    # Check if args look like bindings (simple variable names)
                                    # or complex patterns
                                    args_stripped = inner_args.strip()

                                    # For now, just replace with `inner` and we'll handle
                                    # the destructuring separately
                                    before = line[:m.start() + len(prefix) + 2 + len(variant) + 1]
                                    after_close = line[pos + k + 2:]

                                    new_line = before + 'inner)' + after_close
                                    new_lines.append(new_line)
                                    changes += 1
                                    found = True
                                    i += 1
                                    break
                                else:
                                    break
                        k += 1

                    if not found:
                        new_lines.append(line)
                        i += 1
                else:
                    new_lines.append(line)
                    i += 1
            else:
                new_lines.append(line)
                i += 1
        else:
            new_lines.append(line)
            i += 1

    content = '\n'.join(new_lines)

    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed {changes} Box::new((...)) in patterns in {filepath}")
    else:
        print(f"No pattern Box::new issues in {filepath}")

    return changes


if __name__ == '__main__':
    files = [
        'src/parser/printer.rs',
        'src/parser/ml_printer.rs',
        'src/parser/parsetree_viewer.rs',
        'src/parser/core.rs',
        'src/binary_ast/ppx.rs',
        'src/parser/comment_table.rs',
        'src/binary_ast/mapper_from0.rs',
        'src/binary_ast/writer.rs',
        'src/binary_ast/spice_ppx.rs',
        'src/binary_ast/mapper_to0.rs',
        'src/binary_ast/deps.rs',
        'src/binary_ast/current_marshal.rs',
        'src/parser/pattern.rs',
        'src/parser/expr.rs',
        'src/parser/module.rs',
        'src/parser/typ.rs',
        'src/parser/jsx_ppx.rs',
        'src/types/typecore.rs',
        'src/types/typemod.rs',
    ]
    base = '/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust'
    total = 0
    for f in files:
        path = os.path.join(base, f)
        if os.path.exists(path):
            total += fix_file(path)
    print(f"\nTotal: {total} pattern fixes")
