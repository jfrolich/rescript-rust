#!/usr/bin/env python3
"""Fix the pattern where `}` and `]),` are swapped.

The fix_boxing.py script incorrectly places `}` before `]),` like:
    expression(arena, body)
}
]),

This should be:
    expression(arena, body),
])
}
"""

import re
import sys
import os


def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()

    lines = content.split('\n')
    fixed_lines = []
    i = 0
    changes = 0
    total = len(lines)

    while i < total:
        line = lines[i]
        stripped = line.strip()

        # Pattern: `}` on one line, `]),` or `])` on the next
        if i + 1 < total:
            next_stripped = lines[i + 1].strip()

            if stripped == '}' and next_stripped in (']),', '])', ']),}'):
                # Get indents
                cur_indent = len(line) - len(line.lstrip())
                next_indent = len(lines[i + 1]) - len(lines[i + 1].lstrip())

                # Need to look at the line BEFORE `}` - if it doesn't end with `,`,
                # we need to add one (it was the last element in vec![])
                if fixed_lines:
                    prev = fixed_lines[-1].rstrip()
                    if prev and not prev.endswith(',') and not prev.endswith('{') and not prev.endswith('('):
                        fixed_lines[-1] = prev + ','

                # Emit `])` then `}` (swapping the order)
                close_bracket = next_stripped.rstrip(',')  # `])` without trailing comma
                fixed_lines.append(' ' * next_indent + close_bracket)
                fixed_lines.append(' ' * cur_indent + '}')

                changes += 1
                i += 2
                continue

        # Also fix `}};` -> `};`
        if stripped == '}};':
            indent = len(line) - len(line.lstrip())
            fixed_lines.append(' ' * indent + '};')
            changes += 1
            i += 1
            continue

        # Also fix `}}` -> `}`
        if stripped == '}}':
            indent = len(line) - len(line.lstrip())
            fixed_lines.append(' ' * indent + '}')
            changes += 1
            i += 1
            continue

        fixed_lines.append(line)
        i += 1

    if changes > 0:
        with open(path, 'w') as f:
            f.write('\n'.join(fixed_lines))
        print(f"Fixed {changes} brace/bracket swaps in {path}")
    else:
        print(f"No brace/bracket issues in {path}")


if __name__ == '__main__':
    for path in sys.argv[1:]:
        if os.path.exists(path):
            fix_file(path)
        else:
            print(f"File not found: {path}")
