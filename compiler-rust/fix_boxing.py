#!/usr/bin/env python3
"""Fix corrupted match arms from boxing script.

The boxing script introduced corruption in match arms:
1. `let (a, b) = *inner;` in borrowed match contexts -> `let (ref a, ref b) = **inner;`
2. Match arm body ending with `,` instead of `}` (missing closing brace)
3. Extra `}}` at end of match blocks

Strategy:
- Find lines matching `let (...) = *inner;` or `let Struct { .. } = *inner;`
- Look at the line before to find the match arm header (the `Variant(inner) => {` line)
- Determine the arm header indent
- Scan forward to find the line at or below arm header indent that isn't part of the body
- The last line of the body should end with `,` which we fix to remove `,` and add `}`
"""

import re
import sys
import os


def add_ref_to_let(line):
    """Convert `let (a, b) = *inner;` to `let (ref a, ref b) = **inner;`"""

    # Tuple: let (a, b, ..) = *inner;
    m = re.match(r'^(\s*)let \((.+)\) = \*(\w+);$', line)
    if m:
        indent, vars_str, inner = m.group(1), m.group(2), m.group(3)
        parts = [p.strip() for p in vars_str.split(',')]
        ref_parts = []
        for p in parts:
            p = p.strip()
            if not p or p in ('_', '..') or p.startswith('ref ') or p.startswith('..'):
                ref_parts.append(p)
            else:
                ref_parts.append(f'ref {p}')
        return f'{indent}let ({", ".join(ref_parts)}) = **{inner};'

    # Named struct with single-line fields: let Name { field1, field2: val, .. } = *inner;
    m = re.match(r'^(\s*)let (\w+)\s*\{(.+)\}\s*= \*(\w+);$', line)
    if m:
        indent, name, fields_str, inner = m.group(1), m.group(2), m.group(3), m.group(4)
        parts = [p.strip() for p in fields_str.split(',')]
        ref_parts = []
        for p in parts:
            p = p.strip()
            if not p or p in ('_', '..') or p.startswith('ref '):
                ref_parts.append(p)
            elif ':' in p:
                field, val = p.split(':', 1)
                val = val.strip()
                if val in ('_', '..') or val.startswith('ref '):
                    ref_parts.append(p)
                else:
                    ref_parts.append(f'{field.strip()}: ref {val}')
            else:
                ref_parts.append(f'ref {p}')
        return f'{indent}let {name} {{ {", ".join(ref_parts)} }} = **{inner};'

    return None


def get_indent(line):
    """Get the indentation level of a line."""
    return len(line) - len(line.lstrip()) if line.strip() else -1


def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()

    lines = content.split('\n')
    fixed_lines = []
    i = 0
    changes = 0
    total_lines = len(lines)

    while i < total_lines:
        line = lines[i]
        stripped = line.strip()

        # Fix doubled closing braces
        if stripped in ('}}', '}};', '}}};', '}}}'):
            indent = get_indent(line)
            new = stripped.replace('}}', '}', 1)
            fixed_lines.append(' ' * indent + new)
            changes += 1
            i += 1
            continue

        # Check for let destructuring pattern
        is_let_destr = bool(
            re.match(r'^\s+let \(.+\) = \*\w+;$', line) or
            re.match(r'^\s+let \w+\s*\{.+\}\s*= \*\w+;$', line)
        )

        if is_let_destr:
            let_indent = get_indent(line)

            # Find the arm header line (should be just before this let)
            prev_i = i - 1
            while prev_i >= 0 and not lines[prev_i].strip():
                prev_i -= 1

            if prev_i >= 0:
                arm_header = lines[prev_i]
                arm_header_indent = get_indent(arm_header)

                # The arm body should end when we see a line at arm_header_indent or less
                # that isn't a blank line
                j = i + 1
                arm_end = i  # default: the let line itself is the last

                while j < total_lines:
                    next_line = lines[j]
                    next_stripped = next_line.strip()

                    if not next_stripped:
                        j += 1
                        continue

                    next_indent = get_indent(next_line)

                    # If indent is at or below the arm header indent, we've exited the arm body
                    if next_indent <= arm_header_indent:
                        # arm_end is the last non-empty line before this
                        arm_end = j - 1
                        while arm_end > i and not lines[arm_end].strip():
                            arm_end -= 1
                        break

                    j += 1

                if arm_end > i:
                    last_body_line = lines[arm_end]
                    last_stripped = last_body_line.rstrip()

                    # Check if last body line ends with `,` (the corruption)
                    if last_stripped.endswith(','):
                        # Apply fix:
                        # 1. Add ref to the let line
                        fixed_let = add_ref_to_let(line)
                        if fixed_let:
                            fixed_lines.append(fixed_let)
                        else:
                            fixed_lines.append(line)

                        # 2. Copy lines between let and last body line
                        for k in range(i + 1, arm_end):
                            fixed_lines.append(lines[k])

                        # 3. Fix the last body line: remove trailing `,`
                        fixed_last = last_stripped[:-1]
                        fixed_lines.append(fixed_last)

                        # 4. Add closing `}` at arm header indent level
                        fixed_lines.append(' ' * arm_header_indent + '}')

                        changes += 1
                        i = arm_end + 1
                        continue
                    else:
                        # Arm body is properly closed, but let line still needs ref fix
                        fixed_let = add_ref_to_let(line)
                        if fixed_let:
                            fixed_lines.append(fixed_let)
                            changes += 1
                            i += 1
                            continue

        # Default: keep line unchanged
        fixed_lines.append(line)
        i += 1

    if changes > 0:
        with open(path, 'w') as f:
            f.write('\n'.join(fixed_lines))
        print(f"Fixed {changes} patterns in {path}")
    else:
        print(f"No changes in {path}")


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: fix_boxing.py <file1.rs> [file2.rs ...]")
        sys.exit(1)

    for path in sys.argv[1:]:
        if os.path.exists(path):
            fix_file(path)
        else:
            print(f"File not found: {path}")
