#!/usr/bin/env python3
"""Fix remaining compilation errors from boxing AST enum variants.

This script handles:
1. E0023: Pattern field count mismatches - old multi-arg patterns that need inner + destructure
2. E0061: Constructor arg count mismatches - old multi-arg constructors that need Box::new((...))
3. E0408: Variable not bound in all | patterns - split into separate arms
4. E0422: Missing PexpFun/PexpApply imports
5. E0164: Box::new in pattern position
6. E0308: Various type mismatches from boxing changes
"""

import re
import subprocess
import sys
import os


def get_errors():
    """Run cargo check and parse errors."""
    result = subprocess.run(
        ['cargo', 'check', '--message-format=short'],
        capture_output=True, text=True,
        cwd='/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust'
    )
    errors = []
    for line in result.stderr.split('\n'):
        # Parse lines like: src/binary_ast/deps.rs:343:13: error[E0408]: ...
        m = re.match(r'(src/\S+):(\d+):(\d+): error\[(\w+)\]: (.*)', line)
        if m:
            errors.append({
                'file': m.group(1),
                'line': int(m.group(2)),
                'col': int(m.group(3)),
                'code': m.group(4),
                'msg': m.group(5),
            })
    return errors


def add_imports(filepath):
    """Add missing PexpFun/PexpApply imports to a file."""
    with open(filepath, 'r') as f:
        content = f.read()

    needs_pexp_fun = 'PexpFun' in content and 'use crate::parser::PexpFun' not in content and 'parser::ast::PexpFun' not in content
    needs_pexp_apply = 'PexpApply' in content and 'use crate::parser::PexpApply' not in content and 'parser::ast::PexpApply' not in content

    if not needs_pexp_fun and not needs_pexp_apply:
        return False

    # Find the right place to add imports - after existing use crate::parser lines
    lines = content.split('\n')
    insert_idx = None
    for i, line in enumerate(lines):
        if 'use crate::parser' in line or 'use super::' in line:
            insert_idx = i + 1

    if insert_idx is None:
        # Find after any use statements
        for i, line in enumerate(lines):
            if line.startswith('use '):
                insert_idx = i + 1

    if insert_idx is None:
        return False

    imports = []
    if needs_pexp_fun:
        imports.append('use crate::parser::PexpFun;')
    if needs_pexp_apply:
        imports.append('use crate::parser::PexpApply;')

    for imp in reversed(imports):
        lines.insert(insert_idx, imp)

    with open(filepath, 'w') as f:
        f.write('\n'.join(lines))

    print(f"Added imports to {filepath}: {', '.join(imports)}")
    return True


def fix_imports():
    """Fix all missing imports."""
    files_needing_imports = set()
    errors = get_errors()
    for err in errors:
        if err['code'] == 'E0422' and ('PexpFun' in err['msg'] or 'PexpApply' in err['msg']):
            filepath = os.path.join('/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust', err['file'])
            files_needing_imports.add(filepath)

    for filepath in files_needing_imports:
        add_imports(filepath)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'imports':
        fix_imports()
    else:
        print("Usage: fix_remaining.py imports")
        print("  imports: Add missing PexpFun/PexpApply imports")
