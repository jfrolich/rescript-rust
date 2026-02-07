#!/usr/bin/env python3
"""Fix extra closing paren left by fix_pattern_box.py.

The script replaced `Variant(Box::new((a, b)))` with `Variant(inner))`
leaving an extra `)`. This script removes those extra `)`.
"""

import re
import sys
import os

# These are the variant names that were boxed
VARIANTS = [
    'Pexp_let', 'Pexp_match', 'Pexp_try', 'Pexp_variant', 'Pexp_record',
    'Pexp_setfield', 'Pexp_ifthenelse', 'Pexp_for', 'Pexp_constraint',
    'Pexp_coerce', 'Pexp_send', 'Pexp_letmodule', 'Pexp_letexception',
    'Pexp_newtype', 'Pexp_open',
    'Ppat_interval', 'Ppat_variant', 'Ppat_record', 'Ppat_constraint',
    'Ptyp_arrow', 'Ptyp_constr', 'Ptyp_object', 'Ptyp_alias', 'Ptyp_variant',
    'Ptyp_poly', 'Ptyp_package', 'Ptyp_extension',
    'Pstr_eval', 'Pstr_value', 'Pstr_type', 'Pstr_extension',
    'Psig_type', 'Psig_extension',
    'Pmod_functor', 'Pmod_structure',
    'Pmty_functor', 'Pmty_with',
    'PPat',
]


def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    original = content
    changes = 0

    for variant in VARIANTS:
        # Fix `Variant(inner))` -> `Variant(inner)`
        # But be careful not to match constructor calls like `Variant(Box::new((a, b)))`
        # Only fix in pattern contexts
        pattern = re.compile(r'(' + variant + r'\(inner\))\)')
        while pattern.search(content):
            content = pattern.sub(r'\1', content, count=1)
            changes += 1

        # Also fix `Variant(inner)),` -> `Variant(inner),` etc.
        # And `Variant(inner))` at end of line -> `Variant(inner)`

    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed {changes} extra parens in {filepath}")
    else:
        print(f"No extra parens in {filepath}")

    return changes


if __name__ == '__main__':
    base = '/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust'
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
    total = 0
    for f in files:
        path = os.path.join(base, f)
        if os.path.exists(path):
            total += fix_file(path)
    print(f"\nTotal: {total} fixes")
