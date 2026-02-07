#!/usr/bin/env python3
"""Fix old multi-arg patterns in matches!() macros.

In matches!() macros, we never bind variables, so any multi-arg variant
can safely become single-wildcard Variant(_).

E.g., matches!(expr, Pexp_let(_, _, _)) -> matches!(expr, Pexp_let(_))
"""

import re
import sys
import os

BASE_DIR = '/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust'

# Variants that were changed from multi-arg to single Box<tuple> arg.
BOXED_VARIANTS = [
    'Pexp_let', 'Pexp_match', 'Pexp_try', 'Pexp_variant', 'Pexp_record',
    'Pexp_setfield', 'Pexp_ifthenelse', 'Pexp_for', 'Pexp_constraint',
    'Pexp_coerce', 'Pexp_send', 'Pexp_letmodule', 'Pexp_letexception',
    'Pexp_newtype', 'Pexp_open',
    'Ppat_interval', 'Ppat_variant', 'Ppat_record', 'Ppat_constraint',
    'Ptyp_arrow', 'Ptyp_constr', 'Ptyp_object', 'Ptyp_alias', 'Ptyp_variant',
    'Ptyp_poly',
    'Pstr_eval', 'Pstr_value', 'Pstr_type', 'Pstr_extension',
    'Psig_type', 'Psig_extension',
    'Pmod_functor',
    'Pmty_functor', 'Pmty_with',
    'PPat',
]


def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    original = content
    changes = 0

    for variant in BOXED_VARIANTS:
        # Replace Variant(_, _, _) with Variant(_) - wildcard patterns
        # Match patterns like:  Variant(_, _, _)  or  Variant(_, _)  or Variant(_, _, _, _, _)
        # But NOT Variant(_) which is already correct
        # And NOT Variant(some_var) which binds a variable (not a wildcard)

        # Pattern: variant followed by ( and 2+ comma-separated items that are all _ or _-prefixed )
        # This covers: Variant(_, _), Variant(_, _, _), Variant(a, _, _), etc.
        pattern = re.compile(
            r'(' + re.escape(variant) + r')\(([^)]+)\)'
        )

        def replace_pattern(m):
            nonlocal changes
            args_text = m.group(2)
            args = [a.strip() for a in args_text.split(',')]

            # Only replace if there are 2+ args AND they're all wildcards/underscored
            if len(args) >= 2:
                # Check if ALL args are wildcards (_, .., or _name patterns)
                all_wildcards = all(
                    a == '_' or a == '..' or a.startswith('_')
                    for a in args
                )
                if all_wildcards:
                    changes += 1
                    return m.group(1) + '(_)'

            return m.group(0)

        content = pattern.sub(replace_pattern, content)

    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"Fixed {changes} matches patterns in {filepath}")
    else:
        print(f"No matches pattern changes in {filepath}")

    return changes


if __name__ == '__main__':
    files = [
        'src/parser/parsetree_viewer.rs',
        'src/parser/printer.rs',
        'src/parser/ml_printer.rs',
        'src/parser/comment_table.rs',
        'src/parser/core.rs',
        'src/parser/expr.rs',
        'src/parser/module.rs',
        'src/parser/typ.rs',
        'src/parser/pattern.rs',
        'src/parser/jsx_ppx.rs',
        'src/binary_ast/ppx.rs',
        'src/binary_ast/spice_ppx.rs',
        'src/binary_ast/deps.rs',
        'src/binary_ast/current_marshal.rs',
        'src/binary_ast/mapper_from0.rs',
        'src/binary_ast/mapper_to0.rs',
        'src/binary_ast/writer.rs',
        'src/binary_ast/parsetree0_marshal.rs',
        'src/types/typecore.rs',
        'src/types/typemod.rs',
    ]
    total = 0
    for f in files:
        path = os.path.join(BASE_DIR, f)
        if os.path.exists(path):
            total += fix_file(path)
    print(f"\nTotal: {total} fixes")
