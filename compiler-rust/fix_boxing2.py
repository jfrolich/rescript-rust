#!/usr/bin/env python3
"""Fix remaining boxing errors by pattern-matching on specific error types.

This script reads cargo check errors and applies mechanical fixes.
"""

import re
import subprocess
import sys
import os

BASE_DIR = '/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust'

# Map of variants to their new Box tuple types.
# Format: (variant_name, old_arg_count) -> new single Box tuple
BOXED_VARIANTS = {
    # ExpressionDesc
    'Pexp_let': 3,  # (RecFlag, Vec<ValueBinding>, Box<Expression>)
    'Pexp_match': 2,  # (Box<Expression>, Vec<Case>)
    'Pexp_try': 2,  # (Box<Expression>, Vec<Case>)
    'Pexp_variant': 2,  # (Label, Option<Box<Expression>>)
    'Pexp_record': 2,  # (Vec<ExpressionRecordField>, Option<Box<Expression>>)
    'Pexp_setfield': 3,  # (Box<Expression>, Loc<LidentIdx>, Box<Expression>)
    'Pexp_ifthenelse': 3,  # (Box<Expression>, Box<Expression>, Option<Box<Expression>>)
    'Pexp_for': 5,  # (Pattern, Box<Expression>, Box<Expression>, DirectionFlag, Box<Expression>)
    'Pexp_constraint': 2,  # (Box<Expression>, CoreType)
    'Pexp_coerce': 3,  # (Box<Expression>, Option<CoreType>, CoreType)
    'Pexp_send': 2,  # (Box<Expression>, Loc<Label>)
    'Pexp_letmodule': 3,  # (StringLoc, ModuleExpr, Box<Expression>)
    'Pexp_letexception': 2,  # (ExtensionConstructor, Box<Expression>)
    'Pexp_newtype': 2,  # (StringLoc, Box<Expression>)
    'Pexp_open': 3,  # (OverrideFlag, Loc<LidentIdx>, Box<Expression>)
    # PatternDesc
    'Ppat_interval': 2,  # (Constant, Constant)
    'Ppat_variant': 2,  # (Label, Option<Box<Pattern>>)
    'Ppat_record': 2,  # (Vec<PatternRecordField>, ClosedFlag)
    'Ppat_constraint': 2,  # (Box<Pattern>, CoreType)
    # CoreTypeDesc
    'Ptyp_arrow': 3,  # (Box<TypeArg>, Box<CoreType>, Arity)  -- but this is a tuple variant!
    'Ptyp_constr': 2,  # (Loc<LidentIdx>, Vec<CoreType>)
    'Ptyp_object': 2,  # (Vec<ObjectField>, ClosedFlag)
    'Ptyp_alias': 2,  # (Box<CoreType>, Cow<'static, str>)
    'Ptyp_variant': 3,  # (Vec<RowField>, ClosedFlag, Option<Vec<Label>>)
    'Ptyp_poly': 2,  # (Vec<StringLoc>, Box<CoreType>)
    # StructureItemDesc
    'Pstr_eval': 2,  # (Expression, Attributes)
    'Pstr_value': 2,  # (RecFlag, Vec<ValueBinding>)
    'Pstr_type': 2,  # (RecFlag, Vec<TypeDeclaration>)
    'Pstr_extension': 2,  # (Extension, Attributes)
    # SignatureItemDesc
    'Psig_type': 2,  # (RecFlag, Vec<TypeDeclaration>)
    'Psig_extension': 2,  # (Extension, Attributes)
    # ModuleExprDesc
    'Pmod_functor': 3,  # (StringLoc, Option<Box<ModuleType>>, Box<ModuleExpr>)
    # ModuleTypeDesc
    'Pmty_functor': 3,  # (StringLoc, Option<Box<ModuleType>>, Box<ModuleType>)
    'Pmty_with': 2,  # (Box<ModuleType>, Vec<WithConstraint>)
    # Payload
    'PPat': 2,  # (Box<Pattern>, Option<Box<Expression>>)
}


def get_errors_full():
    """Run cargo check and get full error output."""
    result = subprocess.run(
        ['cargo', 'check'],
        capture_output=True, text=True,
        cwd=BASE_DIR
    )
    return result.stderr


def fix_constructor_calls(filepath):
    """Fix constructor calls that still use old multi-arg syntax.

    E.g., ExpressionDesc::Pexp_match(Box::new(expr), cases)
    becomes ExpressionDesc::Pexp_match(Box::new((expr, cases)))

    Also: ExpressionDesc::Pexp_match(expr, cases) [without Box::new]
    becomes ExpressionDesc::Pexp_match(Box::new((expr, cases)))
    """
    with open(filepath, 'r') as f:
        content = f.read()

    original = content

    for variant, arg_count in BOXED_VARIANTS.items():
        # Pattern: Variant(Box::new(arg1), arg2, arg3, ...)
        # These need to become Variant(Box::new((arg1, arg2, arg3, ...)))
        # This is tricky because args can contain nested parens/brackets

        # Find all occurrences of the variant name used as a constructor (not in a pattern/match)
        # We look for lines that have `::Variant(` not in a `let` destructuring or match pattern
        pass

    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False


def fix_e0164_box_in_pattern(filepath):
    """Fix Box::new(...) used in pattern position.

    E.g., let ExpressionDesc::Pexp_apply(Box::new(PexpApply { funct, args, .. })) = &*expr.pexp_desc
    becomes:
    let ExpressionDesc::Pexp_apply(inner) = &*expr.pexp_desc
    let PexpApply { funct, args, .. } = &**inner;
    """
    with open(filepath, 'r') as f:
        content = f.read()

    lines = content.split('\n')
    new_lines = []
    i = 0
    changes = 0

    while i < len(lines):
        line = lines[i]

        # Match: let ExpressionDesc::Variant(Box::new(Struct { fields.. })) = expr else {
        # or: let ExpressionDesc::Variant(Box::new(Struct { fields across multiple lines })) = expr else {
        m = re.match(
            r'^(\s*)let\s+(\w+::)?(\w+)\(Box::new\((\w+)\s*\{(.*)',
            line
        )
        if m:
            indent = m.group(1)
            prefix = m.group(2) or ''
            variant = m.group(3)
            struct_name = m.group(4)
            rest_of_fields = m.group(5)

            # Collect the full pattern until we find `}) = expr else {` or `}) = expr;`
            full_pattern = rest_of_fields
            j = i
            while True:
                # Check if this line contains the closing `})) = ...`
                close_match = re.search(r'\}\)\)\s*=\s*(.+?)(?:\s+else\s*\{)?$', lines[j] if j == i else lines[j])
                if close_match:
                    if j == i:
                        # Everything on one line
                        # Extract fields before the `})) = `
                        fields_end = lines[j].rfind('})) =')
                        fields_text = full_pattern[:fields_end - len(rest_of_fields) + len(full_pattern)] if j == i else full_pattern

                        # Get the expression and else parts
                        expr_and_rest = close_match.group(0)
                        expr_text = re.sub(r'^\}\)\)\s*=\s*', '', expr_and_rest).rstrip()
                        is_else = 'else' in expr_and_rest

                        # Build the two let statements
                        # First: let Variant(inner) = expr [else { ... }]
                        if is_else:
                            expr_clean = re.sub(r'\s+else\s*\{$', '', expr_text)
                            new_lines.append(f'{indent}let {prefix}{variant}(inner) = {expr_clean} else {{')
                        else:
                            new_lines.append(f'{indent}let {prefix}{variant}(inner) = {expr_text}')

                        # Need to collect the else block if present
                        if is_else:
                            # Collect until matching }
                            j += 1
                            brace_count = 1
                            while j < len(lines) and brace_count > 0:
                                new_lines.append(lines[j])
                                brace_count += lines[j].count('{') - lines[j].count('}')
                                j += 1
                        else:
                            j += 1

                        # Second: let Struct { fields.. } = &**inner;
                        new_lines.append(f'{indent}let {struct_name} {{ {full_pattern.rstrip().rstrip("}")} }} = &**inner;')

                        changes += 1
                        i = j
                        break
                    else:
                        # Multi-line case - collect all fields
                        full_pattern += '\n' + lines[j]

                        # Similar extraction but for multi-line
                        # This is complex, skip for now and handle manually
                        break
                else:
                    if j > i:
                        full_pattern += '\n' + lines[j]
                    j += 1
                    if j >= len(lines):
                        break

            if j >= len(lines) or (changes == 0 and j > i):
                # Couldn't fix this one, just add the original line
                new_lines.append(line)
                i += 1
        else:
            new_lines.append(line)
            i += 1

    if changes > 0:
        with open(filepath, 'w') as f:
            f.write('\n'.join(new_lines))
        print(f"Fixed {changes} Box::new in pattern position in {filepath}")
        return True
    return False


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: fix_boxing2.py <command> [files...]")
        print("Commands:")
        print("  e0164 <file>  - Fix Box::new in pattern position")
        print("  constructor <file> - Fix constructor calls")
    elif sys.argv[1] == 'e0164':
        for f in sys.argv[2:]:
            fix_e0164_box_in_pattern(f)
    elif sys.argv[1] == 'constructor':
        for f in sys.argv[2:]:
            fix_constructor_calls(f)
