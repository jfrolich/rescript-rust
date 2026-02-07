#!/usr/bin/env python3
"""
Fix boxing of AST enum variants across all .rs files.

Two-phase approach (SEPARATE PASSES):
Phase 1: Fix ALL construction sites across ALL variants first
Phase 2: Fix ALL pattern match sites

For struct variants (Pexp_fun, Pexp_apply, Ptyp_arrow):
1. Construction: Variant { f: v, ... } -> Variant(Box::new(Struct { f: v, ... }))
2. Pattern: Variant { f1, f2, .. } => body -> Variant(inner) => { let Struct { f1, f2, .. } = *inner; body }
"""

import re
import os
import sys
from pathlib import Path

SRC_DIR = Path("/Users/jaapf/conductor/workspaces/rescript/manado/compiler-rust/src")
SKIP_FILES = {"ast.rs"}

# ===========================================================================
# Configuration: all variants that need Box wrapping
# ===========================================================================

# Single-arg variants that just need Box::new() wrapping in construction
# Pattern matching is unaffected (the binding is already a single value)
SINGLE_BOX = {
    "Pexp_constant", "Pexp_tuple", "Pexp_array", "Pexp_pack",
    "Pexp_extension", "Pexp_jsx_element",
    "Ppat_constant", "Ppat_tuple", "Ppat_array", "Ppat_extension",
    "Ptyp_var", "Ptyp_tuple", "Ptyp_package", "Ptyp_extension",
    "Pstr_primitive", "Pstr_typext", "Pstr_exception", "Pstr_module",
    "Pstr_recmodule", "Pstr_modtype", "Pstr_open", "Pstr_include",
    "Pstr_attribute",
    "Psig_value", "Psig_typext", "Psig_exception", "Psig_module",
    "Psig_recmodule", "Psig_modtype", "Psig_open", "Psig_include",
    "Psig_attribute",
    "Pmod_structure", "Pmod_extension",
    "Pmty_signature", "Pmty_extension",
    "PStr", "PSig",
}

# Multi-arg tuple variants: Variant(a, b, ...) -> Variant(Box<(A, B, ...)>)
MULTI_BOX = {
    "Pexp_let": 3, "Pexp_match": 2, "Pexp_try": 2,
    "Pexp_variant": 2, "Pexp_record": 2,
    "Pexp_setfield": 3, "Pexp_ifthenelse": 3,
    "Pexp_for": 5, "Pexp_constraint": 2, "Pexp_coerce": 3,
    "Pexp_send": 2, "Pexp_letmodule": 3, "Pexp_letexception": 2,
    "Pexp_newtype": 2, "Pexp_open": 3,
    "Ppat_interval": 2, "Ppat_variant": 2, "Ppat_record": 2,
    "Ppat_constraint": 2,
    "Ptyp_constr": 2, "Ptyp_object": 2, "Ptyp_alias": 2,
    "Ptyp_variant": 3, "Ptyp_poly": 2,
    "Pstr_eval": 2, "Pstr_value": 2, "Pstr_type": 2, "Pstr_extension": 2,
    "Psig_type": 2, "Psig_extension": 2,
    "Pmod_functor": 3,
    "Pmty_functor": 3, "Pmty_with": 2,
    "PPat": 2,
}

# Struct variants -> Box<NamedStruct>
STRUCT_BOX = {
    "Pexp_fun": "PexpFun",
    "Pexp_apply": "PexpApply",
}

# Ptyp_arrow struct variant -> Box<(arg, ret, arity)> tuple
PTYP_ARROW = "Ptyp_arrow"
PTYP_ARROW_FIELDS = ["arg", "ret", "arity"]


def find_rs_files():
    files = []
    for path in SRC_DIR.rglob("*.rs"):
        if path.name not in SKIP_FILES:
            files.append(path)
    return sorted(files)


def find_matching_delim(text, start, open_ch, close_ch):
    """Find matching closing delimiter, handling nesting and string/char literals."""
    depth = 0
    i = start
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return i
        elif ch == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == '\\':
                    i += 1
                i += 1
        elif ch == '/' and i + 1 < n and text[i + 1] == '/':
            # Skip line comments
            while i < n and text[i] != '\n':
                i += 1
        i += 1
    return -1


def count_top_level_commas(text):
    """Count commas at the top nesting level."""
    depth = 0
    commas = 0
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        elif ch == ',' and depth == 0:
            commas += 1
        elif ch == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == '\\':
                    i += 1
                i += 1
        i += 1
    return commas


def split_top_level(text, sep=','):
    """Split text at top-level separators (not inside nested delimiters)."""
    parts = []
    depth = 0
    current = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in '([{':
            depth += 1
            current.append(ch)
        elif ch in ')]}':
            depth -= 1
            current.append(ch)
        elif ch == sep and depth == 0:
            parts.append(''.join(current))
            current = []
        elif ch == '"':
            current.append(ch)
            i += 1
            while i < n and text[i] != '"':
                if text[i] == '\\':
                    current.append(text[i])
                    i += 1
                current.append(text[i])
                i += 1
            if i < n:
                current.append(text[i])
        else:
            current.append(ch)
        i += 1
    if current:
        parts.append(''.join(current))
    return parts


def is_word_boundary_before(text, pos):
    """Check if position is preceded by a word boundary (not an ident char).
    Note: '::' (Rust path separator) IS a valid boundary for our variants."""
    if pos == 0:
        return True
    ch = text[pos - 1]
    # Allow ':' as a word boundary since Rust uses :: to qualify enum variants
    return not (ch.isalnum() or ch == '_')


def looks_like_match_pattern(content, paren_end):
    """Check if what follows the close paren looks like a match arm pattern.
    Returns True if followed by '=>', 'if guard =>', '|', or ',' (or-pattern)."""
    rest = content[paren_end + 1:].lstrip()
    return (rest.startswith('=>') or
            rest.startswith('if ') or
            rest.startswith('| ') or
            rest.startswith('|\n') or
            rest.startswith(','))  # multi-line match patterns


def looks_like_let_else(content, pos):
    """Check if this is a `let Variant(a, b) = expr else {` pattern."""
    # Search backwards for 'let'
    before = content[max(0, pos - 100):pos].rstrip()
    return before.endswith('let') or 'let ' in before[-30:]


def find_arm_body_end(text, pos):
    """Find the end of a match arm body."""
    i = pos
    n = len(text)
    while i < n and text[i] in ' \t\n\r':
        i += 1
    if i >= n:
        return n
    if text[i] == '{':
        end = find_matching_delim(text, i, '{', '}')
        return end + 1 if end != -1 else n
    else:
        depth_paren = 0
        depth_brace = 0
        depth_bracket = 0
        while i < n:
            ch = text[i]
            if ch == '(':
                depth_paren += 1
            elif ch == ')':
                depth_paren -= 1
            elif ch == '{':
                depth_brace += 1
            elif ch == '}':
                if depth_brace == 0:
                    return i
                depth_brace -= 1
            elif ch == '[':
                depth_bracket += 1
            elif ch == ']':
                depth_bracket -= 1
            elif ch == '"':
                i += 1
                while i < n and text[i] != '"':
                    if text[i] == '\\':
                        i += 1
                    i += 1
            i += 1
        return n


def process_file(filepath):
    """Process one .rs file with proper ordering."""
    with open(filepath) as f:
        content = f.read()

    original = content

    # Phase 1: Fix struct variants (Pexp_fun, Pexp_apply) - both construction and pattern
    for variant, struct_name in STRUCT_BOX.items():
        content = fix_struct_construction(content, variant, struct_name)
    content = fix_ptyp_arrow_construction(content)

    # Phase 2: Fix ALL single-box constructions
    for variant in SINGLE_BOX:
        content = fix_single_box_construction(content, variant)

    # Phase 3: Fix ALL multi-box constructions (construction ONLY)
    for variant, nargs in MULTI_BOX.items():
        content = fix_multi_box_construction(content, variant, nargs)

    # Phase 4: Fix ALL multi-box patterns (patterns ONLY, AFTER all constructions fixed)
    for variant, nargs in MULTI_BOX.items():
        content = fix_multi_box_pattern(content, variant, nargs)

    # Phase 5: Fix struct variant patterns
    for variant, struct_name in STRUCT_BOX.items():
        content = fix_struct_pattern(content, variant, struct_name)
    content = fix_ptyp_arrow_pattern(content)

    if content != original:
        with open(filepath, 'w') as f:
            f.write(content)
        return True
    return False


def fix_single_box_construction(content, variant):
    """Variant(x) -> Variant(Box::new(x)) for construction only.
    Pattern matching stays same (x is now Box<T>)."""
    result = []
    i = 0
    pat = variant + '('

    while i < len(content):
        pos = content.find(pat, i)
        if pos == -1:
            result.append(content[i:])
            break

        if not is_word_boundary_before(content, pos):
            result.append(content[i:pos + len(variant)])
            i = pos + len(variant)
            continue

        result.append(content[i:pos])
        paren_start = pos + len(pat) - 1
        paren_end = find_matching_delim(content, paren_start, '(', ')')
        if paren_end == -1:
            result.append(content[pos:])
            break

        inner = content[paren_start + 1:paren_end]

        # Already boxed?
        if inner.lstrip().startswith('Box::new('):
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # Match pattern? Keep as-is
        if looks_like_match_pattern(content, paren_end):
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # let-else pattern? Keep as-is
        if looks_like_let_else(content, pos):
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # In `matches!()` macro? Keep as-is
        if is_in_matches_macro(content, pos):
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # Construction: wrap with Box::new
        result.append(f'{variant}(Box::new({inner}))')
        i = paren_end + 1

    return ''.join(result)


def is_in_matches_macro(content, pos):
    """Check if position is inside a matches!() macro invocation."""
    # Search backwards for 'matches!'
    before = content[max(0, pos - 200):pos]
    # Find last 'matches!' before our pos
    idx = before.rfind('matches!')
    if idx == -1:
        return False
    # Check that we're inside the macro's parens
    after_matches = before[idx + len('matches!'):]
    depth = 0
    for ch in after_matches:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return False  # Macro closed before our position
    return depth > 0  # Still inside macro


def fix_multi_box_construction(content, variant, nargs):
    """Fix construction sites ONLY for multi-arg variants.
    Variant(a, b, c) -> Variant(Box::new((a, b, c)))"""
    result = []
    i = 0
    pat = variant + '('

    while i < len(content):
        pos = content.find(pat, i)
        if pos == -1:
            result.append(content[i:])
            break

        if not is_word_boundary_before(content, pos):
            result.append(content[i:pos + len(variant)])
            i = pos + len(variant)
            continue

        result.append(content[i:pos])
        paren_start = pos + len(pat) - 1
        paren_end = find_matching_delim(content, paren_start, '(', ')')
        if paren_end == -1:
            result.append(content[pos:])
            break

        inner = content[paren_start + 1:paren_end]
        commas = count_top_level_commas(inner)

        # Already boxed?
        if inner.lstrip().startswith('Box::new('):
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        if commas == nargs - 1:
            # Has the right number of args
            if looks_like_match_pattern(content, paren_end):
                # Pattern site — skip (handled in phase 4)
                result.append(content[pos:paren_end + 1])
                i = paren_end + 1
                continue

            if looks_like_let_else(content, pos):
                # let-else pattern — skip
                result.append(content[pos:paren_end + 1])
                i = paren_end + 1
                continue

            if is_in_matches_macro(content, pos):
                # matches! macro — skip
                result.append(content[pos:paren_end + 1])
                i = paren_end + 1
                continue

            # CONSTRUCTION: wrap with Box::new((inner))
            result.append(f'{variant}(Box::new(({inner})))')
            i = paren_end + 1
        else:
            # Wrong number of args (could be single-arg already, wildcard, or inner binding)
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1

    return ''.join(result)


def fix_multi_box_pattern(content, variant, nargs):
    """Fix pattern match sites ONLY for multi-arg variants.
    Pattern: Variant(a, b, c) => body -> Variant(inner) => { let (a, b, c) = *inner; body }

    This runs AFTER all constructions have been fixed, so any variant constructions
    in the body already have Box::new((...)) wrapping.
    """
    result = []
    i = 0
    pat = variant + '('

    while i < len(content):
        pos = content.find(pat, i)
        if pos == -1:
            result.append(content[i:])
            break

        if not is_word_boundary_before(content, pos):
            result.append(content[i:pos + len(variant)])
            i = pos + len(variant)
            continue

        result.append(content[i:pos])
        paren_start = pos + len(pat) - 1
        paren_end = find_matching_delim(content, paren_start, '(', ')')
        if paren_end == -1:
            result.append(content[pos:])
            break

        inner = content[paren_start + 1:paren_end]
        commas = count_top_level_commas(inner)

        # Already single-arg (boxed or inner binding)
        if commas == 0:
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        if commas != nargs - 1:
            # Wrong count, keep as-is
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # Check if this is a pattern match site
        if not looks_like_match_pattern(content, paren_end):
            # Not a pattern (might be a construction that wasn't caught earlier)
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # Also handle let-else patterns
        if looks_like_let_else(content, pos):
            # let Variant(a, b, c) = expr else { ... }
            # -> let Variant(inner) = expr else { ... }; let (a, b, c) = *inner;
            # Actually this is complex - skip for manual fixing
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # PATTERN: Variant(a, b, c) => body
        rest = content[paren_end + 1:]
        stripped = rest.lstrip()

        # Handle optional `if guard` before =>
        guard_text = ""
        if stripped.startswith('if '):
            arrow_pos = stripped.find('=>')
            if arrow_pos != -1:
                guard_text = stripped[:arrow_pos]
                rest_after_arrow = stripped[arrow_pos + 2:]
            else:
                result.append(content[pos:paren_end + 1])
                i = paren_end + 1
                continue
        elif stripped.startswith('=>'):
            rest_after_arrow = stripped[2:]
        elif stripped.startswith('|') or stripped.startswith(','):
            # Or-pattern or tuple, keep as-is
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue
        else:
            result.append(content[pos:paren_end + 1])
            i = paren_end + 1
            continue

        # Calculate absolute position after =>
        whitespace_before = len(rest) - len(stripped)
        if guard_text:
            arrow_offset = paren_end + 1 + whitespace_before + len(guard_text) + 2
        else:
            arrow_offset = paren_end + 1 + whitespace_before + 2

        body_text = rest_after_arrow.lstrip()

        # Build the pattern variable list
        parts = split_top_level(inner.strip())
        pat_vars = ', '.join(p.strip() for p in parts)

        if body_text.startswith('{'):
            # Body is already braced
            brace_start_abs = arrow_offset + (len(rest_after_arrow) - len(body_text))
            brace_end_abs = find_matching_delim(content, brace_start_abs, '{', '}')
            if brace_end_abs == -1:
                result.append(content[pos:paren_end + 1])
                i = paren_end + 1
                continue

            brace_body = content[brace_start_abs + 1:brace_end_abs]
            if guard_text:
                result.append(f'{variant}(inner) {guard_text}=> {{\n                    let ({pat_vars}) = *inner;{brace_body}}}')
            else:
                result.append(f'{variant}(inner) => {{\n                    let ({pat_vars}) = *inner;{brace_body}}}')
            i = brace_end_abs + 1
        else:
            # Body is not braced
            body_abs_start = arrow_offset + (len(rest_after_arrow) - len(body_text))
            arm_end = find_arm_body_end(content, body_abs_start)
            arm_body = content[body_abs_start:arm_end]

            if guard_text:
                result.append(f'{variant}(inner) {guard_text}=> {{\n                    let ({pat_vars}) = *inner;\n                    {arm_body.strip()}\n                }}')
            else:
                result.append(f'{variant}(inner) => {{\n                    let ({pat_vars}) = *inner;\n                    {arm_body.strip()}\n                }}')
            i = arm_end

    return ''.join(result)


def fix_struct_construction(content, variant, struct_name):
    """Handle struct variant construction: Variant { f: v } -> Variant(Box::new(Struct { f: v }))"""
    result = []
    i = 0
    pat_re = re.compile(r'(?<![a-zA-Z0-9_])' + re.escape(variant) + r'\s*\{')

    while i < len(content):
        m = pat_re.search(content, i)
        if m is None:
            result.append(content[i:])
            break

        result.append(content[i:m.start()])
        brace_start = content.index('{', m.start() + len(variant))
        brace_end = find_matching_delim(content, brace_start, '{', '}')

        if brace_end == -1:
            result.append(content[m.start():])
            break

        inner = content[brace_start:brace_end + 1]

        if looks_like_match_pattern(content, brace_end):
            # Pattern site — skip (handled in phase 5)
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
        elif is_in_matches_macro(content, m.start()):
            # matches! macro — skip
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
        else:
            # Construction: Variant { f: v } -> Variant(Box::new(Struct { f: v }))
            result.append(f'{variant}(Box::new({struct_name} {inner}))')
            i = brace_end + 1

    return ''.join(result)


def fix_struct_pattern(content, variant, struct_name):
    """Handle struct variant pattern: Variant { f1, f2 } => body -> Variant(inner) => { let Struct { f1, f2 } = *inner; body }"""
    result = []
    i = 0
    pat_re = re.compile(r'(?<![a-zA-Z0-9_])' + re.escape(variant) + r'\s*\{')

    while i < len(content):
        m = pat_re.search(content, i)
        if m is None:
            result.append(content[i:])
            break

        result.append(content[i:m.start()])
        brace_start = content.index('{', m.start() + len(variant))
        brace_end = find_matching_delim(content, brace_start, '{', '}')

        if brace_end == -1:
            result.append(content[m.start():])
            break

        if not looks_like_match_pattern(content, brace_end):
            # Not a pattern (construction should already be handled)
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
            continue

        # Pattern: Variant { f1, f2, .. } => body
        rest = content[brace_end + 1:]
        stripped = rest.lstrip()

        if stripped.startswith('=>'):
            rest_after_arrow = stripped[2:]
            arrow_offset = brace_end + 1 + (len(rest) - len(stripped)) + 2

            body_text = rest_after_arrow.lstrip()
            field_inner = content[brace_start + 1:brace_end].strip()

            if body_text.startswith('{'):
                brace_start_abs = arrow_offset + (len(rest_after_arrow) - len(body_text))
                brace_end_abs = find_matching_delim(content, brace_start_abs, '{', '}')
                if brace_end_abs == -1:
                    result.append(content[m.start():brace_end + 1])
                    i = brace_end + 1
                    continue

                brace_body = content[brace_start_abs + 1:brace_end_abs]
                result.append(f'{variant}(inner) => {{\n                    let {struct_name} {{ {field_inner} }} = *inner;{brace_body}}}')
                i = brace_end_abs + 1
            else:
                body_abs_start = arrow_offset + (len(rest_after_arrow) - len(body_text))
                arm_end = find_arm_body_end(content, body_abs_start)
                arm_body = content[body_abs_start:arm_end]
                result.append(f'{variant}(inner) => {{\n                    let {struct_name} {{ {field_inner} }} = *inner;\n                    {arm_body.strip()}\n                }}')
                i = arm_end
        else:
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1

    return ''.join(result)


def fix_ptyp_arrow_construction(content):
    """Handle Ptyp_arrow struct variant -> Box<(arg, ret, arity)> construction."""
    result = []
    i = 0
    variant = "Ptyp_arrow"
    pat_re = re.compile(r'(?<![a-zA-Z0-9_])' + re.escape(variant) + r'\s*\{')

    while i < len(content):
        m = pat_re.search(content, i)
        if m is None:
            result.append(content[i:])
            break

        result.append(content[i:m.start()])
        brace_start = content.index('{', m.start() + len(variant))
        brace_end = find_matching_delim(content, brace_start, '{', '}')

        if brace_end == -1:
            result.append(content[m.start():])
            break

        if looks_like_match_pattern(content, brace_end):
            # Pattern — skip (handled in fix_ptyp_arrow_pattern)
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
            continue

        if is_in_matches_macro(content, m.start()):
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
            continue

        inner_text = content[brace_start + 1:brace_end].strip()

        # Construction: Ptyp_arrow { arg: x, ret: y, arity: z }
        # -> Ptyp_arrow(Box::new((x, y, z)))
        field_vals = {}
        for part in split_top_level(inner_text):
            part = part.strip()
            if ':' in part:
                colon_pos = part.index(':')
                fname = part[:colon_pos].strip()
                fval = part[colon_pos + 1:].strip()
                field_vals[fname] = fval
            elif part:
                field_vals[part] = part

        if all(f in field_vals for f in PTYP_ARROW_FIELDS):
            args = ', '.join(field_vals[f] for f in PTYP_ARROW_FIELDS)
            result.append(f'{variant}(Box::new(({args})))')
        else:
            result.append(content[m.start():brace_end + 1])
        i = brace_end + 1

    return ''.join(result)


def fix_ptyp_arrow_pattern(content):
    """Handle Ptyp_arrow struct variant pattern."""
    result = []
    i = 0
    variant = "Ptyp_arrow"
    pat_re = re.compile(r'(?<![a-zA-Z0-9_])' + re.escape(variant) + r'\s*\{')

    while i < len(content):
        m = pat_re.search(content, i)
        if m is None:
            result.append(content[i:])
            break

        result.append(content[i:m.start()])
        brace_start = content.index('{', m.start() + len(variant))
        brace_end = find_matching_delim(content, brace_start, '{', '}')

        if brace_end == -1:
            result.append(content[m.start():])
            break

        if not looks_like_match_pattern(content, brace_end):
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1
            continue

        inner_text = content[brace_start + 1:brace_end].strip()
        rest = content[brace_end + 1:]
        stripped = rest.lstrip()

        if stripped.startswith('=>'):
            rest_after_arrow = stripped[2:]
            arrow_offset = brace_end + 1 + (len(rest) - len(stripped)) + 2
            body_text = rest_after_arrow.lstrip()

            # Extract field names
            field_parts = []
            for part in inner_text.split(','):
                part = part.strip().rstrip(',')
                if ':' in part:
                    field_parts.append(part.split(':')[0].strip())
                elif part.startswith('..'):
                    field_parts.append(part)
                elif part:
                    field_parts.append(part)

            field_str = ', '.join(field_parts)

            if body_text.startswith('{'):
                brace_start_abs = arrow_offset + (len(rest_after_arrow) - len(body_text))
                brace_end_abs = find_matching_delim(content, brace_start_abs, '{', '}')
                if brace_end_abs == -1:
                    result.append(content[m.start():brace_end + 1])
                    i = brace_end + 1
                    continue
                brace_body = content[brace_start_abs + 1:brace_end_abs]
                result.append(f'{variant}(inner) => {{\n                    let ({field_str}) = *inner;{brace_body}}}')
                i = brace_end_abs + 1
            else:
                body_abs_start = arrow_offset + (len(rest_after_arrow) - len(body_text))
                arm_end = find_arm_body_end(content, body_abs_start)
                arm_body = content[body_abs_start:arm_end]
                result.append(f'{variant}(inner) => {{\n                    let ({field_str}) = *inner;\n                    {arm_body.strip()}\n                }}')
                i = arm_end
        else:
            result.append(content[m.start():brace_end + 1])
            i = brace_end + 1

    return ''.join(result)


def main():
    files = find_rs_files()
    print(f"Found {len(files)} .rs files")

    changed = 0
    for f in files:
        if process_file(f):
            changed += 1
            print(f"  Modified: {f.relative_to(SRC_DIR)}")

    print(f"\nModified {changed} files")
    print("\nRun `cargo build --release 2>&1 | grep '^error' | wc -l` to check remaining errors.")


if __name__ == '__main__':
    main()
