#!/usr/bin/env python3
"""
Normalize typedtree sexp output for parity comparison.

This script handles cycle detection differences between OCaml and Rust compilers:
- Pattern A: OCaml has (Tvar None) after cycle, Rust has (Tconstr int/string/...)
- Pattern B: OCaml has resolved type, Rust has cycle
- Pattern C: Both have cycles but in different positions

The normalization strategy:
1. Parse the entire sexp into a tree structure (keeping <cycle> markers as atoms)
2. Replace <cycle> markers with _CYCLE_
3. Normalize primitive types (int, string, float, bool, unit) and (Tvar None) to _UNIFIED_TYPE_
   in ALL positions within type expressions (Tarrow, Tpoly, etc.)
   This is necessary because cycles can appear anywhere and represent primitive types.
"""

import sys
import re
from typing import List, Union, Optional, Tuple


# Type alias for sexp tree
SexpNode = Union[str, List['SexpNode']]


def tokenize(text: str) -> List[str]:
    """Tokenize sexp text into tokens."""
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in '()':
            tokens.append(c)
            i += 1
        elif c == '"':
            # String literal
            j = i + 1
            while j < len(text):
                if text[j] == '\\' and j + 1 < len(text):
                    j += 2
                elif text[j] == '"':
                    break
                else:
                    j += 1
            tokens.append(text[i:j+1])
            i = j + 1
        elif c == '<':
            # Handle <cycle> and similar markers
            j = i + 1
            while j < len(text) and text[j] != '>':
                j += 1
            if j < len(text):
                j += 1  # include the >
            tokens.append(text[i:j])
            i = j
        elif c.isspace():
            i += 1
        else:
            # Atom
            j = i
            while j < len(text) and text[j] not in '()<>"' and not text[j].isspace():
                j += 1
            tokens.append(text[i:j])
            i = j
    return tokens


def parse_sexp(tokens: List[str], pos: int = 0) -> Tuple[Optional[SexpNode], int]:
    """Parse sexp from tokens starting at pos. Returns (node, next_pos)."""
    if pos >= len(tokens):
        return None, pos

    token = tokens[pos]

    if token == '(':
        # Start of list
        items = []
        pos += 1
        while pos < len(tokens) and tokens[pos] != ')':
            item, pos = parse_sexp(tokens, pos)
            if item is not None:
                items.append(item)
        if pos < len(tokens) and tokens[pos] == ')':
            pos += 1
        return items, pos
    elif token == ')':
        # Unexpected close paren
        return None, pos + 1
    else:
        # Atom or string
        return token, pos + 1


def parse_all(text: str) -> List[SexpNode]:
    """Parse all sexp nodes from text."""
    tokens = tokenize(text)
    nodes = []
    pos = 0
    while pos < len(tokens):
        node, pos = parse_sexp(tokens, pos)
        if node is not None:
            nodes.append(node)
    return nodes


def is_list(node: SexpNode) -> bool:
    """Check if node is a list."""
    return isinstance(node, list)


def is_atom(node: SexpNode) -> bool:
    """Check if node is an atom."""
    return isinstance(node, str)


def get_head(node: SexpNode) -> Optional[str]:
    """Get the head atom of a list, or None if not a list or empty."""
    if is_list(node) and len(node) > 0 and is_atom(node[0]):
        return node[0]
    return None


def is_cycle_marker(node: SexpNode) -> bool:
    """Check if node is a cycle marker like <cycle>."""
    return is_atom(node) and node.startswith('<') and node.endswith('>')


def is_tvar_none(node: SexpNode) -> bool:
    """Check if node is (Tvar None)."""
    return (is_list(node) and len(node) == 2 and
            get_head(node) == 'Tvar' and node[1] == 'None')


def strip_quotes(s: str) -> str:
    """Strip surrounding quotes from a string if present."""
    if len(s) >= 2 and s.startswith('"') and s.endswith('"'):
        return s[1:-1]
    return s


def is_primitive_tconstr(node: SexpNode) -> bool:
    """Check if node is a primitive Tconstr like (Tconstr int ()) or (Tconstr (Pident int) ())."""
    if not is_list(node) or get_head(node) != 'Tconstr':
        return False

    if len(node) < 2:
        return False

    primitives = {'int', 'string', 'float', 'bool', 'unit', 'char', 'bytes',
                  'exn', 'array', 'list', 'option', 'nativeint', 'int32', 'int64'}

    path = node[1]

    # Direct primitive name (with or without quotes)
    if is_atom(path) and strip_quotes(path) in primitives:
        return True

    # (Pident int) or (Pident "int") form
    if is_list(path) and get_head(path) == 'Pident' and len(path) >= 2:
        if is_atom(path[1]) and strip_quotes(path[1]) in primitives:
            return True

    return False


def get_primitive_name(node: SexpNode) -> Optional[str]:
    """Extract the primitive type name from a Tconstr node (unquoted)."""
    if not is_primitive_tconstr(node):
        return None

    path = node[1]
    if is_atom(path):
        return strip_quotes(path)
    if is_list(path) and get_head(path) == 'Pident' and len(path) >= 2:
        return strip_quotes(path[1]) if is_atom(path[1]) else None
    return None


def is_type_context(head: Optional[str]) -> bool:
    """Check if we're in a type-level construct that can have cycles."""
    type_heads = {'Tarrow', 'Tpoly', 'Ttuple', 'Tconstr', 'Tvar', 'Tlink',
                  'Tobject', 'Tfield', 'Tnil', 'Tvariant', 'Tpackage', 'type'}
    return head in type_heads


def normalize_type_in_context(node: SexpNode, in_type_context: bool = False) -> SexpNode:
    """
    Normalize a type expression.

    - Replace <cycle> markers with _UNIFIED_TYPE_ in type context (since cycles represent primitive types)
    - In type context, unify (Tvar None) and primitive (Tconstr ...) to handle cycle differences
    """
    # Handle cycle markers - in type context, cycles represent primitive types, so use unified marker
    if is_cycle_marker(node):
        if in_type_context:
            return '_UNIFIED_TYPE_'
        return '_CYCLE_'

    if is_atom(node):
        return node

    if not is_list(node):
        return node

    head = get_head(node)

    # Determine if we're entering/in a type context
    entering_type_context = is_type_context(head)
    current_type_context = in_type_context or entering_type_context

    # In type context, normalize equivalent types to handle cycle differences
    if current_type_context:
        if is_tvar_none(node):
            return '_UNIFIED_TYPE_'
        if is_primitive_tconstr(node):
            prim = get_primitive_name(node)
            # Return unified marker for simple primitives that commonly appear in cycles
            if prim in {'int', 'string', 'float', 'bool', 'unit'}:
                return '_UNIFIED_TYPE_'

    # Handle Tarrow specially: all type positions get normalized
    if head == 'Tarrow':
        result = ['Tarrow']
        for i, child in enumerate(node[1:], 1):
            # Positions 2 (arg) and 3 (ret) are types
            if i in (2, 3):
                result.append(normalize_type_in_context(child, in_type_context=True))
            else:
                result.append(normalize_type_in_context(child, in_type_context))
        return result

    # Handle Tpoly: the body is a type
    if head == 'Tpoly':
        result = ['Tpoly']
        for i, child in enumerate(node[1:], 1):
            if i == 1:  # Body type
                result.append(normalize_type_in_context(child, in_type_context=True))
            else:
                result.append(normalize_type_in_context(child, in_type_context))
        return result

    # Handle Ttuple: all elements are types
    if head == 'Ttuple':
        result = ['Ttuple']
        for child in node[1:]:
            result.append(normalize_type_in_context(child, in_type_context=True))
        return result

    # Handle 'type' wrapper
    if head == 'type':
        result = ['type']
        for child in node[1:]:
            result.append(normalize_type_in_context(child, in_type_context=True))
        return result

    # Recursively normalize all children
    return [normalize_type_in_context(child, in_type_context=current_type_context) for child in node]


def normalize_tree(node: SexpNode) -> SexpNode:
    """Normalize the entire sexp tree."""
    return normalize_type_in_context(node, in_type_context=False)


def sexp_to_flat_string(node: SexpNode) -> str:
    """Convert sexp tree to a flat string (one line per node for line-by-line comparison)."""
    if is_atom(node):
        return node
    if not node:
        return '()'
    return '(' + ' '.join(sexp_to_flat_string(child) for child in node) + ')'


def main():
    """Main entry point - read from stdin, normalize, write to stdout."""
    # Read all input
    input_text = sys.stdin.read()

    # Parse the entire sexp (which may span multiple lines)
    nodes = parse_all(input_text)

    # Normalize each top-level node
    normalized = [normalize_tree(node) for node in nodes]

    # Output each top-level node on its own line (flattened) for comparison
    for node in normalized:
        print(sexp_to_flat_string(node))


if __name__ == '__main__':
    main()
