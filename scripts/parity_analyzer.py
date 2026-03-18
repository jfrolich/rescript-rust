#!/usr/bin/env python3
"""Parity analyzer for ReScript Rust compiler typed tree output.

Analyzes differences between OCaml and Rust compiler sexp output to help
reach 100% parity. Works with files in .parity-cache/tests/.

Commands:
    summary              Overview of all failures
    motifs               Hunk-level motif classification across diffs
    preamble <file>      Aligned type preamble comparison
    trace <file> <id>    Trace a type through both compilers
    extra <file>         Find extra/missing type nodes
    sharing <file>       Copy-sharing imbalance analysis
    sharing-summary      Aggregate sharing imbalances across failing files
    divergence <file>    First divergence analysis
    insertion [file]     First insertion/resync analysis
"""

import argparse
from collections import Counter
import os
import re
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Union

# ─── Colors ───────────────────────────────────────────────────────────────────

USE_COLOR = True

def _c(code: str, text: str) -> str:
    if not USE_COLOR:
        return text
    return f"\033[{code}m{text}\033[0m"

def green(t: str) -> str: return _c("32", t)
def red(t: str) -> str: return _c("31", t)
def yellow(t: str) -> str: return _c("33", t)
def cyan(t: str) -> str: return _c("36", t)
def bold(t: str) -> str: return _c("1", t)
def dim(t: str) -> str: return _c("2", t)

# ─── Sexp Parser ──────────────────────────────────────────────────────────────

@dataclass
class SexpAtom:
    value: str

    def __repr__(self):
        return self.value

    def pretty(self, indent=0):
        return self.value

@dataclass
class SexpList:
    children: list

    def __repr__(self):
        inner = " ".join(repr(c) for c in self.children)
        return f"({inner})"

    def pretty(self, indent=0):
        if not self.children:
            return "()"
        if len(self.children) <= 3 and all(isinstance(c, SexpAtom) for c in self.children):
            return "(" + " ".join(c.value for c in self.children) + ")"
        lines = ["("]
        for c in self.children:
            lines.append("  " + c.pretty(indent + 2))
        lines.append(")")
        return ("\n" + " " * indent).join(lines)


SexpNode = Union[SexpAtom, SexpList]


def tokenize_sexp(text: str) -> list[str]:
    """Tokenize sexp text into tokens: (, ), quoted strings, bare atoms."""
    tokens = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in ' \t\n\r':
            i += 1
        elif c == '(':
            tokens.append('(')
            i += 1
        elif c == ')':
            tokens.append(')')
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '\\':
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            tokens.append(text[i:j])
            i = j
        else:
            j = i
            while j < n and text[j] not in ' \t\n\r()':
                j += 1
            tokens.append(text[i:j])
            i = j
    return tokens


def parse_sexp_file(text: str) -> List[SexpNode]:
    """Parse all top-level sexp forms from text using an iterative stack-based parser."""
    tokens = tokenize_sexp(text)
    # Iterative parser to avoid Python recursion overhead
    stack = [[]]  # stack of children lists; stack[0] = top-level results
    for tok in tokens:
        if tok == '(':
            stack.append([])
        elif tok == ')':
            children = stack.pop()
            stack[-1].append(SexpList(children))
        else:
            stack[-1].append(SexpAtom(tok))
    return stack[0]


# ─── SexpFile ─────────────────────────────────────────────────────────────────

@dataclass
class SexpFile:
    """Parsed sexp file with types preamble and structure."""
    types: dict[int, SexpNode]  # type_id -> type definition
    structure: Optional[SexpNode]
    raw_nodes: list[SexpNode]

    @staticmethod
    def parse(text: str) -> 'SexpFile':
        nodes = parse_sexp_file(text)
        types = {}
        structure = None

        for node in nodes:
            if isinstance(node, SexpList) and node.children:
                head = node.children[0]
                if isinstance(head, SexpAtom) and head.value == "types":
                    # Parse type entries: (id (Tvar ...))
                    for child in node.children[1:]:
                        if isinstance(child, SexpList) and len(child.children) >= 2:
                            id_node = child.children[0]
                            if isinstance(id_node, SexpAtom):
                                try:
                                    tid = int(id_node.value)
                                    type_body = child.children[1] if len(child.children) == 2 else SexpList(child.children[1:])
                                    types[tid] = type_body
                                except ValueError:
                                    pass
                elif isinstance(head, SexpAtom) and head.value == "structure":
                    structure = node

        return SexpFile(types=types, structure=structure, raw_nodes=nodes)


# ─── Content-Based Type Matching ──────────────────────────────────────────────

def sexp_to_str(node: SexpNode) -> str:
    """Convert sexp node to compact string form."""
    if isinstance(node, SexpAtom):
        return node.value
    return "(" + " ".join(sexp_to_str(c) for c in node.children) + ")"


def content_key(type_id: int, types: Dict[int, SexpNode], depth: int = 0,
                memo: Optional[dict] = None) -> str:
    """Recursively expand #N refs to structural content, depth-limited."""
    if memo is None:
        memo = {}
    if type_id in memo:
        return memo[type_id]
    if depth > 3:
        memo[type_id] = f"#{type_id}"
        return f"#{type_id}"
    if type_id not in types:
        memo[type_id] = f"#{type_id}"
        return f"#{type_id}"

    # Mark as in-progress to prevent infinite recursion
    memo[type_id] = f"<cycle:{type_id}>"

    node = types[type_id]
    result = _expand_refs(node, types, depth, memo)
    memo[type_id] = result
    return result


def _expand_refs(node: SexpNode, types: Dict[int, SexpNode], depth: int,
                 memo: dict) -> str:
    """Expand all #N references in a node."""
    if isinstance(node, SexpAtom):
        m = re.match(r'^#(\d+)$', node.value)
        if m:
            ref_id = int(m.group(1))
            return content_key(ref_id, types, depth + 1, memo)
        return node.value
    parts = []
    for c in node.children:
        parts.append(_expand_refs(c, types, depth, memo))
    return "(" + " ".join(parts) + ")"


def type_summary(node: SexpNode) -> str:
    """One-line summary of a type node."""
    if isinstance(node, SexpAtom):
        return node.value
    if not node.children:
        return "()"
    head = node.children[0]
    if isinstance(head, SexpAtom):
        tag = head.value
        if tag == "Tvar":
            if len(node.children) > 1:
                arg = node.children[1]
                if isinstance(arg, SexpList) and arg.children:
                    inner = arg.children[0] if isinstance(arg.children[0], SexpAtom) else arg.children[0]
                    return f"Tvar({sexp_to_str(inner)})"
                return f"Tvar({sexp_to_str(arg)})"
            return "Tvar"
        elif tag == "Tconstr":
            if len(node.children) > 1:
                path = sexp_to_str(node.children[1])
                args = ""
                if len(node.children) > 2:
                    args = " " + sexp_to_str(node.children[2])
                return f"Tconstr({path}{args})"
            return "Tconstr"
        elif tag == "Tarrow":
            return "Tarrow"
        elif tag == "Ttuple":
            refs = [sexp_to_str(c) for c in node.children[1:]]
            return f"Ttuple({', '.join(refs)})"
        elif tag == "Tvariant":
            return "Tvariant"
        elif tag == "Tpoly":
            return "Tpoly"
        elif tag == "Tobject":
            return "Tobject"
        elif tag == "Tpackage":
            return "Tpackage"
        elif tag == "Tfield":
            return "Tfield"
        elif tag == "Tnil":
            return "Tnil"
        else:
            return tag
    return sexp_to_str(node)[:60]


def match_types(ocaml_types: dict[int, SexpNode],
                rust_types: dict[int, SexpNode]) -> list[tuple]:
    """Match types between compilers by content key.

    Returns list of (ocaml_id, rust_id, status) tuples where status is
    MATCH, SHIFTED, EXTRA_OCAML, or EXTRA_RUST.
    """
    # Build content keys
    ocaml_memo: dict = {}
    rust_memo: dict = {}
    ocaml_keys = {}
    rust_keys = {}

    for tid in ocaml_types:
        ocaml_keys[tid] = content_key(tid, ocaml_types, memo=ocaml_memo)
    for tid in rust_types:
        rust_keys[tid] = content_key(tid, rust_types, memo=rust_memo)

    # Group by content key
    ocaml_by_key: dict[str, list[int]] = {}
    rust_by_key: dict[str, list[int]] = {}

    for tid, key in ocaml_keys.items():
        ocaml_by_key.setdefault(key, []).append(tid)
    for tid, key in rust_keys.items():
        rust_by_key.setdefault(key, []).append(tid)

    # Match: prefer same ID, then closest ID
    matched_ocaml = set()
    matched_rust = set()
    matches = []  # (ocaml_id, rust_id, status)

    # First pass: exact ID matches
    all_ids = sorted(set(ocaml_types.keys()) | set(rust_types.keys()))
    for tid in all_ids:
        if tid in ocaml_keys and tid in rust_keys:
            if ocaml_keys[tid] == rust_keys[tid]:
                matches.append((tid, tid, "MATCH"))
                matched_ocaml.add(tid)
                matched_rust.add(tid)

    # Second pass: shifted matches (same content, different ID)
    for key, o_ids in ocaml_by_key.items():
        r_ids = rust_by_key.get(key, [])
        unmatched_o = [i for i in o_ids if i not in matched_ocaml]
        unmatched_r = [i for i in r_ids if i not in matched_rust]

        # Match by proximity
        for oid in unmatched_o:
            if not unmatched_r:
                break
            # Find closest rust ID
            best_r = min(unmatched_r, key=lambda r: abs(r - oid))
            matches.append((oid, best_r, "SHIFTED"))
            matched_ocaml.add(oid)
            matched_rust.add(best_r)
            unmatched_r.remove(best_r)

    # Remaining unmatched
    for tid in sorted(ocaml_types.keys()):
        if tid not in matched_ocaml:
            matches.append((tid, None, "EXTRA_OCAML"))

    for tid in sorted(rust_types.keys()):
        if tid not in matched_rust:
            matches.append((None, tid, "EXTRA_RUST"))

    # Sort by ocaml_id, then rust_id
    matches.sort(key=lambda m: (m[0] if m[0] is not None else 99999,
                                 m[1] if m[1] is not None else 99999))
    return matches


# ─── File Resolution ──────────────────────────────────────────────────────────

def find_project_root() -> str:
    """Find the project root by looking for .parity-cache."""
    d = os.getcwd()
    while d != '/':
        if os.path.isdir(os.path.join(d, '.parity-cache')):
            return d
        d = os.path.dirname(d)
    # Fallback: try common locations
    for candidate in [os.getcwd(), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]:
        if os.path.isdir(os.path.join(candidate, '.parity-cache')):
            return candidate
    return os.getcwd()


def resolve_file(name: str, root: str) -> str:
    """Resolve a short name like 'ticker' to 'tests_tests_src_ticker.res'.

    Returns the base name without extension, matching cache file naming.
    """
    cache_dir = os.path.join(root, '.parity-cache', 'tests')
    diff_dir = os.path.join(cache_dir, 'diffs')

    if not os.path.isdir(diff_dir):
        return name

    # Try exact match first
    for ext in ['.diff', '.sexp']:
        if os.path.exists(os.path.join(diff_dir, name + ext)):
            return name

    # Try with tests_tests_src_ prefix
    prefixed = f"tests_tests_src_{name}.res"
    if os.path.exists(os.path.join(diff_dir, prefixed + '.diff')):
        return prefixed

    # Try stdlib_intl prefix
    prefixed2 = f"tests_tests_src_stdlib_intl_{name}.res"
    if os.path.exists(os.path.join(diff_dir, prefixed2 + '.diff')):
        return prefixed2

    # Fuzzy match: find files containing the name
    matches = []
    for f in os.listdir(diff_dir):
        if f.endswith('.diff'):
            base = f[:-5]  # remove .diff
            if name.lower() in base.lower():
                matches.append(base)

    if len(matches) == 1:
        return matches[0]
    elif len(matches) > 1:
        print(f"Ambiguous name '{name}', matches:")
        for m in sorted(matches):
            print(f"  {m}")
        sys.exit(1)

    return prefixed  # best guess


def get_diff_path(name: str, root: str) -> str:
    return os.path.join(root, '.parity-cache', 'tests', 'diffs', name + '.diff')


def get_sexp_path(compiler: str, name: str, root: str) -> str:
    return os.path.join(root, '.parity-cache', 'tests', compiler, name + '.sexp')


def load_sexp(compiler: str, name: str, root: str) -> Optional[SexpFile]:
    path = get_sexp_path(compiler, name, root)
    if not os.path.exists(path):
        return None
    # Some cached sexp files may include non-UTF8 bytes or partial writes.
    try:
        with open(path, encoding='utf-8', errors='replace') as f:
            return SexpFile.parse(f.read())
    except Exception:
        return None


def require_sexp_files(name: str, root: str) -> tuple[SexpFile, SexpFile]:
    """Load both sexp files, or print error and exit."""
    ocaml = load_sexp('ocaml', name, root)
    rust = load_sexp('rust', name, root)
    missing = []
    if ocaml is None:
        missing.append(get_sexp_path('ocaml', name, root))
    if rust is None:
        missing.append(get_sexp_path('rust', name, root))
    if missing:
        print(red("Missing sexp files:"))
        for m in missing:
            print(f"  {m}")
        print()
        print("Generate them by running the parity test:")
        # Extract short name for the command
        short = name.replace("tests_tests_src_", "").replace(".res", "")
        print(f"  ./scripts/test_typedtree_parity.sh {short}")
        sys.exit(1)
    return ocaml, rust


# ─── Diff Analysis Helpers ────────────────────────────────────────────────────

def count_hunks(diff_text: str) -> int:
    return diff_text.count('\n@@')


def analyze_diff(diff_text: str) -> dict:
    """Analyze a diff file for summary info."""
    hunks = count_hunks(diff_text)
    lines = diff_text.split('\n')

    # Check if diff is in preamble (types section) or structure
    in_types = False
    preamble_hunks = 0
    structure_hunks = 0
    current_in_types = True

    for line in lines:
        if line.startswith('@@'):
            if current_in_types:
                preamble_hunks += 1
            else:
                structure_hunks += 1
        # Track if we've passed the (structure line
        stripped = line.lstrip('+-').lstrip()
        if stripped.startswith('(structure'):
            current_in_types = False

    # Find first actual difference
    first_diff = ""
    for line in lines:
        if line.startswith('-') and not line.startswith('---'):
            first_diff = line[1:].strip()[:60]
            break

    # Categorize
    category = categorize_diff(diff_text)

    return {
        'hunks': hunks,
        'preamble_hunks': preamble_hunks,
        'structure_hunks': structure_hunks,
        'first_diff': first_diff,
        'category': category,
    }


def categorize_diff(diff_text: str) -> str:
    """Categorize the type of difference."""
    lines = diff_text.split('\n')

    has_path_diff = False
    has_id_diff = False
    has_structural = False

    for line in lines:
        if not (line.startswith('+') or line.startswith('-')):
            continue
        if line.startswith('+++') or line.startswith('---'):
            continue
        stripped = line[1:].strip()

        # Check for #N reference diffs
        if re.match(r'^#\d+\)?$', stripped):
            has_id_diff = True
        # Check for path diffs (Pdot, Pident)
        elif 'Pdot' in stripped or 'Pident' in stripped:
            has_path_diff = True
        elif stripped.startswith('(') or stripped.endswith(')'):
            # Could be structural or just reindented
            if any(tag in stripped for tag in ['Tvar', 'Tconstr', 'Tarrow', 'Ttuple', 'Tvariant']):
                has_structural = True
            else:
                has_id_diff = True

    if has_path_diff and has_id_diff:
        return "path+id"
    elif has_path_diff:
        return "path"
    elif has_structural:
        return "structural"
    else:
        return "id-only"


def count_preamble_types(diff_text: str) -> tuple[int, int]:
    """Count types mentioned in OCaml (-) and Rust (+) sides of preamble."""
    ocaml_ids = set()
    rust_ids = set()
    in_preamble = True

    for line in diff_text.split('\n'):
        stripped = line.lstrip('+-').lstrip()
        if stripped.startswith('(structure'):
            in_preamble = False
            continue
        if not in_preamble:
            continue

        # Look for type ID definitions: lines that are just a number
        if line.startswith('-') and not line.startswith('---'):
            content = line[1:].strip()
            if re.match(r'^\d+$', content):
                ocaml_ids.add(int(content))
        elif line.startswith('+') and not line.startswith('+++'):
            content = line[1:].strip()
            if re.match(r'^\d+$', content):
                rust_ids.add(int(content))

    return len(ocaml_ids), len(rust_ids)


# ─── Motif Helpers ───────────────────────────────────────────────────────────

PATH_DOT_RE = re.compile(r'\(Pdot\s+\(Pident\s+"?([^) "]+)"?\)\s+"?([^) "]+)"?\)')
PATH_IDENT_RE = re.compile(r'\(Pident\s+"?([^) "]+)"?\)')
TYPE_ID_RE = re.compile(r'^#\d+$')


def iter_diff_hunks(diff_text: str) -> List[List[str]]:
    """Return unified-diff hunk blocks (each starting with @@ ...)."""
    hunks: List[List[str]] = []
    current: Optional[List[str]] = None

    for line in diff_text.splitlines():
        if line.startswith('@@'):
            if current:
                hunks.append(current)
            current = [line]
        elif current is not None:
            current.append(line)

    if current:
        hunks.append(current)
    return hunks


def _canonicalize_ident_path(ident: str) -> str:
    """Convert flattened alias names to dotted form for rough path matching."""
    return ident.replace('__', '.')


def _canonical_paths_from_text(text: str) -> set[str]:
    paths: set[str] = set()
    for m, label in PATH_DOT_RE.findall(text):
        paths.add(f"{m}.{label}")
    for ident in PATH_IDENT_RE.findall(text):
        paths.add(_canonicalize_ident_path(ident))
    return paths


def _normalize_type_refs(line: str) -> str:
    return re.sub(r'#\d+', '#N', line)


def _extract_path_terms(text: str) -> List[str]:
    """Extract canonicalized path terms from a line/block."""
    terms: List[str] = []
    for m, label in PATH_DOT_RE.findall(text):
        terms.append(f"{m}.{label}")
    for ident in PATH_IDENT_RE.findall(text):
        terms.append(_canonicalize_ident_path(ident))
    return terms


def _extract_path_transitions(minus_lines: List[str], plus_lines: List[str]) -> List[Tuple[str, str]]:
    """Infer path transitions from paired line edits and from set-level diffs."""
    transitions: List[Tuple[str, str]] = []
    seen: set[Tuple[str, str]] = set()

    # Pass 1: pair minus/plus lines at same relative position.
    for m_line, p_line in zip(minus_lines, plus_lines):
        if m_line == p_line:
            continue
        m_terms = [t for t in _extract_path_terms(m_line) if '.' in t]
        p_terms = [t for t in _extract_path_terms(p_line) if '.' in t]
        for src in m_terms:
            src_tail = src.split('.')[-1]
            for dst in p_terms:
                if src == dst or src_tail != dst.split('.')[-1]:
                    continue
                pair = (src, dst)
                if pair not in seen:
                    transitions.append(pair)
                    seen.add(pair)

    # Pass 2: fallback using set differences across the whole hunk.
    minus_paths = _canonical_paths_from_text("\n".join(minus_lines))
    plus_paths = _canonical_paths_from_text("\n".join(plus_lines))
    removed = sorted(minus_paths - plus_paths)
    added = sorted(plus_paths - minus_paths)
    for src in removed:
        src_tail = src.split('.')[-1]
        for dst in added:
            if src == dst or src_tail != dst.split('.')[-1]:
                continue
            pair = (src, dst)
            if pair not in seen:
                transitions.append(pair)
                seen.add(pair)
            break

    return transitions


def _extract_hunk_path_delta(minus_lines: List[str], plus_lines: List[str]) -> tuple[set[str], set[str]]:
    minus_terms = {t for t in _extract_path_terms("\n".join(minus_lines)) if '.' in t}
    plus_terms = {t for t in _extract_path_terms("\n".join(plus_lines)) if '.' in t}
    return minus_terms - plus_terms, plus_terms - minus_terms


def classify_hunk_motifs(hunk_lines: List[str]) -> tuple[set[str], List[Tuple[str, str]]]:
    """Return motif set for a single diff hunk plus inferred path transitions."""
    minus = [line[1:].strip() for line in hunk_lines if line.startswith('-') and not line.startswith('---')]
    plus = [line[1:].strip() for line in hunk_lines if line.startswith('+') and not line.startswith('+++')]
    minus_text = "\n".join(minus)
    plus_text = "\n".join(plus)
    motifs: set[str] = set()

    if not minus and not plus:
        return motifs, []

    minus_has_path = ('Pdot' in minus_text) or ('Pident' in minus_text)
    plus_has_path = ('Pdot' in plus_text) or ('Pident' in plus_text)
    has_path = minus_has_path or plus_has_path
    has_refs = ('#' in minus_text) or ('#' in plus_text)

    minus_flat = {_canonicalize_ident_path(i) for i in PATH_IDENT_RE.findall(minus_text) if '__' in i}
    plus_flat = {_canonicalize_ident_path(i) for i in PATH_IDENT_RE.findall(plus_text) if '__' in i}
    minus_dot = {f"{m}.{label}" for m, label in PATH_DOT_RE.findall(minus_text)}
    plus_dot = {f"{m}.{label}" for m, label in PATH_DOT_RE.findall(plus_text)}

    if (minus_flat & plus_dot) or (plus_flat & minus_dot):
        motifs.add("path_flattened_vs_dotted")

    minus_simple = {i for i in PATH_IDENT_RE.findall(minus_text) if '__' not in i}
    plus_simple = {i for i in PATH_IDENT_RE.findall(plus_text) if '__' not in i}
    minus_dot_tails = {label for _, label in PATH_DOT_RE.findall(minus_text)}
    plus_dot_tails = {label for _, label in PATH_DOT_RE.findall(plus_text)}
    if (minus_dot_tails & plus_simple) or (plus_dot_tails & minus_simple):
        motifs.add("path_qualification_flip")

    transitions = _extract_path_transitions(minus, plus) if has_path else []
    if any(set(src.split('.')) == set(dst.split('.')) and src != dst for src, dst in transitions):
        motifs.add("path_head_reassociation")

    if has_path and has_refs:
        motifs.add("path_plus_id")

    id_norm_matches = 0
    for m_line, p_line in zip(minus, plus):
        if m_line != p_line and _normalize_type_refs(m_line) == _normalize_type_refs(p_line):
            if '#' in m_line or '#' in p_line or TYPE_ID_RE.match(m_line) or TYPE_ID_RE.match(p_line):
                id_norm_matches += 1
    if id_norm_matches:
        motifs.add("id_ref_shift")

    minus_num_ids = sum(1 for l in minus if l.isdigit())
    plus_num_ids = sum(1 for l in plus if l.isdigit())
    if minus_num_ids != plus_num_ids:
        motifs.add("preamble_id_imbalance")

    if (('Reither' in minus_text and 'Rpresent' in plus_text) or
            ('Rpresent' in minus_text and 'Reither' in plus_text)):
        motifs.add("row_reither_rpresent")

    if (('open' in minus_text and 'closed' in plus_text) or
            ('closed' in minus_text and 'open' in plus_text)):
        motifs.add("row_open_closed_flip")

    if any(tok in minus_text or tok in plus_text for tok in ['Tvariant', 'Tfield', 'Tobject']):
        motifs.add("variant_or_object_area")

    if not motifs:
        motifs.add("other")

    return motifs, transitions


# ─── Insertion/Resync Helpers ────────────────────────────────────────────────

@dataclass
class InsertionResult:
    divergence_idx: Optional[int]
    matching_prefix: int
    reason: str
    ocaml_id: Optional[int]
    rust_id: Optional[int]
    shift: Optional[int] = None
    run_len: int = 0
    resync_ocaml_pos: Optional[int] = None
    resync_rust_pos: Optional[int] = None


def _compute_ordered_type_keys(sf: SexpFile) -> tuple[List[int], List[str]]:
    ids = sorted(sf.types.keys())
    memo: dict[int, str] = {}
    keys = [content_key(tid, sf.types, memo=memo) for tid in ids]
    return ids, keys


def _find_first_divergence(
    ocaml_ids: List[int],
    rust_ids: List[int],
    ocaml_keys: List[str],
    rust_keys: List[str],
) -> tuple[Optional[int], int, str]:
    max_len = max(len(ocaml_ids), len(rust_ids))
    matching_prefix = 0
    for i in range(max_len):
        if i >= len(ocaml_ids) or i >= len(rust_ids):
            return i, matching_prefix, "length"
        if ocaml_ids[i] != rust_ids[i]:
            return i, matching_prefix, "id"
        if ocaml_keys[i] != rust_keys[i]:
            return i, matching_prefix, "content"
        matching_prefix += 1
    return None, matching_prefix, "none"


def _find_resync_window(
    ocaml_keys: List[str],
    rust_keys: List[str],
    start: int,
    lookahead: int,
    min_run: int,
) -> Optional[Tuple[int, int, int]]:
    """Find a stable matching window after divergence.

    Returns (ocaml_pos, rust_pos, run_len) for the best resync candidate.
    """
    if start >= len(ocaml_keys) or start >= len(rust_keys):
        return None

    o_end = min(len(ocaml_keys), start + lookahead)
    r_end = min(len(rust_keys), start + lookahead)

    rust_positions_by_key: dict[str, List[int]] = {}
    for r in range(start, r_end):
        rust_positions_by_key.setdefault(rust_keys[r], []).append(r)

    best: Optional[Tuple[int, int, int]] = None
    for o in range(start, o_end):
        for r in rust_positions_by_key.get(ocaml_keys[o], []):
            run = 0
            while o + run < len(ocaml_keys) and r + run < len(rust_keys):
                if ocaml_keys[o + run] != rust_keys[r + run]:
                    break
                run += 1
            if run < min_run:
                continue

            if best is None:
                best = (o, r, run)
                continue

            b_o, b_r, b_run = best
            cand_dist = max(o - start, r - start)
            best_dist = max(b_o - start, b_r - start)
            cand_delta = abs(r - o)
            best_delta = abs(b_r - b_o)
            if (run > b_run or
                    (run == b_run and cand_dist < best_dist) or
                    (run == b_run and cand_dist == best_dist and cand_delta < best_delta) or
                    (run == b_run and cand_dist == best_dist and cand_delta == best_delta and (o, r) < (b_o, b_r))):
                best = (o, r, run)

    return best


def analyze_insertion(
    ocaml_sf: SexpFile,
    rust_sf: SexpFile,
    lookahead: int = 200,
    min_run: int = 4,
) -> InsertionResult:
    ocaml_ids, ocaml_keys = _compute_ordered_type_keys(ocaml_sf)
    rust_ids, rust_keys = _compute_ordered_type_keys(rust_sf)

    div_idx, matching_prefix, reason = _find_first_divergence(ocaml_ids, rust_ids, ocaml_keys, rust_keys)
    if div_idx is None:
        return InsertionResult(
            divergence_idx=None,
            matching_prefix=matching_prefix,
            reason=reason,
            ocaml_id=None,
            rust_id=None,
        )

    ocaml_id = ocaml_ids[div_idx] if div_idx < len(ocaml_ids) else None
    rust_id = rust_ids[div_idx] if div_idx < len(rust_ids) else None
    result = InsertionResult(
        divergence_idx=div_idx,
        matching_prefix=matching_prefix,
        reason=reason,
        ocaml_id=ocaml_id,
        rust_id=rust_id,
    )

    resync = _find_resync_window(ocaml_keys, rust_keys, div_idx, lookahead, min_run)
    if resync is None:
        return result

    resync_o, resync_r, run_len = resync
    result.resync_ocaml_pos = resync_o
    result.resync_rust_pos = resync_r
    result.run_len = run_len
    result.shift = resync_r - resync_o
    return result


# ─── Structure Reference Finder ──────────────────────────────────────────────

def find_refs_in_structure(structure: SexpNode, target_id: int,
                           path: Optional[List[str]] = None) -> List[str]:
    """Find all references to #<target_id> in the structure tree.

    Returns list of path descriptions.
    """
    if path is None:
        path = []
    results = []

    if isinstance(structure, SexpAtom):
        if structure.value == f"#{target_id}":
            results.append(" > ".join(path) if path else "(root)")
        return results

    # Build context from this node
    context = ""
    if structure.children:
        head = structure.children[0]
        if isinstance(head, SexpAtom):
            context = head.value

    # Check for (type #N) pattern
    if (len(structure.children) == 2 and
        isinstance(structure.children[0], SexpAtom) and
        structure.children[0].value == "type" and
        isinstance(structure.children[1], SexpAtom) and
        structure.children[1].value == f"#{target_id}"):
        results.append(" > ".join(path + ["type"]) if path else "type")
        return results

    new_path = path + [context] if context else path
    for child in structure.children:
        results.extend(find_refs_in_structure(child, target_id, new_path))

    return results


# ─── Commands ─────────────────────────────────────────────────────────────────

def cmd_summary(args, root: str):
    """Show overview of all failures."""
    diff_dir = os.path.join(root, '.parity-cache', 'tests', 'diffs')
    if not os.path.isdir(diff_dir):
        print(red("No diffs directory found. Run the parity test first:"))
        print("  ./scripts/test_typedtree_parity.sh")
        return

    diff_files = sorted(f for f in os.listdir(diff_dir) if f.endswith('.diff'))
    if not diff_files:
        print(green("No failures! All tests pass."))
        return

    entries = []
    total_hunks = 0

    for f in diff_files:
        path = os.path.join(diff_dir, f)
        with open(path, encoding='utf-8', errors='replace') as fh:
            diff_text = fh.read()

        info = analyze_diff(diff_text)
        base = f.replace('.diff', '').replace('tests_tests_src_', '')
        entries.append((base, info))
        total_hunks += info['hunks']

    # Sort by hunk count descending
    entries.sort(key=lambda e: e[1]['hunks'], reverse=True)

    # Print header
    print(bold(f"Parity Failures: {len(entries)} files, {total_hunks} total hunks"))
    print()
    print(f"  {'File':<45} {'Hunks':>6}  {'Pre/Str':>8}  {'Category':<12} {'First diff'}")
    print(f"  {'─'*45} {'─'*6}  {'─'*8}  {'─'*12} {'─'*40}")

    for name, info in entries:
        hunks_str = str(info['hunks'])
        pre_str = f"{info['preamble_hunks']}/{info['structure_hunks']}"

        cat = info['category']
        if cat == "id-only":
            cat_str = green(cat)
        elif cat == "path":
            cat_str = yellow(cat)
        elif cat == "path+id":
            cat_str = red(cat)
        else:
            cat_str = cat

        first = info['first_diff'][:40]
        print(f"  {name:<45} {hunks_str:>6}  {pre_str:>8}  {cat:<12} {dim(first)}")

    print()
    print(f"  Total: {bold(str(total_hunks))} hunks across {bold(str(len(entries)))} files")


def cmd_motifs(args, root: str):
    """Classify repeated hunk motifs across one or all diff files."""
    diff_dir = os.path.join(root, '.parity-cache', 'tests', 'diffs')
    if not os.path.isdir(diff_dir):
        print(red("No diffs directory found. Run the parity test first:"))
        print("  ./scripts/test_typedtree_parity.sh")
        return

    if args.file:
        name = resolve_file(args.file, root)
        diff_files = [name + '.diff']
    else:
        diff_files = sorted(f for f in os.listdir(diff_dir) if f.endswith('.diff'))

    if not diff_files:
        print(green("No failures! All tests pass."))
        return

    motif_hunk_counts: Counter[str] = Counter()
    motif_file_sets: dict[str, set[str]] = {}
    transition_counts: Counter[str] = Counter()
    transition_file_sets: dict[str, set[str]] = {}
    removed_path_counts: Counter[str] = Counter()
    added_path_counts: Counter[str] = Counter()
    removed_path_file_sets: dict[str, set[str]] = {}
    added_path_file_sets: dict[str, set[str]] = {}
    total_hunks = 0

    for diff_file in diff_files:
        path = os.path.join(diff_dir, diff_file)
        if not os.path.exists(path):
            print(red(f"Diff file not found: {path}"))
            continue

        with open(path, encoding='utf-8', errors='replace') as fh:
            diff_text = fh.read()

        base = diff_file.replace('.diff', '').replace('tests_tests_src_', '')
        hunks = iter_diff_hunks(diff_text)
        for hunk in hunks:
            motifs, transitions = classify_hunk_motifs(hunk)
            total_hunks += 1
            for motif in motifs:
                motif_hunk_counts[motif] += 1
                motif_file_sets.setdefault(motif, set()).add(base)
            for src, dst in transitions:
                transition = f"{src} -> {dst}"
                transition_counts[transition] += 1
                transition_file_sets.setdefault(transition, set()).add(base)

            minus_lines = [line[1:].strip() for line in hunk if line.startswith('-') and not line.startswith('---')]
            plus_lines = [line[1:].strip() for line in hunk if line.startswith('+') and not line.startswith('+++')]
            removed_paths, added_paths = _extract_hunk_path_delta(minus_lines, plus_lines)
            for term in removed_paths:
                removed_path_counts[term] += 1
                removed_path_file_sets.setdefault(term, set()).add(base)
            for term in added_paths:
                added_path_counts[term] += 1
                added_path_file_sets.setdefault(term, set()).add(base)

    if total_hunks == 0:
        print(yellow("No hunks found in selected diff files."))
        return

    print(bold(f"Motif Analysis: {len(diff_files)} files, {total_hunks} hunks"))
    print()
    print(f"  {'Motif':<30} {'Hunks':>7} {'Files':>7} {'Share':>8}")
    print(f"  {'─'*30} {'─'*7} {'─'*7} {'─'*8}")

    for motif, count in motif_hunk_counts.most_common(args.top):
        file_count = len(motif_file_sets.get(motif, set()))
        share = (count / total_hunks) * 100.0
        print(f"  {motif:<30} {count:>7} {file_count:>7} {share:>7.1f}%")

    if transition_counts:
        print()
        print(bold(f"Top Path Transitions (tail-matched, top {args.transitions})"))
        print(f"  {'Transition':<62} {'Hunks':>7} {'Files':>7}")
        print(f"  {'─'*62} {'─'*7} {'─'*7}")
        for transition, count in transition_counts.most_common(args.transitions):
            file_count = len(transition_file_sets.get(transition, set()))
            print(f"  {transition[:62]:<62} {count:>7} {file_count:>7}")

    if removed_path_counts or added_path_counts:
        print()
        print(bold(f"Top Removed Path Terms (top {args.paths})"))
        print(f"  {'Path':<62} {'Hunks':>7} {'Files':>7}")
        print(f"  {'─'*62} {'─'*7} {'─'*7}")
        for term, count in removed_path_counts.most_common(args.paths):
            file_count = len(removed_path_file_sets.get(term, set()))
            print(f"  {term[:62]:<62} {count:>7} {file_count:>7}")

        print()
        print(bold(f"Top Added Path Terms (top {args.paths})"))
        print(f"  {'Path':<62} {'Hunks':>7} {'Files':>7}")
        print(f"  {'─'*62} {'─'*7} {'─'*7}")
        for term, count in added_path_counts.most_common(args.paths):
            file_count = len(added_path_file_sets.get(term, set()))
            print(f"  {term[:62]:<62} {count:>7} {file_count:>7}")


def _print_candidate_extra_ids(
    label: str,
    ids: List[int],
    sf: SexpFile,
    limit: int = 8,
) -> None:
    if not ids:
        return
    print(f"  Candidate {label} IDs near divergence:")
    for tid in ids[:limit]:
        print(f"    #{tid}: {type_summary(sf.types[tid])}")
    if len(ids) > limit:
        print(f"    ... and {len(ids) - limit} more")


def cmd_insertion(args, root: str):
    """Analyze first divergence and estimate insertion/shift cascades."""
    if args.file:
        name = resolve_file(args.file, root)
        ocaml_sf, rust_sf = require_sexp_files(name, root)
        result = analyze_insertion(
            ocaml_sf,
            rust_sf,
            lookahead=args.lookahead,
            min_run=args.min_run,
        )

        short_name = name.replace("tests_tests_src_", "")
        print(bold(f"Insertion Analysis: {short_name}"))
        print(f"  Matching prefix: {result.matching_prefix} type(s)")

        if result.divergence_idx is None:
            print(green("  No divergence in preamble content."))
            return

        print(f"  First divergence: position {result.divergence_idx} "
              f"(reason: {result.reason}, OCaml #{result.ocaml_id}, Rust #{result.rust_id})")

        if result.shift is None:
            print(yellow("  No stable resync found in lookahead window; likely multi-cause divergence."))
            return

        print(f"  Resync window: OCaml pos {result.resync_ocaml_pos}, Rust pos {result.resync_rust_pos}, "
              f"run={result.run_len}, shift={result.shift:+d}")
        if result.shift > 0:
            print(red(f"  Rust likely inserted ~{result.shift} extra type node(s) before resync."))
        elif result.shift < 0:
            print(red(f"  OCaml likely inserted ~{-result.shift} extra type node(s) before resync."))
        else:
            print(yellow("  Shift is 0; divergence is likely content/path mismatch rather than insertion count."))

        ocaml_ids, _ = _compute_ordered_type_keys(ocaml_sf)
        rust_ids, _ = _compute_ordered_type_keys(rust_sf)
        div = result.divergence_idx
        if div is not None and result.shift and result.shift > 0:
            extras = rust_ids[div: min(len(rust_ids), div + result.shift)]
            _print_candidate_extra_ids("Rust", extras, rust_sf)
        elif div is not None and result.shift and result.shift < 0:
            extras = ocaml_ids[div: min(len(ocaml_ids), div + (-result.shift))]
            _print_candidate_extra_ids("OCaml", extras, ocaml_sf)
        return

    diff_dir = os.path.join(root, '.parity-cache', 'tests', 'diffs')
    if not os.path.isdir(diff_dir):
        print(red("No diffs directory found. Run the parity test first:"))
        print("  ./scripts/test_typedtree_parity.sh")
        return

    diff_files = sorted(f for f in os.listdir(diff_dir) if f.endswith('.diff'))
    if not diff_files:
        print(green("No failures! All tests pass."))
        return

    records: List[Tuple[str, InsertionResult]] = []
    missing_sexp = 0
    for diff_file in diff_files:
        name = diff_file[:-5]
        ocaml_sf = load_sexp('ocaml', name, root)
        rust_sf = load_sexp('rust', name, root)
        if ocaml_sf is None or rust_sf is None:
            missing_sexp += 1
            continue
        result = analyze_insertion(
            ocaml_sf,
            rust_sf,
            lookahead=args.lookahead,
            min_run=args.min_run,
        )
        short_name = name.replace("tests_tests_src_", "")
        records.append((short_name, result))

    if not records:
        print(red("No analyzable files with both OCaml and Rust sexp outputs."))
        print("Run parity test first to populate .parity-cache/tests/{ocaml,rust}.")
        return

    perfect = [(n, r) for n, r in records if r.divergence_idx is None]
    unresolved = [(n, r) for n, r in records if r.divergence_idx is not None and r.shift is None]
    shifted = [(n, r) for n, r in records if r.shift is not None and r.shift != 0]
    zero_shift = [(n, r) for n, r in records if r.shift == 0]
    rust_extra = [(n, r) for n, r in shifted if r.shift is not None and r.shift > 0]
    ocaml_extra = [(n, r) for n, r in shifted if r.shift is not None and r.shift < 0]
    total_rust_extra = sum(r.shift for _, r in rust_extra if r.shift is not None)
    total_ocaml_extra = sum(-r.shift for _, r in ocaml_extra if r.shift is not None)

    print(bold("Insertion Analysis (all cached failing files)"))
    print(f"  Files analyzed: {len(records)}"
          f"{f' ({missing_sexp} missing sexp skipped)' if missing_sexp else ''}")
    print(f"  Perfect preamble match: {len(perfect)}")
    print(f"  Shift detected: {len(shifted)} (Rust-extra: {len(rust_extra)}, OCaml-extra: {len(ocaml_extra)}, zero-shift: {len(zero_shift)})")
    print(f"  Unresolved (no resync window): {len(unresolved)}")
    print(f"  Estimated extra nodes: Rust +{total_rust_extra}, OCaml +{total_ocaml_extra}")

    if shifted:
        print()
        print(bold(f"Top Shift Files (top {args.top})"))
        print(f"  {'File':<42} {'Shift':>7} {'Run':>5} {'DivPos':>7} {'IDs'}")
        print(f"  {'─'*42} {'─'*7} {'─'*5} {'─'*7} {'─'*18}")
        ranked = sorted(
            shifted,
            key=lambda item: (abs(item[1].shift or 0), item[1].run_len, -(item[1].divergence_idx or 0)),
            reverse=True,
        )
        for file_name, result in ranked[:args.top]:
            ids = f"#{result.ocaml_id}/#{result.rust_id}"
            shift_str = f"{result.shift:+d}" if result.shift is not None else "?"
            div_str = str(result.divergence_idx) if result.divergence_idx is not None else "-"
            print(f"  {file_name:<42} {shift_str:>7} {result.run_len:>5} {div_str:>7} {ids}")

    if unresolved:
        print()
        print(bold(f"Earliest Unresolved Divergences (top {args.top})"))
        unresolved_sorted = sorted(unresolved, key=lambda item: item[1].divergence_idx or 999999)
        for file_name, result in unresolved_sorted[:args.top]:
            div_str = str(result.divergence_idx) if result.divergence_idx is not None else "-"
            print(f"  {file_name:<42} div={div_str:<6} reason={result.reason:<8} ids=#{result.ocaml_id}/#{result.rust_id}")


def cmd_preamble(args, root: str):
    """Show aligned type preamble comparison."""
    name = resolve_file(args.file, root)
    ocaml_sf, rust_sf = require_sexp_files(name, root)

    matches = match_types(ocaml_sf.types, rust_sf.types)

    # Stats
    n_match = sum(1 for m in matches if m[2] == "MATCH")
    n_shifted = sum(1 for m in matches if m[2] == "SHIFTED")
    n_extra_o = sum(1 for m in matches if m[2] == "EXTRA_OCAML")
    n_extra_r = sum(1 for m in matches if m[2] == "EXTRA_RUST")
    total = len(ocaml_sf.types)

    short_name = name.replace("tests_tests_src_", "")
    print(bold(f"Type Preamble: {short_name}"))
    print(f"  OCaml: {len(ocaml_sf.types)} types, Rust: {len(rust_sf.types)} types")
    print(f"  {green(f'{n_match} match')}  {yellow(f'{n_shifted} shifted')}  "
          f"{red(f'{n_extra_o} extra-ocaml')}  {red(f'{n_extra_r} extra-rust')}")
    print()

    # Table header
    print(f"  {'OCaml':>6} {'Rust':>6}  {'Status':<12} {'OCaml Type':<35} {'Rust Type'}")
    print(f"  {'─'*6} {'─'*6}  {'─'*12} {'─'*35} {'─'*35}")

    only_diff = hasattr(args, 'diff') and args.diff

    for o_id, r_id, status in matches:
        if only_diff and status == "MATCH":
            continue

        o_str = str(o_id) if o_id is not None else ""
        r_str = str(r_id) if r_id is not None else ""

        o_type = type_summary(ocaml_sf.types[o_id]) if o_id is not None else ""
        r_type = type_summary(rust_sf.types[r_id]) if r_id is not None else ""

        if status == "MATCH":
            stat = green("MATCH")
            o_type_c = o_type
            r_type_c = r_type
        elif status == "SHIFTED":
            stat = yellow("SHIFTED")
            o_type_c = yellow(o_type)
            r_type_c = yellow(r_type)
        elif status == "EXTRA_OCAML":
            stat = red("EXTRA_OCaml")
            o_type_c = red(o_type)
            r_type_c = ""
        else:
            stat = red("EXTRA_Rust")
            o_type_c = ""
            r_type_c = red(r_type)

        # Highlight #N refs
        o_type_c = re.sub(r'(#\d+)', lambda m: cyan(m.group(1)), o_type_c)
        r_type_c = re.sub(r'(#\d+)', lambda m: cyan(m.group(1)), r_type_c)

        print(f"  {o_str:>6} {r_str:>6}  {stat:<12} {o_type_c:<35} {r_type_c}")


def cmd_trace(args, root: str):
    """Trace a type through both compilers."""
    name = resolve_file(args.file, root)
    target_id = args.id
    compiler = args.compiler

    ocaml_sf, rust_sf = require_sexp_files(name, root)

    short_name = name.replace("tests_tests_src_", "")
    print(bold(f"Type Trace: #{target_id} in {compiler} ({short_name})"))
    print()

    # Primary compiler
    if compiler == "ocaml":
        primary_sf = ocaml_sf
        other_sf = rust_sf
        other_name = "rust"
    else:
        primary_sf = rust_sf
        other_sf = ocaml_sf
        other_name = "ocaml"

    if target_id not in primary_sf.types:
        print(red(f"Type #{target_id} not found in {compiler} (max: {max(primary_sf.types.keys())})"))
        return

    # Show type definition
    print(bold(f"  {compiler.upper()} #{target_id}:"))
    print(f"    {sexp_to_str(primary_sf.types[target_id])}")
    print(f"    Summary: {type_summary(primary_sf.types[target_id])}")
    print()

    # Find content match in other compiler
    primary_memo: dict = {}
    other_memo: dict = {}
    target_key = content_key(target_id, primary_sf.types, memo=primary_memo)

    matched_ids = []
    for tid in sorted(other_sf.types.keys()):
        k = content_key(tid, other_sf.types, memo=other_memo)
        if k == target_key:
            matched_ids.append(tid)

    if matched_ids:
        print(bold(f"  Content matches in {other_name}:"))
        for mid in matched_ids:
            marker = green("= same ID") if mid == target_id else yellow(f"shifted from #{target_id}")
            print(f"    #{mid} {marker}")
            print(f"      {sexp_to_str(other_sf.types[mid])}")
        print()
    else:
        print(red(f"  No content match found in {other_name}!"))
        # Show expanded content key for debugging
        print(f"  Content key: {target_key[:120]}...")
        print()

    # Find structural references
    print(bold(f"  References in {compiler} structure:"))
    if primary_sf.structure:
        refs = find_refs_in_structure(primary_sf.structure, target_id)
        if refs:
            for r in refs[:20]:  # Limit output
                print(f"    {cyan(f'#{target_id}')} at {r}")
            if len(refs) > 20:
                print(f"    ... and {len(refs) - 20} more")
        else:
            print(dim("    (no references found)"))
    print()

    # Find refs in other compiler
    if matched_ids:
        print(bold(f"  References in {other_name} structure:"))
        if other_sf.structure:
            for mid in matched_ids:
                refs = find_refs_in_structure(other_sf.structure, mid)
                if refs:
                    for r in refs[:20]:
                        print(f"    {cyan(f'#{mid}')} at {r}")
                    if len(refs) > 20:
                        print(f"    ... and {len(refs) - 20} more")
                else:
                    print(dim(f"    #{mid}: (no references found)"))
        print()

    # Show what references this type
    print(bold(f"  Types referencing #{target_id} in {compiler}:"))
    referencing = []
    for tid, node in sorted(primary_sf.types.items()):
        s = sexp_to_str(node)
        if f"#{target_id}" in s and tid != target_id:
            referencing.append(tid)
    if referencing:
        for tid in referencing[:15]:
            print(f"    #{tid}: {type_summary(primary_sf.types[tid])}")
        if len(referencing) > 15:
            print(f"    ... and {len(referencing) - 15} more")
    else:
        print(dim("    (none)"))


def cmd_extra(args, root: str):
    """Find extra/missing type nodes between compilers."""
    name = resolve_file(args.file, root)
    ocaml_sf, rust_sf = require_sexp_files(name, root)

    short_name = name.replace("tests_tests_src_", "")
    print(bold(f"Extra/Missing Types: {short_name}"))
    print()

    # Build content keys
    ocaml_memo: dict = {}
    rust_memo: dict = {}
    ocaml_keys: dict[int, str] = {}
    rust_keys: dict[int, str] = {}

    for tid in ocaml_sf.types:
        ocaml_keys[tid] = content_key(tid, ocaml_sf.types, memo=ocaml_memo)
    for tid in rust_sf.types:
        rust_keys[tid] = content_key(tid, rust_sf.types, memo=rust_memo)

    # Count each content key
    ocaml_counts: dict[str, list[int]] = {}
    rust_counts: dict[str, list[int]] = {}

    for tid, key in ocaml_keys.items():
        ocaml_counts.setdefault(key, []).append(tid)
    for tid, key in rust_keys.items():
        rust_counts.setdefault(key, []).append(tid)

    all_keys = sorted(set(ocaml_counts.keys()) | set(rust_counts.keys()),
                       key=lambda k: min(ocaml_counts.get(k, [9999])[0],
                                          rust_counts.get(k, [9999])[0]))

    # Find differences
    extra_ocaml = []  # (key, ocaml_ids, rust_ids)
    extra_rust = []
    duplicated_ocaml = []
    duplicated_rust = []

    for key in all_keys:
        o_ids = ocaml_counts.get(key, [])
        r_ids = rust_counts.get(key, [])
        o_count = len(o_ids)
        r_count = len(r_ids)

        if o_count > 0 and r_count == 0:
            extra_ocaml.append((key, o_ids, r_ids))
        elif r_count > 0 and o_count == 0:
            extra_rust.append((key, o_ids, r_ids))
        elif o_count > r_count:
            duplicated_ocaml.append((key, o_ids, r_ids))
        elif r_count > o_count:
            duplicated_rust.append((key, o_ids, r_ids))

    # Report
    if extra_ocaml:
        print(red(bold(f"  Types only in OCaml ({len(extra_ocaml)}):")))
        for key, o_ids, _ in extra_ocaml:
            ids_str = ", ".join(f"#{i}" for i in sorted(o_ids))
            summary = _key_to_summary(key)
            print(f"    {cyan(ids_str):>20}  {summary}")
        print()

    if extra_rust:
        print(red(bold(f"  Types only in Rust ({len(extra_rust)}):")))
        for key, _, r_ids in extra_rust:
            ids_str = ", ".join(f"#{i}" for i in sorted(r_ids))
            summary = _key_to_summary(key)
            print(f"    {cyan(ids_str):>20}  {summary}")
        print()

    if duplicated_ocaml:
        print(yellow(bold(f"  More copies in OCaml ({len(duplicated_ocaml)}):")))
        for key, o_ids, r_ids in duplicated_ocaml:
            o_str = ", ".join(f"#{i}" for i in sorted(o_ids))
            r_str = ", ".join(f"#{i}" for i in sorted(r_ids))
            summary = _key_to_summary(key)
            print(f"    OCaml: {cyan(o_str)}  Rust: {cyan(r_str)}")
            print(f"    {dim(summary)}")
        print()

    if duplicated_rust:
        print(yellow(bold(f"  More copies in Rust ({len(duplicated_rust)}):")))
        for key, o_ids, r_ids in duplicated_rust:
            o_str = ", ".join(f"#{i}" for i in sorted(o_ids))
            r_str = ", ".join(f"#{i}" for i in sorted(r_ids))
            summary = _key_to_summary(key)
            print(f"    OCaml: {cyan(o_str)}  Rust: {cyan(r_str)}")
            print(f"    {dim(summary)}")
        print()

    if not (extra_ocaml or extra_rust or duplicated_ocaml or duplicated_rust):
        print(green("  No extra or missing types! Differences are in ID assignment only."))
    else:
        total_diff = len(extra_ocaml) + len(extra_rust) + len(duplicated_ocaml) + len(duplicated_rust)
        print(f"  Total content differences: {bold(str(total_diff))}")


def _format_id_list(ids: List[int], limit: int) -> str:
    shown = ids[:limit]
    txt = ", ".join(f"#{i}" for i in shown)
    if len(ids) > limit:
        txt += f", ... (+{len(ids) - limit})"
    return txt


def cmd_sharing(args, root: str):
    """Analyze copy-sharing imbalances for a specific file."""
    name = resolve_file(args.file, root)
    ocaml_sf, rust_sf = require_sexp_files(name, root)

    short_name = name.replace("tests_tests_src_", "")
    print(bold(f"Sharing Imbalance: {short_name}"))
    print()

    # Build content keys
    ocaml_memo: dict = {}
    rust_memo: dict = {}
    ocaml_keys: dict[int, str] = {}
    rust_keys: dict[int, str] = {}
    for tid in ocaml_sf.types:
        ocaml_keys[tid] = content_key(tid, ocaml_sf.types, memo=ocaml_memo)
    for tid in rust_sf.types:
        rust_keys[tid] = content_key(tid, rust_sf.types, memo=rust_memo)

    # Group ids by content key
    ocaml_counts: dict[str, list[int]] = {}
    rust_counts: dict[str, list[int]] = {}
    for tid, key in ocaml_keys.items():
        ocaml_counts.setdefault(key, []).append(tid)
    for tid, key in rust_keys.items():
        rust_counts.setdefault(key, []).append(tid)

    # Keep only keys present in both compilers with different multiplicity
    entries = []
    for key in set(ocaml_counts.keys()) & set(rust_counts.keys()):
        o_ids = sorted(ocaml_counts[key])
        r_ids = sorted(rust_counts[key])
        if len(o_ids) == len(r_ids):
            continue
        summary = _key_to_summary(key)
        if args.contains:
            needle = args.contains.lower()
            if needle not in summary.lower() and needle not in key.lower():
                continue
        diff = len(r_ids) - len(o_ids)
        refs_score = 0
        if ocaml_sf.structure and rust_sf.structure:
            for tid in o_ids[:3]:
                refs_score += len(find_refs_in_structure(ocaml_sf.structure, tid))
            for tid in r_ids[:3]:
                refs_score += len(find_refs_in_structure(rust_sf.structure, tid))
        entries.append((abs(diff), refs_score, diff, summary, o_ids, r_ids))

    if not entries:
        if args.contains:
            print(green(f'  No sharing imbalance keys matched "{args.contains}".'))
        else:
            print(green("  No sharing imbalances found (content multiplicities match)."))
        return

    entries.sort(key=lambda e: (-e[0], -e[1], e[3]))
    shown = entries[:args.top]

    print(f"  Found {bold(str(len(entries)))} imbalanced keys; showing top {bold(str(len(shown)))}.")
    print()

    for idx, (_abs_diff, _refs_score, diff, summary, o_ids, r_ids) in enumerate(shown, 1):
        side = f"Rust +{diff}" if diff > 0 else f"OCaml +{-diff}"
        side_colored = yellow(side) if diff != 0 else side
        print(bold(f"  {idx:>2}. {summary}"))
        print(f"      Count: OCaml={len(o_ids)} Rust={len(r_ids)} ({side_colored})")
        print(f"      OCaml ids: {cyan(_format_id_list(o_ids, args.ids))}")
        print(f"      Rust  ids: {cyan(_format_id_list(r_ids, args.ids))}")

        if ocaml_sf.structure:
            for tid in o_ids[:min(args.ids, len(o_ids))]:
                refs = find_refs_in_structure(ocaml_sf.structure, tid)
                if refs:
                    refs_text = " | ".join(refs[:args.refs])
                    extra = f" (+{len(refs) - args.refs})" if len(refs) > args.refs else ""
                    print(f"      OCaml #{tid} refs: {dim(refs_text + extra)}")
                else:
                    print(f"      OCaml #{tid} refs: {dim('(no structure refs)')}")
        if rust_sf.structure:
            for tid in r_ids[:min(args.ids, len(r_ids))]:
                refs = find_refs_in_structure(rust_sf.structure, tid)
                if refs:
                    refs_text = " | ".join(refs[:args.refs])
                    extra = f" (+{len(refs) - args.refs})" if len(refs) > args.refs else ""
                    print(f"      Rust  #{tid} refs: {dim(refs_text + extra)}")
                else:
                    print(f"      Rust  #{tid} refs: {dim('(no structure refs)')}")
        print()


def cmd_sharing_summary(args, root: str):
    """Aggregate sharing imbalances across all failing files."""
    diff_dir = os.path.join(root, '.parity-cache', 'tests', 'diffs')
    if not os.path.isdir(diff_dir):
        print(red("No diffs directory found. Run the parity test first:"))
        print("  ./scripts/test_typedtree_parity.sh")
        return

    diff_files = sorted(f for f in os.listdir(diff_dir) if f.endswith('.diff'))
    if not diff_files:
        print(green("No failures! All tests pass."))
        return

    grouped: Dict[Tuple[str, str], Dict[str, Union[int, List[str]]]] = {}
    scanned = 0
    skipped = 0

    for diff_file in diff_files:
        name = diff_file.replace('.diff', '')
        ocaml_sf = load_sexp('ocaml', name, root)
        rust_sf = load_sexp('rust', name, root)
        if ocaml_sf is None or rust_sf is None:
            skipped += 1
            continue

        scanned += 1
        ocaml_memo: dict = {}
        rust_memo: dict = {}
        ocaml_counts: dict[str, list[int]] = {}
        rust_counts: dict[str, list[int]] = {}

        for tid in ocaml_sf.types:
            key = content_key(tid, ocaml_sf.types, memo=ocaml_memo)
            ocaml_counts.setdefault(key, []).append(tid)
        for tid in rust_sf.types:
            key = content_key(tid, rust_sf.types, memo=rust_memo)
            rust_counts.setdefault(key, []).append(tid)

        for key in set(ocaml_counts.keys()) & set(rust_counts.keys()):
            o_count = len(ocaml_counts[key])
            r_count = len(rust_counts[key])
            diff = r_count - o_count
            if diff == 0:
                continue
            summary = _key_to_summary(key)
            if args.contains:
                needle = args.contains.lower()
                if needle not in summary.lower() and needle not in key.lower():
                    continue
            side = "Rust" if diff > 0 else "OCaml"
            bucket = (side, summary)
            entry = grouped.setdefault(bucket, {"files": 0, "copies": 0, "examples": []})
            entry["files"] = int(entry["files"]) + 1
            entry["copies"] = int(entry["copies"]) + abs(diff)
            examples = entry["examples"]
            if isinstance(examples, list) and len(examples) < args.examples:
                examples.append(name)

    if not grouped:
        if args.contains:
            print(green(f'No aggregate sharing imbalances matched "{args.contains}".'))
        else:
            print(green("No aggregate sharing imbalances found."))
        return

    rows = []
    for (side, summary), info in grouped.items():
        rows.append((
            int(info["files"]),
            int(info["copies"]),
            side,
            summary,
            info["examples"] if isinstance(info["examples"], list) else [],
        ))

    rows.sort(key=lambda r: (-r[0], -r[1], r[2], r[3]))
    shown = rows[:args.top]

    print(bold("Sharing Imbalance Summary"))
    print()
    print(f"  Scanned files with sexp cache: {bold(str(scanned))}  (skipped: {skipped})")
    print(f"  Distinct imbalance motifs: {bold(str(len(rows)))}")
    print()
    print(f"  {'Side':<6} {'Files':>5} {'Copies':>6}  {'Type Summary'}")
    print(f"  {'─'*6} {'─'*5} {'─'*6}  {'─'*60}")

    for files_count, copies, side, summary, examples in shown:
        side_colored = yellow(side)
        print(f"  {side_colored:<6} {files_count:>5} {copies:>6}  {summary}")
        if examples:
            ex = ", ".join(str(e).replace('tests_tests_src_', '') for e in examples[:args.examples])
            print(f"          {dim('examples: ' + ex)}")

    if len(rows) > len(shown):
        print()
        print(dim(f"  ... {len(rows) - len(shown)} more motifs (increase --top to see more)"))


def _key_to_summary(key: str) -> str:
    """Convert a content key to a short summary."""
    key = key.strip()
    if not key:
        return key

    # Best effort: parse as sexp and reuse type_summary for more informative labels.
    if key.startswith('('):
        try:
            parsed = parse_sexp_file(key)
            if parsed:
                summary = type_summary(parsed[0])
                if len(summary) > 120:
                    return summary[:117] + "..."
                return summary
        except Exception:
            pass

    return key[:120] + ("..." if len(key) > 120 else "")


def cmd_divergence(args, root: str):
    """Find first divergence point between preambles."""
    name = resolve_file(args.file, root)
    ocaml_sf, rust_sf = require_sexp_files(name, root)

    short_name = name.replace("tests_tests_src_", "")
    print(bold(f"First Divergence: {short_name}"))
    print()

    ocaml_ids = sorted(ocaml_sf.types.keys())
    rust_ids = sorted(rust_sf.types.keys())

    print(f"  OCaml: {len(ocaml_ids)} types (#{ocaml_ids[0]}..#{ocaml_ids[-1]})")
    print(f"  Rust:  {len(rust_ids)} types (#{rust_ids[0]}..#{rust_ids[-1]})")
    print()

    # Walk in parallel and find first content mismatch
    ocaml_memo: dict = {}
    rust_memo: dict = {}

    max_len = max(len(ocaml_ids), len(rust_ids))
    first_diverge = None
    matching_prefix = 0

    for i in range(max_len):
        o_id = ocaml_ids[i] if i < len(ocaml_ids) else None
        r_id = rust_ids[i] if i < len(rust_ids) else None

        if o_id is None or r_id is None:
            first_diverge = i
            break

        if o_id != r_id:
            first_diverge = i
            break

        # Same ID - check content
        o_key = content_key(o_id, ocaml_sf.types, memo=ocaml_memo)
        r_key = content_key(r_id, rust_sf.types, memo=rust_memo)

        if o_key != r_key:
            first_diverge = i
            break

        matching_prefix += 1

    if first_diverge is None:
        print(green("  No divergence found! All types match."))
        return

    print(f"  {green(f'First {matching_prefix} types match perfectly.')}")
    print()
    print(bold(f"  First divergence at position {first_diverge}:"))

    o_id = ocaml_ids[first_diverge] if first_diverge < len(ocaml_ids) else None
    r_id = rust_ids[first_diverge] if first_diverge < len(rust_ids) else None

    if o_id is not None and r_id is not None:
        if o_id == r_id:
            # Same ID but different content
            print(f"    ID #{o_id} exists in both but differs:")
            print(f"    OCaml: {type_summary(ocaml_sf.types[o_id])}")
            print(f"    Rust:  {type_summary(rust_sf.types[r_id])}")
            print()
            print(f"    OCaml full: {sexp_to_str(ocaml_sf.types[o_id])[:120]}")
            print(f"    Rust  full: {sexp_to_str(rust_sf.types[r_id])[:120]}")

            # Check if it's a ref difference
            o_str = sexp_to_str(ocaml_sf.types[o_id])
            r_str = sexp_to_str(rust_sf.types[r_id])
            _show_string_diff(o_str, r_str)
        else:
            # Different IDs at same position
            print(f"    OCaml has #{o_id}, Rust has #{r_id}")
            if o_id in rust_sf.types:
                print(f"    OCaml #{o_id} also exists in Rust")
            else:
                print(f"    OCaml #{o_id} does NOT exist in Rust")
            if r_id in ocaml_sf.types:
                print(f"    Rust #{r_id} also exists in OCaml")
            else:
                print(f"    Rust #{r_id} does NOT exist in OCaml")
    elif o_id is None:
        print(f"    OCaml ran out of types, Rust has extra #{r_id}: {type_summary(rust_sf.types[r_id])}")
    else:
        print(f"    Rust ran out of types, OCaml has extra #{o_id}: {type_summary(ocaml_sf.types[o_id])}")

    print()

    # Show context: few types around the divergence
    print(bold("  Context around divergence:"))
    start = max(0, first_diverge - 2)
    end = min(max_len, first_diverge + 5)

    for i in range(start, end):
        o_id = ocaml_ids[i] if i < len(ocaml_ids) else None
        r_id = rust_ids[i] if i < len(rust_ids) else None

        marker = " >> " if i == first_diverge else "    "

        o_info = f"#{o_id} {type_summary(ocaml_sf.types[o_id])}" if o_id is not None else "(none)"
        r_info = f"#{r_id} {type_summary(rust_sf.types[r_id])}" if r_id is not None else "(none)"

        if i == first_diverge:
            o_info = red(o_info)
            r_info = red(r_info)

        print(f"  {marker}[{i:>4}] OCaml: {o_info}")
        print(f"  {marker}       Rust:  {r_info}")

    # Analyze the cascade
    print()
    _analyze_cascade(ocaml_sf, rust_sf, ocaml_ids, rust_ids, first_diverge, ocaml_memo, rust_memo)


def _show_string_diff(a: str, b: str):
    """Show where two strings first differ."""
    for i in range(min(len(a), len(b))):
        if a[i] != b[i]:
            ctx_start = max(0, i - 20)
            print(f"    First char diff at position {i}:")
            print(f"      OCaml: ...{a[ctx_start:i]}{red(a[i:i+10])}...")
            print(f"      Rust:  ...{b[ctx_start:i]}{red(b[i:i+10])}...")
            return


def _analyze_cascade(ocaml_sf, rust_sf, ocaml_ids, rust_ids, first_diverge, ocaml_memo, rust_memo):
    """Analyze whether the divergence is an insertion, deletion, or reordering."""
    if first_diverge >= len(ocaml_ids) or first_diverge >= len(rust_ids):
        return

    o_id = ocaml_ids[first_diverge]
    r_id = rust_ids[first_diverge]

    o_key = content_key(o_id, ocaml_sf.types, memo=ocaml_memo)
    r_key = content_key(r_id, rust_sf.types, memo=rust_memo)

    # Check if ocaml's type at divergence exists later in rust
    if o_id == r_id:
        # Same ID, different content. Check if either content exists elsewhere
        # See if OCaml's content for this ID matches a different Rust ID
        for j, rid in enumerate(rust_ids):
            if j <= first_diverge:
                continue
            rk = content_key(rid, rust_sf.types, memo=rust_memo)
            if rk == o_key:
                print(bold("  Cascade analysis:"))
                print(f"    OCaml #{o_id} content matches Rust #{rid} (position {j})")
                print(f"    This suggests Rust inserted {j - first_diverge} extra type(s) before #{o_id}")
                return

        for j, oid in enumerate(ocaml_ids):
            if j <= first_diverge:
                continue
            ok = content_key(oid, ocaml_sf.types, memo=ocaml_memo)
            if ok == r_key:
                print(bold("  Cascade analysis:"))
                print(f"    Rust #{r_id} content matches OCaml #{oid} (position {j})")
                print(f"    This suggests OCaml inserted {j - first_diverge} extra type(s) before #{r_id}")
                return

    # Check for simple shift
    remaining_ocaml = set(ocaml_ids[first_diverge:])
    remaining_rust = set(rust_ids[first_diverge:])
    only_ocaml = remaining_ocaml - remaining_rust
    only_rust = remaining_rust - remaining_ocaml

    if only_ocaml or only_rust:
        print(bold("  ID analysis after divergence:"))
        if only_ocaml:
            print(f"    IDs only in OCaml: {', '.join(f'#{i}' for i in sorted(only_ocaml)[:10])}")
        if only_rust:
            print(f"    IDs only in Rust:  {', '.join(f'#{i}' for i in sorted(only_rust)[:10])}")
        if len(only_ocaml) == len(only_rust):
            print(f"    Equal count ({len(only_ocaml)}) — likely shifted allocation")
        elif len(only_rust) > len(only_ocaml):
            print(f"    Rust has {len(only_rust) - len(only_ocaml)} extra type node(s)")
        else:
            print(f"    OCaml has {len(only_ocaml) - len(only_rust)} extra type node(s)")


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Analyze parity differences between OCaml and Rust compiler output.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s summary
  %(prog)s motifs
  %(prog)s motifs Service__PublicVideo --top 15
  %(prog)s preamble ticker
  %(prog)s trace ticker 11
  %(prog)s extra more_poly_variant_test
  %(prog)s sharing Service__PublicVideo --contains transcriptStatus
  %(prog)s sharing-summary --top 20
  %(prog)s divergence bs_set_int_test
  %(prog)s insertion
  %(prog)s insertion ticker
        """)

    parser.add_argument('--no-color', action='store_true', help='Disable colored output')

    subparsers = parser.add_subparsers(dest='command', help='Command to run')

    # summary
    sub_summary = subparsers.add_parser('summary', help='Overview of all failures')

    # motifs
    sub_motifs = subparsers.add_parser('motifs', help='Hunk-level motif classification')
    sub_motifs.add_argument('file', nargs='?', help='Optional file name/short name for single-file analysis')
    sub_motifs.add_argument('--top', type=int, default=12, help='Number of motifs to show (default: 12)')
    sub_motifs.add_argument('--transitions', type=int, default=12,
                            help='Number of path transitions to show (default: 12)')
    sub_motifs.add_argument('--paths', type=int, default=12,
                            help='Number of removed/added path terms to show (default: 12)')

    # preamble
    sub_preamble = subparsers.add_parser('preamble', help='Aligned type preamble comparison')
    sub_preamble.add_argument('file', help='File name or short name (e.g., "ticker")')
    sub_preamble.add_argument('--diff', action='store_true', help='Only show non-matching types')

    # trace
    sub_trace = subparsers.add_parser('trace', help='Trace a type through both compilers')
    sub_trace.add_argument('file', help='File name or short name')
    sub_trace.add_argument('id', type=int, help='Type ID to trace')
    sub_trace.add_argument('--compiler', choices=['ocaml', 'rust'], default='ocaml',
                          help='Which compiler\'s ID to trace (default: ocaml)')

    # extra
    sub_extra = subparsers.add_parser('extra', help='Find extra/missing type nodes')
    sub_extra.add_argument('file', help='File name or short name')

    # sharing
    sub_sharing = subparsers.add_parser('sharing', help='Copy-sharing imbalance analysis')
    sub_sharing.add_argument('file', help='File name or short name')
    sub_sharing.add_argument('--top', type=int, default=15,
                             help='How many imbalance entries to show (default: 15)')
    sub_sharing.add_argument('--ids', type=int, default=4,
                             help='Max ids per compiler for each entry (default: 4)')
    sub_sharing.add_argument('--refs', type=int, default=2,
                             help='Max structure reference paths per id (default: 2)')
    sub_sharing.add_argument('--contains', type=str, default=None,
                             help='Only show entries containing this text')

    # sharing-summary
    sub_sharing_summary = subparsers.add_parser(
        'sharing-summary', help='Aggregate sharing imbalances across failing files'
    )
    sub_sharing_summary.add_argument('--top', type=int, default=20,
                                     help='How many motifs to show (default: 20)')
    sub_sharing_summary.add_argument('--examples', type=int, default=3,
                                     help='How many example files per motif (default: 3)')
    sub_sharing_summary.add_argument('--contains', type=str, default=None,
                                     help='Only include motifs containing this text')

    # divergence
    sub_divergence = subparsers.add_parser('divergence', help='First divergence analysis')
    sub_divergence.add_argument('file', help='File name or short name')

    # insertion
    sub_insertion = subparsers.add_parser('insertion', help='First insertion/resync analysis')
    sub_insertion.add_argument('file', nargs='?', help='Optional file name or short name')
    sub_insertion.add_argument('--lookahead', type=int, default=200,
                               help='Max positions to scan for resync window (default: 200)')
    sub_insertion.add_argument('--min-run', type=int, default=4,
                               help='Minimum consecutive matches to accept a resync (default: 4)')
    sub_insertion.add_argument('--top', type=int, default=12,
                               help='Rows to show in aggregated tables (default: 12)')

    args = parser.parse_args()

    global USE_COLOR
    if args.no_color or not sys.stdout.isatty():
        USE_COLOR = False

    if not args.command:
        parser.print_help()
        sys.exit(1)

    root = find_project_root()

    commands = {
        'summary': cmd_summary,
        'motifs': cmd_motifs,
        'preamble': cmd_preamble,
        'trace': cmd_trace,
        'extra': cmd_extra,
        'sharing': cmd_sharing,
        'sharing-summary': cmd_sharing_summary,
        'divergence': cmd_divergence,
        'insertion': cmd_insertion,
    }

    commands[args.command](args, root)


if __name__ == '__main__':
    main()
