"""Token-level and structure-aware mutators for ReScript sources.

The mutators aim for *near-miss* programs: one small change to a program
that compiles, so the result sits right next to a type-checker or parser
boundary. Many mutants are syntax errors (exercising the parser), many are
type errors (exercising typecore/typedecl/typemod), and some remain valid.
"""

from __future__ import annotations

import random
import re
from dataclasses import dataclass

TOKEN_RE = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<comment>//[^\n]*|/\*.*?\*/)
  | (?P<string>"(?:[^"\\\n]|\\.)*")
  | (?P<template>`(?:[^`\\]|\\.)*`)
  | (?P<char>'(?:[^'\\\n]|\\.[^']*)')
  | (?P<tyvar>'[a-z_][A-Za-z0-9_]*)
  | (?P<number>\d[\d_]*(?:\.\d*)?(?:[eE][+-]?\d+)?[lnf]?)
  | (?P<polyvar>\#[A-Za-z0-9_]+)
  | (?P<lident>[a-z_][A-Za-z0-9_']*)
  | (?P<uident>[A-Z][A-Za-z0-9_']*)
  | (?P<op>\.\.\.|=>|->|\|>|==|===|!=|!==|<=|>=|:=|\+\+|\+\.|-\.|\*\.|/\.|\?\.|[-+*/=<>!&|^%@~?:;,.#{}()\[\]])
  | (?P<other>.)
    """,
    re.S | re.X,
)

KEYWORDS = {
    "let", "rec", "and", "type", "module", "open", "include", "external", "if",
    "else", "switch", "when", "for", "while", "in", "to", "downto", "try",
    "catch", "exception", "mutable", "private", "constraint", "as", "true",
    "false", "async", "await", "assert", "lazy", "of", "list", "dict", "unpack",
}

LITERALS = [
    "0", "1", "-1", "1.0", "0.5", '"s"', '""', "'c'", "true", "false", "()",
    "[]", "list{}", "None", "Some(1)", "Ok(1)", "Error(\"e\")", "#tag", "{x: 1}",
    "[1, 2]", "(1, 2)", "1n", "dict{}", "x => x", "%raw(\"1\")", "?x", "_",
]

TYPES = [
    "int", "float", "string", "bool", "unit", "'a", "'b", "array<int>",
    "option<'a>", "list<string>", "result<int, string>", "int => int",
    "(int, string)", "{..}", "[#a | #b]", "[> #a]", "[< #a | #b]", "promise<int>",
    "dict<int>", "Js.Json.t", "t", "t<int>", "_", "bigint", "char",
]

INSERT_TOKENS = [
    "let", "rec", "mutable", "private", "?", "~", "...", "=", "=>", "->", ",", ";",
    "|", "(", ")", "{", "}", "[", "]", "<", ">", ":", ".", "@as(\"x\")", "@unboxed",
    "@tag(\"k\")", "@inline", "@module(\"m\")", "@send", "@val", "@new", "@uncurry",
    "async", "await", "open", "!", "&&", "||", "_", "type", "module", "include",
    "external", "exception", "switch", "if", "assert", "lazy",
]

OPEN = {"(": ")", "[": "]", "{": "}"}


@dataclass
class Tok:
    kind: str
    text: str


def tokenize(src: str) -> list[Tok]:
    return [Tok(m.lastgroup or "other", m.group(0)) for m in TOKEN_RE.finditer(src)]


def detok(toks: list[Tok]) -> str:
    return "".join(t.text for t in toks)


def _sig(toks):  # significant token indices
    return [i for i, t in enumerate(toks) if t.kind not in ("ws", "comment")]


def _groups(toks: list[Tok]) -> list[tuple[int, int]]:
    """Balanced (open, close) index pairs."""
    stack, out = [], []
    for i, t in enumerate(toks):
        if t.text in OPEN:
            stack.append(i)
        elif t.text in (")", "]", "}") and stack:
            j = stack.pop()
            if OPEN[toks[j].text] == t.text:
                out.append((j, i))
    return out


def _elements(toks, a, b):
    """Comma-separated element spans strictly inside group (a, b)."""
    spans, depth, start = [], 0, a + 1
    for i in range(a + 1, b):
        t = toks[i].text
        if t in OPEN:
            depth += 1
        elif t in (")", "]", "}"):
            depth -= 1
        elif t == "," and depth == 0:
            spans.append((start, i))
            start = i + 1
    if start < b:
        spans.append((start, b))
    return [s for s in spans if any(toks[k].kind not in ("ws", "comment") for k in range(*s))]


class Mutator:
    def __init__(self, rng: random.Random, donors: list[str] | None = None):
        self.rng = rng
        self.donors = donors or []

    def mutate(self, src: str, n: int = 1) -> tuple[str, list[str]]:
        applied = []
        for _ in range(n):
            ops = [m for m in dir(self) if m.startswith("m_")]
            for _attempt in range(10):
                op = self.rng.choice(ops)
                toks = tokenize(src)
                out = getattr(self, op)(toks)
                if out is not None:
                    new = detok(out) if isinstance(out, list) else out
                    if new != src:
                        src = new
                        applied.append(op[2:])
                        break
        return src, applied

    # --- identifier / literal substitution -------------------------------
    def _swap_kind(self, toks, kind, filt=lambda t: True):
        idx = [i for i in _sig(toks) if toks[i].kind == kind and filt(toks[i].text)]
        if len(idx) < 2:
            return None
        pool = sorted({toks[i].text for i in idx})
        i = self.rng.choice(idx)
        choices = [p for p in pool if p != toks[i].text]
        if not choices:
            return None
        toks[i] = Tok(kind, self.rng.choice(choices))
        return toks

    def m_swap_lident(self, toks):
        return self._swap_kind(toks, "lident", lambda s: s not in KEYWORDS)

    def m_swap_uident(self, toks):
        return self._swap_kind(toks, "uident")

    def m_swap_polyvar(self, toks):
        return self._swap_kind(toks, "polyvar")

    def m_swap_tyvar(self, toks):
        idx = [i for i in _sig(toks) if toks[i].kind == "tyvar"]
        if not idx:
            return None
        i = self.rng.choice(idx)
        toks[i] = Tok("tyvar", self.rng.choice(["'a", "'b", "'c", "'_", "'x"]))
        return toks

    def m_literal(self, toks):
        idx = [i for i in _sig(toks) if toks[i].kind in ("number", "string", "char", "template")
               or toks[i].text in ("true", "false", "None")]
        if not idx:
            return None
        i = self.rng.choice(idx)
        toks[i] = Tok("other", self.rng.choice(LITERALS))
        return toks

    def m_type_swap(self, toks):
        # replace the token right after a ':' (annotation) or inside <...>
        idx = [i for i in _sig(toks) if toks[i].kind in ("lident", "tyvar")
               and i > 0 and self._prev_sig(toks, i) in (":", "<", ",", "=>")]
        if not idx:
            return None
        i = self.rng.choice(idx)
        toks[i] = Tok("other", self.rng.choice(TYPES))
        return toks

    def _prev_sig(self, toks, i):
        j = i - 1
        while j >= 0 and toks[j].kind in ("ws", "comment"):
            j -= 1
        return toks[j].text if j >= 0 else ""

    # --- annotations ------------------------------------------------------
    def m_add_annotation(self, toks):
        idx = [i for i in _sig(toks) if toks[i].kind == "lident" and self._prev_sig(toks, i) in ("let", "(", ",", "~")]
        if not idx:
            return None
        i = self.rng.choice(idx)
        toks.insert(i + 1, Tok("other", ": " + self.rng.choice(TYPES)))
        return toks

    # --- token edits -----------------------------------------------------
    def m_delete_token(self, toks):
        s = _sig(toks)
        if not s:
            return None
        del toks[self.rng.choice(s)]
        return toks

    def m_duplicate_token(self, toks):
        s = _sig(toks)
        if not s:
            return None
        i = self.rng.choice(s)
        toks.insert(i, Tok(toks[i].kind, toks[i].text + " "))
        return toks

    def m_swap_adjacent(self, toks):
        s = _sig(toks)
        if len(s) < 2:
            return None
        k = self.rng.randrange(len(s) - 1)
        a, b = s[k], s[k + 1]
        toks[a], toks[b] = toks[b], toks[a]
        return toks

    def m_insert_token(self, toks):
        s = _sig(toks)
        if not s:
            return None
        i = self.rng.choice(s)
        toks.insert(i, Tok("other", self.rng.choice(INSERT_TOKENS) + " "))
        return toks

    # --- structural edits -------------------------------------------------
    def m_delete_element(self, toks):
        cands = [(a, b, e) for a, b in _groups(toks) for e in [_elements(toks, a, b)] if e]
        if not cands:
            return None
        a, b, els = self.rng.choice(cands)
        s, e = self.rng.choice(els)
        # also drop the following comma if any
        if e < b and toks[e].text == ",":
            e += 1
        elif s > a + 1 and toks[s - 1].text == ",":
            s -= 1
        del toks[s:e]
        return toks

    def m_duplicate_element(self, toks):
        cands = [(a, b, e) for a, b in _groups(toks) for e in [_elements(toks, a, b)] if e]
        if not cands:
            return None
        a, b, els = self.rng.choice(cands)
        s, e = self.rng.choice(els)
        toks.insert(e, Tok("other", ", " + detok(toks[s:e]).strip()))
        return toks

    def m_swap_elements(self, toks):
        cands = [(a, b, e) for a, b in _groups(toks) for e in [_elements(toks, a, b)] if len(e) >= 2]
        if not cands:
            return None
        a, b, els = self.rng.choice(cands)
        (s1, e1), (s2, e2) = self.rng.sample(els, 2)
        if s1 > s2:
            (s1, e1), (s2, e2) = (s2, e2), (s1, e1)
        x, y = detok(toks[s1:e1]), detok(toks[s2:e2])
        return detok(toks[:s1]) + y + detok(toks[e1:s2]) + x + detok(toks[e2:])

    def m_empty_group(self, toks):
        g = _groups(toks)
        if not g:
            return None
        a, b = self.rng.choice(g)
        del toks[a + 1:b]
        return toks

    def m_splice_group(self, toks):
        """Replace a balanced group with one of the same bracket kind from a donor."""
        g = _groups(toks)
        if not g or not self.donors:
            return None
        a, b = self.rng.choice(g)
        dt = tokenize(self.rng.choice(self.donors))
        dg = [(x, y) for x, y in _groups(dt) if dt[x].text == toks[a].text and y - x < 80]
        if not dg:
            return None
        x, y = self.rng.choice(dg)
        return detok(toks[:a]) + detok(dt[x:y + 1]) + detok(toks[b + 1:])

    # --- line edits -------------------------------------------------------
    def m_delete_line(self, toks):
        lines = detok(toks).split("\n")
        if len(lines) < 2:
            return None
        del lines[self.rng.randrange(len(lines))]
        return "\n".join(lines)

    def m_duplicate_line(self, toks):
        lines = detok(toks).split("\n")
        i = self.rng.randrange(len(lines))
        lines.insert(i, lines[i])
        return "\n".join(lines)

    def m_move_line(self, toks):
        lines = detok(toks).split("\n")
        if len(lines) < 3:
            return None
        i = self.rng.randrange(len(lines))
        line = lines.pop(i)
        lines.insert(self.rng.randrange(len(lines) + 1), line)
        return "\n".join(lines)

    # --- targeted keyword flips ------------------------------------------
    FLIPS = [
        (r"\blet rec\b", "let"), (r"\blet\b(?! rec)", "let rec"), (r"\bmutable ", ""),
        (r"~(\w+)(?!=)", r"~\1=?"), (r"=\?", ""), (r"\?(\w+)", r"\1"), (r"\basync ", ""),
        (r"\bawait ", ""), (r"=>", "->"), (r"\btype\b", "type rec"), (r"\btype rec\b", "type"),
        (r"\bprivate ", ""), (r"(type \w+) =", r"\1 = private"), (r"\.\.\.", ""),
        (r"\[#", "[> #"), (r"\[#", "[< #"), (r"\[>", "["), (r"\[<", "["), (r"\bopen ", "open! "),
        (r"\bexternal\b", "let"), (r":=", "="), (r"\bSome\(", "("), (r"\bOk\(", "Error("),
        (r"\bint\b", "float"), (r"\bfloat\b", "int"), (r"\bstring\b", "int"),
        (r"\blist\{", "["), (r"\{\.\.\.", "{"), (r"\?\.", "."), (r"\bwhen\b", "if"),
        (r"\|", ""), (r"\b_\b", "x"), (r"\bmodule type\b", "module"), (r": \w+ =>", "=>"),
        (r"\bunit\b", "int"), (r"\+", "+."), (r"\+\.", "+"), (r"\+\+", "+"),
        (r"\bdict\{", "{"), (r"@unboxed", ""), (r"@as\([^)]*\)", ""), (r"@tag\([^)]*\)", ""),
    ]

    def m_flip(self, toks):
        src = detok(toks)
        pat, rep = self.rng.choice(self.FLIPS)
        ms = list(re.finditer(pat, src))
        if not ms:
            return None
        m = self.rng.choice(ms)
        return src[:m.start()] + m.expand(rep) + src[m.end():]
