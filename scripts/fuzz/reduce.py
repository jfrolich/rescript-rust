"""Delta-debugging reducer that keeps a differential verdict mismatch."""

from __future__ import annotations

from typing import Callable

from mutate import _groups, detok, tokenize


def ddmin(items: list, test: Callable[[list], bool]) -> list:
    n = 2
    while len(items) >= 2:
        chunk = max(1, len(items) // n)
        reduced = False
        for i in range(0, len(items), chunk):
            cand = items[:i] + items[i + chunk:]
            if cand and test(cand):
                items = cand
                n = max(n - 1, 2)
                reduced = True
                break
        if not reduced:
            if chunk == 1:
                break
            n = min(len(items), n * 2)
    return items


def reduce_source(src: str, keep: Callable[[str], bool], budget: int = 400) -> str:
    calls = 0

    def t(s: str) -> bool:
        nonlocal calls
        if calls >= budget:
            return False
        calls += 1
        return keep(s)

    # 1) lines
    lines = src.split("\n")
    lines = ddmin(lines, lambda ls: t("\n".join(ls)))
    src = "\n".join(lines)
    # 2) balanced groups: try emptying each group body (outermost last)
    changed = True
    while changed and calls < budget:
        changed = False
        toks = tokenize(src)
        for a, b in sorted(_groups(toks), key=lambda g: g[0] - g[1]):
            if b - a <= 1:
                continue
            cand = detok(toks[:a + 1] + toks[b:])
            if t(cand):
                src, changed = cand, True
                break
    # 3) tokens
    toks = [x for x in tokenize(src) if x.kind != "comment"]
    toks = ddmin(toks, lambda ts: t(detok(ts)))
    src = detok(toks)
    # 4) squash whitespace runs
    import re

    cand = re.sub(r"\n\s*\n+", "\n", src).strip() + "\n"
    if cand != src and t(cand):
        src = cand
    return src
