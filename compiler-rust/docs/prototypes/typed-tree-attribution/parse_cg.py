#!/usr/bin/env python3
# Measurement prototype, not reviewed code. See ../../THREE_TREES.md section 6.
"""Parse a callgrind profile taken with --dump-instr=yes.
Writes: self cost per (object, address); call edges (object, call-site address,
callee object, callee function) with inclusive cost."""
import sys, re, pickle, collections
path = sys.argv[1]
names = {"ob": {}, "fl": {}, "fn": {}}
def resolve(kind, text):
    m = re.match(r"\((\d+)\)(?: (.*))?$", text)
    if not m:
        return text
    ident, name = m.group(1), m.group(2)
    if name is not None:
        names[kind][ident] = name
    return names[kind][ident]
self_cost = collections.Counter()
edges = collections.Counter()
fn_of_addr = {}
ob = fn = cob = cfn = None
addr = 0
pending_call = False
with open(path) as f:
    for line in f:
        line = line.rstrip("\n")
        if not line:
            continue
        c = line[0]
        if c.isdigit() or c in "+-*":
            parts = line.split()
            a = parts[0]
            if a == "*":
                pass
            elif a[0] == "+":
                addr += int(a[1:], 0) if a[1:].startswith("0x") else int(a[1:])
            elif a[0] == "-":
                addr -= int(a[1:], 0) if a[1:].startswith("0x") else int(a[1:])
            else:
                addr = int(a, 16)
            cost = int(parts[2]) if len(parts) > 2 else 0
            if pending_call:
                edges[(ob, addr, cob or ob, cfn)] += cost
                pending_call = False
                cob = None
            else:
                self_cost[(ob, addr)] += cost
                fn_of_addr[(ob, addr)] = fn
            continue
        if line.startswith("ob="):
            ob = resolve("ob", line[3:])
        elif line.startswith("fn="):
            fn = resolve("fn", line[3:])
        elif line.startswith("cob="):
            cob = resolve("ob", line[4:])
        elif line.startswith("cfn="):
            cfn = resolve("fn", line[4:])
        elif line.startswith(("fl=", "fi=", "fe=", "cfi=", "cfl=")):
            k, v = line.split("=", 1)
            resolve("fl", v)
        elif line.startswith("calls="):
            pending_call = True
pickle.dump((dict(self_cost), dict(edges), fn_of_addr), open(sys.argv[2], "wb"))
print("self", sum(self_cost.values()), "addresses", len(self_cost), "edges", len(edges))
