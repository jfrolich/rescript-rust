#!/usr/bin/env python3
# Measurement prototype, not reviewed code. See ../../THREE_TREES.md section 6.
"""Resolve every profiled address of the executable to its stack of inlined
frames with llvm-symbolizer --inlines. Output: pickle {addr: [(function, file), ...]} innermost first."""
import sys, pickle, subprocess, json
parsed, exe, out = sys.argv[1:4]
self_cost, edges, fn_of_addr = pickle.load(open(parsed, "rb"))
addrs = sorted({a for (ob, a) in self_cost if ob.endswith("/rescript")} | {a for (ob, a, _, _) in edges if ob.endswith("/rescript")})
inp = "\n".join("0x%x" % a for a in addrs) + "\n"
p = subprocess.run(["llvm-symbolizer", "--obj=" + exe, "--inlines", "--output-style=JSON", "--no-demangle"],
                   input=inp, capture_output=True, text=True, check=True)
res = {}
for line in p.stdout.splitlines():
    if not line.strip():
        continue
    d = json.loads(line)
    a = int(d["Address"], 16)
    res[a] = [(s.get("FunctionName", ""), s.get("FileName", "")) for s in d.get("Symbol", [])]
pickle.dump(res, open(out, "wb"))
print(len(res), "addresses")
