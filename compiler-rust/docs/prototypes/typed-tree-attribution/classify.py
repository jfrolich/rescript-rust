#!/usr/bin/env python3
# Measurement prototype, not reviewed code. See ../../THREE_TREES.md section 6.
"""Attribute every instruction of a callgrind profile to typed-tree mechanisms.
An address belongs to the first mechanism any of its inlined frames matches;
out-of-line allocator and memcpy calls are charged to the mechanism of the
calling address."""
import pickle, collections, subprocess, re, sys
self_cost, edges, fn_of_addr = pickle.load(open("parsed.pkl","rb"))
frames = pickle.load(open("frames.pkl","rb"))
total = sum(self_cost.values())
names = sorted({f for fr in frames.values() for f,_ in fr})
dem = subprocess.run(["llvm-cxxfilt"], input="\n".join(names), capture_output=True, text=True).stdout.split("\n")
D = dict(zip(names, dem))
WRITE = re.compile(r"TypedArena>::(push_|with_|update_|set_|prepend_|new|with_source_len|default)|ListPool<.*>>::(push_iter|reserve)|Idx>::from_index|TypedArena as core::default::Default|::overlay(_pattern_list)?$")
TT = re.compile(r"types::typedtree::|types::tast_arena::")
def short(path):
    i = path.find("compiler-rust/src/")
    if i >= 0: return path[i+len("compiler-rust/src/"):]
    i = path.find("rewatch/src/")
    if i >= 0: return "rewatch/" + path[i+len("rewatch/src/"):]
    return "lib"
def kind(fr):
    # innermost first
    for f, fl in fr:
        d = D.get(f, f)
        if fl.endswith("types/tast_arena.rs"):
            return "push" if WRITE.search(d) else "read"
    for f, fl in fr:
        d = D.get(f, f)
        if TT.search(d):
            if "drop_in_place<" in d or "as core::ops::drop::Drop>::drop" in d:
                return "drop"
            if "as core::clone::Clone>::clone" in d or "::clone" in d:
                return "clone"
            if short(fl) == "lib":
                return "collect"
    return None
def owner(fr):
    # outermost frame = the function the code was compiled into
    for f, fl in reversed(fr):
        s = short(fl)
        if s != "lib":
            if s.startswith("types/typecore") or s.startswith("types/typemod"): return "checker walk"
            if s.startswith("types/parmatch"): return "pattern analysis"
            if s.startswith("types/"): return "types other (" + s.split("/")[1] + ")"
            if s.startswith("raw_lambda/"): return "raw Lambda (" + s.split("/")[1] + ")"
            if s.startswith("gentype/"): return "genType"
            if s.startswith("driver"): return "driver"
            return s.split("/")[0]
    return "generic/library"
K = collections.Counter(); KO = collections.Counter(); kind_of = {}
for (ob,a),c in self_cost.items():
    if not ob.endswith("/rescript"): continue
    fr = frames.get(a, [])
    k = kind(fr)
    kind_of[a] = (k, owner(fr))
    if k:
        K[k]+=c; KO[(k, owner(fr))]+=c
ALLOC = re.compile(r"^(mi_|_mi_|__rust_alloc|__rust_dealloc|__rust_realloc|__rdl_|__rg_|malloc|free|realloc|calloc)")
COPY = re.compile(r"mem(cpy|move|set)")
E = collections.Counter(); EO = collections.Counter()
for (ob,a,cob,cfn),c in edges.items():
    if not ob.endswith("/rescript"): continue
    if a not in kind_of:
        fr = frames.get(a, []); kind_of[a] = (kind(fr), owner(fr))
    k, o = kind_of[a]
    if not k: continue
    d = D.get(cfn, cfn)
    if ALLOC.search(cfn): E[(k,"allocator")]+=c; EO[(k,o)]+=c
    elif COPY.search(cfn): E[(k,"memcpy")]+=c; EO[(k,o)]+=c
    else: E[(k,"other callee: "+d[:70])]+=c
M=1e6
print("total", total)
print("\n== self instructions by mechanism")
for k,c in K.most_common(): print(f"{k:8} {c/M:9.2f} M {100*c/total:.3f}%")
print("\n== out-of-line callees charged to the calling address (inclusive)")
agg = collections.Counter()
for (k,w),c in sorted(E.items(), key=lambda x:-x[1]):
    if w in ("allocator","memcpy"): agg[(k,w)]+=c
    elif c > 0.3*M: print(f"   [not charged] {k:8} {w:75} {c/M:8.2f} M")
for (k,w),c in sorted(agg.items()): print(f"{k:8} {w:10} {c/M:9.2f} M {100*c/total:.3f}%")
print("\n== mechanism x owner (self + allocator + memcpy)")
tot = collections.Counter()
for key,c in KO.items(): tot[key]+=c
for key,c in EO.items(): tot[key]+=c
for (k,o),c in sorted(tot.items(), key=lambda x:(x[0][0], -x[1])):
    if c > 0.05*M: print(f"{k:8} {o:34} {c/M:9.2f} M {100*c/total:.3f}%")
bym = collections.Counter()
for (k,o),c in tot.items(): bym[k]+=c
print("\n== totals by mechanism (self + allocator + memcpy)")
for k,c in bym.most_common(): print(f"{k:8} {c/M:9.2f} M {100*c/total:.3f}%")
print("sum", sum(bym.values())/M, 100*sum(bym.values())/total)
# self instructions by owner file group, whole build
OW = collections.Counter()
for (ob,a),c in self_cost.items():
    if ob.endswith("/rescript"): OW[kind_of[a][1]]+=c
    else: OW["other objects (libc, ld)"]+=c
print("\n== self instructions by owner (outermost frame's file)")
for o,c in OW.most_common(30): print(f"{o:36} {c/M:9.2f} M {100*c/total:.2f}%")
