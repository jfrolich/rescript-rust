import sys, collections, re
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import cg
sc, arcs, summary = cg.load(sys.argv[1])
selfc = {f: sum(m.values()) for f, m in sc.items()}
incl = collections.Counter(selfc)
for (caller, a, callee, c) in arcs:
    if caller != callee: incl[caller] += c
pats = sys.argv[2:]
print('summary', summary)
for (ob, fn), c in sorted(incl.items(), key=lambda x: -x[1]):
    if any(re.search(p, fn) for p in pats):
        print(f'{c/1e6:10.1f} M {c/summary*100:6.2f}%  self {selfc.get((ob,fn),0)/1e6:8.1f}  {fn[:150]}')
