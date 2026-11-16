"""Count what T6x of the three-trees plan has to change in src/bir/lower.

Run from compiler-rust: python3 ../scripts/count_lowering_ids.py
Prints four Markdown tables over the non-test code: per file the functions
with a NodeId or ListId in their signature and the transition calls; the
J-touching functions called from other files; the structs and enums holding
an id; and where outputs and statements are stored and read.
"""
import re,glob,os,collections
T=['from_node','node','at','stmt_from_node','stmt_node','list_from','list_id']
src={}
for p in sorted(glob.glob('src/bir/lower/*.rs')):
    f=os.path.basename(p)[:-3]
    if f.endswith('_tests') or f in ('js','js_stmt'): continue
    lines=open(p).read().split('\n'); cut=len(lines)
    for i,l in enumerate(lines):
        if (l.startswith('mod tests') or l.startswith('mod allocation_tests')) and l.rstrip().endswith('{') or (l.startswith('#[cfg(test)]') and i+1<len(lines) and lines[i+1].startswith('mod ') and lines[i+1].rstrip().endswith('{')): cut=i;break
    src[f]='\n'.join(lines[:cut])
fn=re.compile(r'\n[ \t]*(?:pub(?:\([a-z:]+\))? )?fn (\w+)\s*(?:<[^>]*>)?\(([^{;]*?)\)\s*(->[^{;]*)?\{')
def body(t,start):
    d=0;i=start
    while True:
        c=t[i]
        if c=='{': d+=1
        elif c=='}':
            d-=1
            if d==0: return t[start:i+1]
        i+=1
rows=[];defs={}
for f,t in src.items():
    lines=len(t.split('\n'))
    sig=jsig=0; names=[]
    for m in fn.finditer(t):
        s=(m.group(2) or '')+(m.group(3) or '')
        if not re.search(r'\bNodeId\b|\bListId\b',s): continue
        sig+=1
        b=body(t,m.end()-1)
        if re.search(r'B::(from_node|node|at|stmt_from_node|stmt_node|list_from|list_id)\(',b) or 'self.js.' in b:
            jsig+=1; names.append(m.group(1))
        defs.setdefault(m.group(1),[]).append(f)
    tc={k:len(re.findall(r'B::'+k+r'\(',t)) for k in T}
    extra={'function_of_block':len(re.findall(r'\.function_of_block\(',t)),'push_list':len(re.findall(r'\.push_list\(',t))}
    raw=len(re.findall(r'View::J|Op::J|View::S[A-Z]|Op::S[A-Z]|plain::|norm::|\.arena\.(?:view|node|release|detach|replace|new_node|cold|set_cold|copy_subtree\w*|copy_leaf|\w+_from_list)\(|pure_expression|bir::j::|arena\.nodes\b|arena\.parents',t))
    rows.append((f,lines,sig,jsig,sum(tc.values()),tc,extra,raw,names))
print('| File | Lines | fns with NodeId/ListId in signature | of these, touching J (a transition call or self.js in the body) | transition calls | from_node | node | at | stmt_from_node | stmt_node | list_from | list_id | function_of_block | push_list | raw J sites left |')
print('| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |')
tot=collections.Counter()
for f,lines,sig,jsig,n,tc,ex,raw,names in rows:
    print(f'| `{f}.rs` | {lines} | {sig} | {jsig} | {n} | '+' | '.join(str(tc[k]) for k in T)+f" | {ex['function_of_block']} | {ex['push_list']} | {raw} |")
    tot['lines']+=lines;tot['sig']+=sig;tot['jsig']+=jsig;tot['n']+=n;tot['raw']+=raw
    for k in T: tot[k]+=tc[k]
    for k in ex: tot[k]+=ex[k]
print(f"| total | {tot['lines']} | {tot['sig']} | {tot['jsig']} | {tot['n']} | "+' | '.join(str(tot[k]) for k in T)+f" | {tot['function_of_block']} | {tot['push_list']} | {tot['raw']} |")
# cross-file callers of J-touching fns
print()
print('| Function (file) | Called from other files |')
print('| --- | --- |')
for f,lines,sig,jsig,n,tc,ex,raw,names in rows:
    for name in names:
        callers=collections.Counter()
        for g,t in src.items():
            if g==f: continue
            c=len(re.findall(r'(?:\.|::)'+name+r'\(',t))
            if c: callers[g]+=c
        if callers: print(f"| `{name}` (`{f}.rs`) | "+', '.join(f'`{g}.rs` {c}' for g,c in sorted(callers.items()))+' |')
# fields
print()
print('| Struct (file) | Fields that hold a NodeId or a ListId |')
print('| --- | --- |')
for f,t in src.items():
    for m in re.finditer(r'\n(?:pub(?:\([a-z:]+\))? )?(?:struct|enum) (\w+)[^{;]*\{',t):
        b=body(t,m.end()-1)
        fields=re.findall(r'\n\s*(?:pub(?:\([a-z:]+\))? )?(\w+): ([^,\n]*(?:NodeId|ListId)[^,\n]*),',b)
        variants=re.findall(r'\n\s*(\w+)\s*[\({][^\n]*(?:NodeId|ListId)[^\n]*',b) if not fields else []
        if fields or variants:
            print(f"| `{m.group(1)}` (`{f}.rs`) | "+', '.join(f'`{a}: {b2.strip()}`' for a,b2 in fields)+', '.join(f'`{v}`' for v in variants)+' |')
print()
print('| File | `Out {` built | `.value` of an output read or written | `statements.push`/`fill`/`place` | `impl norm::IfLists` / `simplify_if_head` |')
print('| --- | --- | --- | --- | --- |')
tot=[0,0,0,0]
for p in sorted(glob.glob('src/bir/lower/*.rs')):
    f=os.path.basename(p)[:-3]
    if f.endswith('_tests') or f in ('js','js_stmt'): continue
    lines=open(p).read().split('\n'); cut=len(lines)
    for i,l in enumerate(lines):
        if (l.startswith('mod tests') or l.startswith('mod allocation_tests')) and l.rstrip().endswith('{') or (l.startswith('#[cfg(test)]') and i+1<len(lines) and lines[i+1].startswith('mod ') and lines[i+1].rstrip().endswith('{')): cut=i;break
    t='\n'.join(lines[:cut])
    a=len(re.findall(r'\bOut \{',t)); b=len(re.findall(r'\b(?:out|output|first|second|arg|body|child)\.value\b',t)); c=len(re.findall(r'statements\s*\.\s*(?:push|fill|fill_held)\(|\.place\(',t)); d=len(re.findall(r'IfLists|simplify_if_head',t))
    if a+b+c+d:
        print(f'| `{f}.rs` | {a} | {b} | {c} | {d} |')
        for i,x in enumerate((a,b,c,d)): tot[i]+=x
print(f'| total | {tot[0]} | {tot[1]} | {tot[2]} | {tot[3]} |')
