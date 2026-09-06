#!/usr/bin/env python3
"""Summarize fixed cohorts and exclusive sampled stacks. Never reruns builds."""
import json
import re
import statistics as s
from collections import Counter, defaultdict
from pathlib import Path
D = Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round')
rows = [json.loads(x) for x in (D/'runs.jsonl').read_text().splitlines()]
assert len(rows) == 32
expected = [(p,w,v) for p in range(1,9) for w in ([1,12] if p%2 else [12,1]) for v in (['A','D'] if p%2 else ['D','A'])]
assert [(r['pair'],r['workers'],r['variant']) for r in rows] == expected
assert all(r['exit']==0 and r['compiled_3248'] and r['js_count']==5048 and r['js_sha256']=='1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49' for r in rows)
def stats(xs):
    return dict(n=len(xs),mean=s.mean(xs),sd=s.stdev(xs),min=min(xs),max=max(xs),median=s.median(xs))
result = dict(cells={},paired={},screens={},phases={},samples={})
for w in (1,12):
    for v in ('A','D'):
        rr = [r for r in rows if (r['workers'],r['variant'])==(w,v)]
        result['cells'][f'{v}-w{w}'] = {k:stats([r[k]/1e9 if k=='wall_ns' else r[k] for r in rr]) for k in ['wall_ns','user','sys','maximum resident set size','instructions retired','cycles elapsed']}
        result['screens'][f'{v}-w{w}'] = json.loads((D/f'screen-{v}-w{w}.json').read_text())['results'][0]
    deltas=[]
    for p in range(1,9):
        pair={r['variant']:r['wall_ns']/1e9 for r in rows if (r['workers'],r['pair'])==(w,p)}
        deltas.append(pair['D']-pair['A'])
    half=2.364624251*s.stdev(deltas)/8**.5
    result['paired'][w]=dict(deltas=deltas,mean=s.mean(deltas),ci95=[s.mean(deltas)-half,s.mean(deltas)+half])

for v in ('A','D'):
  for w in (1,12):
    key=f'{v}-w{w}'
    text=(D/f'logs/phases-{key}.log').read_text()
    phases={m[1]:float(m[2]) for m in re.finditer(r'\[phase-timing\] phase=(\w+) ms=([\d.]+)',text)}
    modules=defaultdict(dict)
    for line in text.splitlines():
      if line.startswith(('[module-timing]','[module-js-timing]')):
        fields=dict(re.findall(r'(\w+)=([^ ]+)',line));name=fields.pop('module');fields.pop('package')
        prefix='js_' if line.startswith('[module-js') else ''
        modules[name].update({prefix+k:float(value) for k,value in fields.items()})
    result['phases'][key]=dict(phases=phases,modules=modules)
    stack=[]; role='other'; exclusive=defaultdict(Counter);semantic=defaultdict(Counter); mechanism=defaultdict(Counter);total=Counter()
    def finish():
      depth,count,name,children=stack.pop()
      residual=count-children
      assert residual>=0
      leaf=name.split('  (in ',1)[0]
      if residual:
        exclusive[role][leaf]+=residual
        chain=' '.join(x[2] for x in stack)+' '+name
        wait=any(p in leaf for p in ('__ulock_wait','__psynch_cvwait','__psynch_mutexwait','semaphore_wait','__semwait_signal','kevent','mach_msg2_trap','__workq_kernreturn','swtch_pri','thread_switch'))
        mech=('blocking' if wait else 'allocator' if leaf.startswith(('mi_','_mi_')) else 'memory_copy' if any(p in leaf for p in ('memmove','memcpy','memset','bzero')) else 'refcount' if 'Arc' in leaf and any(p in leaf for p in ('clone','drop','release')) else 'drop' if 'drop' in leaf else 'other_running_or_unknown')
        mechanism[role][mech]+=residual
        # Assign once using nearest named semantic ancestor. Mechanisms remain a separate partition.
        family='other'
        if wait: family='blocking'
        else:
          for frame in [name]+[x[2] for x in reversed(stack)]:
            if any(p in frame for p in ('copy_type_cached','instance_poly','ctype::instance','ctype..instance')): family='type_instancing';break
            if any(p in frame for p in ('subst_identity','substitute_type_expr_path','rewrite_type_expr_by_path_prefix','subst_type')): family='type_substitution';break
            if any(p in frame for p in ('portable_types','internalize')): family='portable';break
            if any(p in frame for p in ('env_lazy','persistent_env','types::env::','types..env..')): family='env';break
            if any(p in frame for p in ('translcore','translmod','raw_lambda','lambda::lower','lambda..lower')): family='raw_lower';break
            if any(p in frame for p in ('types::ctype','types..ctype','types::typecore','types..typecore','types::typemod','types..typemod')): family='other_typecheck';break
            if any(p in frame for p in ('lambda::','lambda..','js_ir::','js_ir..')): family='other_backend';break
        semantic[role][family]+=residual
      if stack:stack[-1][3]+=count
    active=False
    for line in (D/f'sample-{key}.txt').read_text().splitlines():
      if line.startswith('Call graph:'):active=True;continue
      if line.startswith('Total number in stack'):break
      if not active:continue
      match=re.match(r'^([ +!|:.,`]*)(\d+) (.*)$',line)
      if not match:continue
      depth,count,name=len(match[1]),int(match[2]),match[3]
      while stack and stack[-1][0]>=depth:finish()
      if 'Thread_' in name:
        role='compiler_worker' if 'rewatch-in-process-worker' in name or 'rewatch-runtime-in-process' in name else 'other_thread'
        total[role]+=count
      stack.append([depth,count,name,0])
    while stack:finish()
    assert all(sum(exclusive[k].values())==n==sum(semantic[k].values())==sum(mechanism[k].values()) for k,n in total.items())
    result['samples'][key]=dict(total=total,semantic=semantic,mechanism=mechanism,exclusive_top={k:c.most_common(60) for k,c in exclusive.items()})
(D/'analysis.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('phases','samples','screens')},indent=2))
for key,r in result['phases'].items():print(key,r['phases'])
for key,r in result['samples'].items():print(key,r['total'],r['semantic'],r['mechanism'])
