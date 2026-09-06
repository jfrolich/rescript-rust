#!/usr/bin/env python3
"""Produce lightweight aggregates from private raw measurement artifacts."""
import ast,json,re,statistics as s
from collections import defaultdict
from pathlib import Path
from measurement_rebaseline import D
rows=[json.loads(x) for x in (D/'runs.jsonl').read_text().splitlines()]
result={'runs':{},'paired':{},'profiles':{},'samples':{},'trace':{}}
for stage in ['paired','scaling','confirm']:
 for v in ['A','B']:
  for w in sorted({x['workers'] for x in rows}):
   rr=[x for x in rows if (x['stage'],x['variant'],x['workers'])==(stage,v,w)]
   if not rr:continue
   z=[x['wall_ns']/1e9 for x in rr]
   result['runs'][f'{stage}-{v}-w{w}']=dict(n=len(z),mean=s.mean(z),sd=s.stdev(z),median=s.median(z),min=min(z),max=max(z),user=s.mean(x['user'] for x in rr),system=s.mean(x['sys'] for x in rr),rss=s.mean(x['maximum resident set size'] for x in rr),instructions=s.mean(x['instructions retired'] for x in rr),cycles=s.mean(x['cycles elapsed'] for x in rr))
for w in [1,12]:
 deltas=[]
 for p in range(1,9):
  a={x['variant']:x['wall_ns']/1e9 for x in rows if x['stage']=='paired' and x['workers']==w and x['pair']==p}
  deltas.append(a['B']-a['A'])
 mean=s.mean(deltas);h=2.364624251*s.stdev(deltas)/8**.5
 result['paired'][w]=dict(deltas=deltas,mean=mean,ci95=[mean-h,mean+h])
for w in [1,12]:
 for variant,suffix in [('A',''),('B','-B')]:
  text=(D/f'logs/profile-phases{suffix}-w{w}.log').read_text()
  phases={m[1]:float(m[2]) for m in re.finditer(r'\[phase-timing\] phase=(\w+) ms=([\d.]+)',text)}
  modules=defaultdict(dict)
  for line in text.splitlines():
   if line.startswith(('[module-timing]','[module-js-timing]')):
    fields=dict(re.findall(r'(\w+)=([^ ]+)',line));name=fields.pop('module');fields.pop('package')
    prefix='js_' if line.startswith('[module-js') else ''
    modules[name].update({prefix+k:float(v) for k,v in fields.items()})
  distributions={}
  for field in ['wall_ms','typecheck_ms','lambda_ms','lambda_optimization_ms','js_wall_ms','js_write_ms','js_codegen_ms']:
   vals=sorted(m.get(field,0) for m in modules.values()); n=len(vals)
   distributions[field]=dict(sum=sum(vals),p50=vals[n//2],p90=vals[int(n*.9)],p99=vals[int(n*.99)],max=max(vals),top=sorted([(k,v.get(field,0)) for k,v in modules.items()],key=lambda x:x[1],reverse=True)[:10])
  result['profiles'][f'{variant}-w{w}']=dict(phases=phases,distributions=distributions)
 # Sampling: residual counts avoid double-counting recursive inclusive stacks.
 text=(D/f'profile-sample-full-w{w}.txt').read_text().split('Call graph:',1)[1].split('Total number in stack',1)[0]
 stack=[]; top=defaultdict(int);denom=0;worker=False
 def finish():
  depth,count,name,children=stack.pop()
  residual=count-children
  if worker and residual>0:top[name.split('  (in ',1)[0]]+=residual
  if stack:stack[-1][3]+=count
 for line in text.splitlines():
  m=re.match(r'^([ +!|:.,`]*)(\d+) (.*)$',line)
  if not m:continue
  depth=len(m[1]);count=int(m[2]);name=m[3]
  while stack and stack[-1][0]>=depth:finish()
  if 'Thread_' in name:
   worker=('rewatch-in-process-worker' in name or 'rewatch-runtime-in-process' in name)
   if worker:denom+=count
  stack.append([depth,count,name,0])
 while stack:finish()
 result['samples'][w]=dict(worker_samples=denom,exclusive_total=sum(top.values()),top=sorted(top.items(),key=lambda x:x[1],reverse=True)[:40],memmove=sum(v for k,v in top.items() if '_platform_memmove' in k),allocator=sum(v for k,v in top.items() if k.startswith(('mi_','_mi_'))))
 # Dispatcher trace: critical signature DAG lower bound with observed task service
 # (queue residence included). This is NOT the full JS metadata critical path.
 text=(D/f'logs/profile-census-trace-w{w}.log').read_text();deps={};events=defaultdict(dict)
 for line in text.splitlines():
  m=re.match(r'\[measurement-deps\] module=(\S+) deps=(.*)',line)
  if m:deps[m[1]]=set(ast.literal_eval(m[2])) if m[2]!='{}' else set()
  m=re.match(r'\[measurement-event\] ns=(\d+) event=(\w+) module=(\S+)',line)
  if m:events[m[3]][m[2]]=int(m[1])/1e6
 memo={}
 def longest(name,visiting=frozenset()):
  if name in memo:return memo[name]
  if name in visiting:raise RuntimeError('dependency cycle')
  e=events.get(name,{})
  own=max(0,e.get('sig',e.get('pre',e.get('end',0)))-e.get('startpre',0))
  choices=[longest(d,visiting|{name}) for d in deps.get(name,set()) if d in deps]
  best=max(choices,default=(0,[]),key=lambda x:x[0]);memo[name]=(best[0]+own,best[1]+[name]);return memo[name]
 longest_path=max((longest(n) for n in deps),key=lambda x:x[0])
 intervals=[]
 for name,e in events.items():
  if 'startpre' in e:intervals.append((e['startpre'],e.get('pre',e.get('end',e['startpre']))))
  if 'startjs' in e:intervals.append((e['startjs'],e.get('end',e['startjs'])))
 end=max(b for a,b in intervals);busy=sum(b-a for a,b in intervals)
 result['trace'][w]=dict(signature_dag_bound_ms=longest_path[0],path=longest_path[1],scheduler_end_ms=end,scheduled_slot_ms=busy,scheduled_utilization=busy/(w*end),largest_pre=sorted([(n,e.get('pre',e.get('end',0))-e['startpre']) for n,e in events.items() if 'startpre' in e],key=lambda x:x[1],reverse=True)[:10])
(D/'aggregates.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
