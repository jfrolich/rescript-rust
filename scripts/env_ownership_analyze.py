#!/usr/bin/env python3
"""Analyze all four registered rows without adding or excluding observations."""
import collections,json,re
from pathlib import Path
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/env-ownership');R=D/'runs'
rows=[json.loads(x) for x in (R/'runs.jsonl').read_text().splitlines()]
assert [(r['variant'],r['workers']) for r in rows]==[('D',1),('P',1),('D',12),('P',12)]
summary={}
for row in rows:
 label=f"{row['variant']}-w{row['workers']}"
 path=R/f"logs/env-1-{row['position']}-{row['variant']}-w{row['workers']}.log"
 text=path.read_text(errors='replace');contexts=[];roots=[];teardown=[];phase=[];cleanup=[]
 for line in text.splitlines():
  if line.startswith('[env-ownership] '):contexts.append(json.loads(line.split('] ',1)[1]))
  elif line.startswith('[env-roots] '):roots.append(json.loads(line.split('] ',1)[1]))
  elif line.startswith('[env-teardown] '):teardown.append(json.loads(line.split('] ',1)[1]))
  elif line.startswith('[env-probe-cleanup] '):cleanup.append(int(line.split('] ',1)[1]))
  elif line.startswith('[module-timing] module=Layout__Types '):phase.append(line)
 total=collections.Counter();times=collections.defaultdict(lambda:[0,0,0]);layout=[]
 for context in contexts:
  c=context['stats'];t=context['times']
  assert c.get('query_requests',0)==context['unique_query_keys']+c.get('query_repeat_key',0)
  assert c.get('component_requests',0)==context['unique_component_keys']+c.get('component_repeat_key',0)
  assert all(0<=ex<=inc for n,inc,ex in t.values())
  assert sum(v[2] for k,v in t.items() if k!='outer_union')==t.get('outer_union',[0,0,0])[1]
  total.update(c)
  for k,vals in t.items():
   for i,v in enumerate(vals):times[k][i]+=v
  if context['module']=='Layout__Types':layout.append(context)
 if row['variant']=='P':
  assert contexts and layout and phase and len(contexts)==len(teardown)==len(cleanup)
  assert {x['phase'] for x in roots if x['module']=='Layout__Types'}>={'setup','after_typecheck','pre_js_exit','context_drop_entry'}
 else:assert not contexts
 item={'process':row,'contexts':len(contexts),'stats':dict(total),'times':dict(times),'context_fields_teardown_ns':sum(x['fields_ns'] for x in teardown),'instrumentation_cleanup_ns':sum(cleanup),'layout':layout,'layout_phase_lines':phase,'layout_roots':[x for x in roots if x['module']=='Layout__Types'],'layout_teardown':[x for x in teardown if x['module']=='Layout__Types']}
 summary[label]=item
 print(label, 'wall',row['wall_ns']/1e9, 'contexts',len(contexts))
 if contexts:
  for k in ['outer_union','resolve_type_item','all_persistent_clone','wrapper_payload_scan','wrapper_clone','wrapper_drop','decl_transport_clone','local_construction','qualification','raw_module_resolve','table_assembly','module_declaration_force','value_first_build','constructor_bucket_build','label_bucket_build']:
   n,inc,ex=times[k];print(f'  {k}: calls={n} inclusive_ms={inc/1e6:.3f} exclusive_ms={ex/1e6:.3f}')
  print('  Layout phases:',phase)
  print('  Layout query:',[x['times'].get('resolve_type_item') for x in layout])
(R/'summary.json').write_text(json.dumps(summary,indent=2))
