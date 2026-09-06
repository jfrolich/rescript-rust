#!/usr/bin/env python3
"""Validate actual action accounting and aggregate per-context probe records."""
import re, ast, json
from pathlib import Path
D=Path('/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round')
names=['entries','outer_scopes','scope_ns','scope_allocated_nodes','endpoint_map_len_sum','endpoint_map_capacity_sum','endpoint_map_len_max','row_marker_hits','node_cache_probes','node_cache_hits','variant_marker_hits','identity_actions','var_actions','univar_actions','arrow_actions','tuple_actions','constr_actions','object_actions','field_actions','nil_actions','poly_actions','variant_actions','package_actions','link_actions','forget_actions','selected_container_elements','path_bearing_actions','arrow_elements','labeled_arrow_elements','unused29','unused30','unused31']
result={}
for w,pos in [(1,2),(12,4)]:
    records=[];nodes=0
    for match in re.finditer(r'\[architecture-copy\] nodes=(\d+) counters=(\[[^\n]*\])',(D/f'graph/logs/graph-1-{pos}-P-w{w}.log').read_text()):
        c=ast.literal_eval(match[2]);assert len(c)==32
        assert c[0]==c[7]+c[8] and c[0]==sum(c[11:25])+c[7]+c[9]+c[10]
        assert c[9]<=c[8] and c[28]<=c[27] and c[29:]==[0,0,0]
        records.append(c);nodes+=int(match[1])
    assert len(records)==3511
    totals=[sum(c[i] for c in records) if i!=6 else max(c[i] for c in records) for i in range(32)]
    result[w]=dict(contexts=len(records),nodes=nodes,**dict(zip(names,totals)))
(D/'graph/summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
