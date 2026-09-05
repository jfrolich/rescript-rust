#!/usr/bin/env python3
"""Parse Apple sample call trees; inclusive union avoids recursive double counting."""
from pathlib import Path
from collections import Counter
import json
import re
D = Path('/tmp/rescript-descriptor-snapshots')
OUT = Path('projects/in-process-performance/descriptor-snapshots-5dc38')
patterns = ['TypeDesc$u20$as$u20$core..clone..Clone', 'type_application', 'lower_args', 'deep_occur', 'substitute_type_expr_path', 'rewrite_type_expr_by_path_prefix', 'unify', '_platform_memmove', 'mi_malloc', 'mi_free']
results = {}
for workers in [1, 12]:
    stack = []
    exclusive = Counter()
    inclusive = Counter()
    denom = 0
    worker = False
    def finish():
        depth, count, name, children = stack.pop()
        residual = count - children
        assert residual >= 0, (name, residual)
        if worker:
            exclusive[name.split('  (in ', 1)[0]] += residual
            for pattern in patterns:
                if pattern in name and not any(pattern in entry[2] for entry in stack):
                    inclusive[pattern] += count
        if stack: stack[-1][3] += count
    active = False
    with (D/f'sample-D-w{workers}.txt').open() as f:
        for line in f:
            if line.startswith('Call graph:'): active=True; continue
            if line.startswith('Total number in stack'): break
            if not active: continue
            m = re.match(r'^([ +!|:.,`]*)(\d+) (.*)$', line)
            if not m: continue
            depth, count, name = len(m[1]), int(m[2]), m[3]
            while stack and stack[-1][0] >= depth: finish()
            if 'Thread_' in name:
                worker = 'rewatch-in-process-worker' in name or 'rewatch-runtime-in-process' in name
                if worker: denom += count
            stack.append([depth, count, name, 0])
    while stack: finish()
    assert sum(exclusive.values()) == denom
    results[workers] = dict(worker_samples=denom, exclusive_total=sum(exclusive.values()),
        exclusive_top=exclusive.most_common(40), inclusive_union=dict(inclusive),
        selected_exclusive={p:sum(n for name,n in exclusive.items() if p in name) for p in patterns},
        allocator_exclusive=sum(n for name,n in exclusive.items() if name.startswith(('mi_', '_mi_'))))
(OUT/'samples.json').write_text(json.dumps(results, indent=2)+'\n')
print(json.dumps(results, indent=2))
