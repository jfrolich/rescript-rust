#!/usr/bin/env python3
"""Fixed eight-pair analysis, no pooling with hyperfine or historical A."""
import json
import math
import statistics as s
from pathlib import Path

D = Path('/tmp/rescript-type-arg-experiment')
rows = [json.loads(line) for line in (D / 'runs.jsonl').read_text().splitlines()]
expected_order = [(p, v, w) for p in range(1, 9)
                  for w in ([1, 12] if p % 2 else [12, 1])
                  for v in (['C', 'D'] if p % 2 else ['D', 'C'])]
assert [(r['pair'], r['variant'], r['workers']) for r in rows] == expected_order
assert all(r['exit'] == 0 and r['compiled_3248'] and r['js_count'] == 5048
           and r['js_sha256'] == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
           for r in rows)

def summary(xs):
    return dict(mean=s.mean(xs), sd=s.stdev(xs), median=s.median(xs), min=min(xs), max=max(xs))

result = {}
for w in [1, 12]:
    group = {}
    for v in ['C', 'D']:
        sample = [r for r in rows if r['workers'] == w and r['variant'] == v]
        group[v] = dict(wall_seconds=summary([r['wall_ns']/1e9 for r in sample]))
        for metric in ['user', 'sys', 'maximum resident set size', 'instructions retired', 'cycles elapsed']:
            group[v][metric] = summary([r[metric] for r in sample])
    deltas = []
    for pair in range(1, 9):
        values = {r['variant']: r['wall_ns']/1e9 for r in rows if r['workers'] == w and r['pair'] == pair}
        deltas.append(values['D'] - values['C'])
    mean = s.mean(deltas)
    half = 2.364624251 * s.stdev(deltas) / math.sqrt(8)
    group['paired_D_minus_C_seconds'] = dict(samples=deltas, **summary(deltas), ci95=[mean-half, mean+half])
    group['mean_reduction_percent'] = -mean/group['C']['wall_seconds']['mean']*100
    result[str(w)] = group
(D / 'timing-summary.json').write_text(json.dumps(result, indent=2))
print(json.dumps(result, indent=2))
