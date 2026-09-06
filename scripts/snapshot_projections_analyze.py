#!/usr/bin/env python3
"""Fixed sample order and separate D/E and A/E statistics; no pooling."""
import json
import math
from pathlib import Path
import statistics as s
D = Path('/tmp/rescript-snapshot-projections-experiment')
rows = [json.loads(line) for line in (D / 'runs.jsonl').read_text().splitlines()]
expected = [('paired', p, v, w) for p in range(1, 9)
            for w in ([1, 12] if p % 2 else [12, 1])
            for v in (['D', 'E'] if p % 2 else ['E', 'D'])]
expected += [('historical', p, v, 12) for p in range(1, 9)
             for v in (['A', 'E'] if p % 2 else ['E', 'A'])]
assert [(r['stage'], r['pair'], r['variant'], r['workers']) for r in rows] == expected
assert all(r['exit'] == 0 and r['compiled_3248'] and r['js_count'] == 5048
           and r['js_sha256'] == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
           for r in rows)
def summary(xs):
    return dict(mean=s.mean(xs), sd=s.stdev(xs), median=s.median(xs), min=min(xs), max=max(xs))
result = {}
for stage, control, workers in [('paired', 'D', [1, 12]), ('historical', 'A', [12])]:
    cohort = [r for r in rows if r['stage'] == stage]
    for w in workers:
        group = {}
        for v in [control, 'E']:
            sample = [r for r in cohort if r['workers'] == w and r['variant'] == v]
            group[v] = dict(wall_seconds=summary([r['wall_ns']/1e9 for r in sample]))
            for metric in ['user', 'sys', 'maximum resident set size', 'instructions retired', 'cycles elapsed']:
                group[v][metric] = summary([r[metric] for r in sample])
        deltas = []
        for pair in range(1, 9):
            values = {r['variant']:r['wall_ns']/1e9 for r in cohort if r['workers'] == w and r['pair'] == pair}
            deltas.append(values['E'] - values[control])
        mean = s.mean(deltas)
        half = 2.364624251 * s.stdev(deltas) / math.sqrt(8)
        group['paired_E_minus_control_seconds'] = dict(samples=deltas, **summary(deltas), ci95=[mean-half, mean+half])
        group['mean_reduction_percent'] = -mean/group[control]['wall_seconds']['mean']*100
        result[f'{stage}-w{w}'] = group
(D / 'timing-summary.json').write_text(json.dumps(result, indent=2))
print(json.dumps(result, indent=2))
