#!/usr/bin/env python3
"""Aggregate per-context probe rows without treating logical bytes as allocator data."""
import collections
import json
from pathlib import Path
D = Path('/tmp/rescript-descriptor-snapshots')
OUT = Path('projects/in-process-performance/descriptor-snapshots-5dc38')
OUT.mkdir(exist_ok=True)
fields = ['calls', 'inline_bytes', 'vec_requests', 'vec_bytes', 'string_requests', 'string_bytes', 'box_requests', 'box_bytes']
for workers, pos in [(1, 2), (12, 4)]:
    sites = collections.defaultdict(lambda: [0]*8)
    variants = collections.defaultdict(lambda: [0]*8)
    contexts = 0
    for line in (D / f'logs/diagnostic-1-{pos}-P-w{workers}.log').read_text().splitlines():
        if line.startswith('DESC_CONTEXT '): contexts += 1
        if not line.startswith('DESC_SNAPSHOT\t'): continue
        _, file, row, col, variant, raw = line.split('\t')
        # Compiler crate can be recorded as an absolute source path by Cargo.
        file = 'compiler-rust/src/' + file.split('/src/', 1)[1] if '/src/' in file else 'compiler-rust/' + file
        key = (file, int(row), int(col), variant)
        n = json.loads(raw)
        for i, val in enumerate(n): sites[key][i] += val; variants[variant][i] += val
    def record(n):
        return dict(zip(fields, n), nested_bytes=n[3]+n[5]+n[7])
    rows = [dict(file=k[0], line=k[1], column=k[2], variant=k[3], **record(n)) for k,n in sites.items()]
    rows.sort(key=lambda r: (-r['nested_bytes'], -r['calls'], r['file'], r['line']))
    totals = [sum(n[i] for n in variants.values()) for i in range(8)]
    result = dict(contexts=contexts, totals=record(totals), variants={k:record(n) for k,n in sorted(variants.items())}, sites=rows)
    (OUT / f'counts-w{workers}.json').write_text(json.dumps(result, indent=2)+'\n')
    print(workers, contexts, record(totals))
    for row in rows[:15]: print(row)
