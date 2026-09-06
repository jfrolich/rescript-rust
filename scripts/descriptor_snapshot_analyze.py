#!/usr/bin/env python3
"""Aggregate per-context probe rows without treating logical bytes as allocator data."""
import collections
import json
import difflib
import subprocess
from pathlib import Path
D = Path('/tmp/rescript-descriptor-snapshots')
OUT = Path('projects/in-process-performance/descriptor-snapshots-5dc38')
OUT.mkdir(exist_ok=True)
fields = ['calls', 'inline_bytes', 'vec_requests', 'vec_bytes', 'string_requests', 'string_bytes', 'box_requests', 'box_bytes']
for workers, pos in [(1, 2), (12, 4)]:
    sites = collections.defaultdict(lambda: [0]*8)
    variants = collections.defaultdict(lambda: [0]*8)
    for variant in ['Tvar', 'Tarrow', 'Ttuple', 'Tconstr', 'Tobject', 'Tfield', 'Tnil', 'Tlink', 'Tsubst', 'Tvariant', 'Tunivar', 'Tpoly', 'Tpackage']:
        variants[variant] = [0]*8
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
    # Preserve the actual probe location and map unchanged caller lines to D.
    source_maps = {}
    for row in rows:
        file = row['file']
        if file not in source_maps:
            old = subprocess.check_output(['git', 'show', f'5dc38ba2154e158d43436ada2142a13eef9f2c8c:{file}']).decode().splitlines()
            source = D/'probe-context.rs' if file == 'compiler-rust/src/types/context.rs' else D/'probe-source'/file
            probe = source.read_text().splitlines()
            mapping = {}
            for block in difflib.SequenceMatcher(None, old, probe, autojunk=False).get_matching_blocks():
                for i in range(block.size): mapping[block.b+i+1] = block.a+i+1
            source_maps[file] = mapping
            # Every reported immediate location must actually call get_desc.
            source_maps[(file, 'text')] = probe
        assert 'get_desc(' in source_maps[(file, 'text')][row['line']-1]
        row['source_line'] = source_maps[file][row['line']]
    rows.sort(key=lambda r: (-r['nested_bytes'], -r['calls'], r['file'], r['line']))
    totals = [sum(n[i] for n in variants.values()) for i in range(8)]
    result = dict(contexts=contexts, totals=record(totals), variants={k:record(n) for k,n in sorted(variants.items())}, sites=rows)
    (OUT / f'counts-w{workers}.json').write_text(json.dumps(result, indent=2)+'\n')
    print(workers, contexts, record(totals))
    for row in rows[:15]: print(row)
