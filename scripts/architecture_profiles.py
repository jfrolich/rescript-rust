#!/usr/bin/env python3
"""Fixed separate sample/phase diagnostics; run under heavy lock."""
import os
os.environ['MEASUREMENT_DIR'] = '/Users/jake/.opensession/artifacts/rescript-performance-20260905/architecture-round'
import measurement_rebaseline as m
import json
import subprocess
import time

kind = __import__('sys').argv[1]
assert kind in ('sample', 'phases')
target = m.D / f'{kind}-runs.json'
assert not target.exists(), 'No repeated diagnostic cohort'
rows = []
for v, w in [('A', 1), ('D', 1), ('D', 12), ('A', 12)]:
    m.clean(v, w)
    name = f'{kind}-{v}-w{w}'
    e = m.env(v, w)
    if kind == 'phases':
        e.update(RESCRIPT_PHASE_TIMINGS='1', RESCRIPT_MODULE_TIMINGS='1', RESCRIPT_SCHEDULER_COUNTERS='1')
    load = os.getloadavg()
    with (m.D / f'logs/{name}.log').open('wb') as log:
        start = time.perf_counter_ns()
        p = subprocess.Popen(m.command(v), env=e, stdout=log, stderr=log)
        if kind == 'sample':
            attach = time.perf_counter_ns()
            sampler = subprocess.Popen(['/usr/bin/sample', str(p.pid), '35' if w == 1 else '15', '1', '-file', str(m.D / f'{name}.txt')], stdout=log, stderr=log)
        code = p.wait(timeout=180)
        process_end = time.perf_counter_ns()
        sample_code = sampler.wait(timeout=90) if kind == 'sample' else None
        wrapper_end = time.perf_counter_ns()
    count, digest, manifest = m.outputs()
    (m.D / f'{name}-js.json').write_text(json.dumps(manifest, sort_keys=True))
    row = dict(variant=v, workers=w, exit=code, sample_exit=sample_code,
        process_ns=process_end-start, wrapper_ns=wrapper_end-start,
        sample_launch_delay_ns=attach-start if kind == 'sample' else None,
        load=load, js_count=count, js_sha256=digest,
        compiled_3248='Compiled 3248 modules' in (m.D / f'logs/{name}.log').read_text())
    rows.append(row)
    target.write_text(json.dumps(rows, indent=2))
    print(row, flush=True)
    assert code == 0 and sample_code in (None, 0) and count == 5048 and row['compiled_3248']
    assert digest == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
