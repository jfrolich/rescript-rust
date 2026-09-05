#!/usr/bin/env python3
"""Two separately registered full-duration sample runs on immutable D."""
import os
os.environ['MEASUREMENT_DIR'] = '/tmp/rescript-descriptor-snapshots'
import measurement_rebaseline as m
import json
import subprocess
import time

assert not (m.D / 'profile-runs.json').exists()
m.clean('D', 1)
before = m.inputs()
(m.D / 'profile-inputs-before.json').write_text(json.dumps(before, sort_keys=True))
rows = []
try:
    for workers, duration in [(1, 30), (12, 10)]:
        m.clean('D', workers)
        name = f'sample-D-w{workers}'
        with (m.D / f'logs/{name}.log').open('wb') as log:
            start = time.perf_counter_ns()
            p = subprocess.Popen(m.command('D'), env=m.env('D', workers), stdout=log, stderr=log)
            sample_start = time.perf_counter_ns()
            sample = subprocess.run(['/usr/bin/sample', str(p.pid), str(duration), '1', '-file', str(m.D/f'{name}.txt')], stdout=log, stderr=log, timeout=45)
            code = p.wait(timeout=180)
            end = time.perf_counter_ns()
        count, digest, manifest = m.outputs()
        (m.D/f'{name}-js.json').write_text(json.dumps(manifest, sort_keys=True))
        row = dict(workers=workers, exit=code, sample_exit=sample.returncode,
                   wrapper_ns=end-start, sample_launch_delay_ns=sample_start-start,
                   js_count=count, js_sha256=digest,
                   compiled_3248=b'Compiled 3248 modules' in (m.D/f'logs/{name}.log').read_bytes())
        rows.append(row)
        (m.D/'profile-runs.json').write_text(json.dumps(rows, indent=2))
        print(row, flush=True)
        assert code == sample.returncode == 0 and count == 5048 and row['compiled_3248']
        assert digest == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
finally:
    after = m.inputs()
    (m.D/'profile-inputs-after.json').write_text(json.dumps(after, sort_keys=True))
    changed = sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))
    (m.D/'profile-input-differences.json').write_text(json.dumps(changed, indent=2))
    subprocess.run(['python3', 'scripts/descriptor_snapshot_measure.py', 'restore'], check=True)
# Only previously individually proven build metadata may differ.
allowed = json.loads((m.D/'input-verification.json').read_text())['changed']
assert all(p in allowed for p in changed)
