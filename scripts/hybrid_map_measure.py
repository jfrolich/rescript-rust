#!/usr/bin/env python3
"""Dedicated hybrid B/C cohort. Run under the heavy lock, from repository root."""
import os
from pathlib import Path
import runpy
import subprocess
import sys

os.environ['MEASUREMENT_DIR'] = '/tmp/rescript-hybrid-map-experiment'
import measurement_rebaseline as m

mode = sys.argv[1]
if mode == 'screen':
    for w in [1, 12]:
        for v in ['B', 'C']:
            subprocess.run(['hyperfine', '--runs', '2', '--prepare',
                f'{m.D}/bin/rescript-{v} clean {m.WEB}', '--export-json',
                str(m.D / f'screen-{v}-w{w}.json'), ' '.join(m.command(v))],
                env=m.env(v, w), check=True)
elif mode == 'paired':
    assert not (m.D / 'runs.jsonl').exists(), 'Never append a second cohort'
    for pair in range(1, 9):
        for w in ([1, 12] if pair % 2 else [12, 1]):
            for pos, v in enumerate(['B', 'C'] if pair % 2 else ['C', 'B'], 1):
                row = m.run(mode, pair, pos, v, w)
                assert row['js_sha256'] == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
elif mode == 'probe':
    m.clean('B', 1)
    cmd = m.command('B')
    cmd[0] = str(m.D / 'probe-source/rewatch/target/release/rescript')
    with (m.D / 'logs/map-probe.log').open('wb') as f:
        p = subprocess.run(cmd, env=m.env('B', 1), stdout=f, stderr=f, timeout=180)
    n, h, _ = m.outputs()
    print(p.returncode, n, h)
    assert p.returncode == 0 and n == 5048 and h == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
else:
    runpy.run_path(str(Path(__file__).with_name('measurement_rebaseline.py')), run_name='__main__')
