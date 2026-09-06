#!/usr/bin/env python3
"""Dedicated TypeArg C/D cohort. Run under the heavy lock, from repository root."""
import os
import json
from pathlib import Path
import runpy
import subprocess
import sys

os.environ['MEASUREMENT_DIR'] = '/tmp/rescript-type-arg-experiment'
import measurement_rebaseline as m

mode = sys.argv[1]
if mode == 'screen':
    assert not list(m.D.glob('screen-*.json')), 'Never rerun screening'
    for w in [1, 12]:
        for v in ['C', 'D']:
            subprocess.run(['hyperfine', '--runs', '2', '--prepare',
                f'{m.D}/bin/rescript-{v} clean {m.WEB}',
                '--conclude', f'python3 {__file__} screen-validate {v} {w}', '--export-json',
                str(m.D / f'screen-{v}-w{w}.json'),
                '/usr/bin/time -lp ' + ' '.join(m.command(v)) +
                f' > {m.D}/logs/screen-{v}-w{w}-current.log 2>&1'],
                env=m.env(v, w), check=True)
elif mode == 'screen-validate':
    v, w = sys.argv[2], int(sys.argv[3])
    rows_path = m.D / 'screen-runs.jsonl'
    rows = [json.loads(x) for x in rows_path.read_text().splitlines()] if rows_path.exists() else []
    n = 1 + sum(r['variant'] == v and r['workers'] == w for r in rows)
    assert n <= 2
    text = (m.D / f'logs/screen-{v}-w{w}-current.log').read_text()
    (m.D / f'logs/screen-{v}-w{w}-{n}.log').write_text(text)
    count, digest, manifest = m.outputs()
    (m.D / f'screen-{v}-w{w}-{n}-js.json').write_text(json.dumps(manifest, sort_keys=True))
    row = dict(variant=v, workers=w, repetition=n, js_count=count, js_sha256=digest,
               compiled_3248='Compiled 3248 modules' in text)
    with rows_path.open('a') as f:
        f.write(json.dumps(row) + '\n')
    assert count == 5048 and row['compiled_3248'] and digest == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
elif mode == 'paired':
    assert not (m.D / 'runs.jsonl').exists(), 'Never append a second cohort'
    for pair in range(1, 9):
        for w in ([1, 12] if pair % 2 else [12, 1]):
            for pos, v in enumerate(['C', 'D'] if pair % 2 else ['D', 'C'], 1):
                row = m.run(mode, pair, pos, v, w)
                assert row['js_sha256'] == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
elif mode == 'freeze-inputs':
    # Separate from the pre-probe inventory; full gates create source mirrors
    # and Cargo outputs through the existing linked compiler package.
    target = m.D / 'timing-inputs-before.json'
    assert not target.exists()
    m.clean('C', 1)
    target.write_text(json.dumps(m.inputs(), sort_keys=True))
elif mode == 'verify-timing':
    before = json.loads((m.D / 'timing-inputs-before.json').read_text())
    after = m.inputs()
    (m.D / 'timing-inputs-after.json').write_text(json.dumps(after, sort_keys=True))
    packages = ['@rescript/react', '@rescript/belt', '@jfrolich/ppx-spice',
                'rescript-debounce-react', 'rescript-nodejs', 'rescript-debounce',
                'bs-css', 'bs-css-dom', '@tella-fusion/webapp',
                '@tella-fusion/webapp/packages/tella-std',
                '@tella-fusion/webapp/node_modules/rescript-webapi']
    metadata = {str(m.T / 'node_modules' / p / 'lib/bs/compiler-info.json') for p in packages}
    # Written after compilation by sourcedirs.rs:74-77 / build.rs:517-518.
    # Consumed by editor analysis/reanalyze, not by compiler or build input lookup.
    metadata.add(str(m.T / 'node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json'))
    changed = sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))
    unexpected = [p for p in changed if p not in metadata]
    report = dict(before_count=len(before), after_count=len(after),
                  generated_metadata=[p for p in changed if p in metadata], unexpected=unexpected)
    (m.D / 'timing-input-verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report))
    assert not unexpected, 'Input drift; preserve evidence and stop'
elif mode == 'probe':
    m.clean('C', 1)
    cmd = m.command('C')
    cmd[0] = str(m.D / 'probe-source/rewatch/target/release/rescript')
    with (m.D / 'logs/type-arg-probe.log').open('wb') as f:
        p = subprocess.run(cmd, env=m.env('C', 1), stdout=f, stderr=f, timeout=180)
    n, h, _ = m.outputs()
    print(p.returncode, n, h)
    assert p.returncode == 0 and n == 5048 and h == '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
else:
    runpy.run_path(str(Path(__file__).with_name('measurement_rebaseline.py')), run_name='__main__')
