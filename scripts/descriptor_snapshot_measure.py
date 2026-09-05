#!/usr/bin/env python3
"""Fixed four diagnostic builds; invoke under campaign heavy lock."""
import os
os.environ['MEASUREMENT_DIR'] = '/tmp/rescript-descriptor-snapshots'
import measurement_rebaseline as m
import json
import subprocess
import shutil
import sys

EXPECTED = '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'
mode = sys.argv[1]
if mode == 'setup':
    assert not (m.D / 'backups.json').exists()
    assert subprocess.check_output(['git', '-C', str(m.T), 'rev-parse', 'HEAD']).decode().strip() == '66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa'
    (m.D / 'tella-status-before.txt').write_bytes(subprocess.check_output(['git', '-C', str(m.T), 'status', '--porcelain=v1']))
    subprocess.run([sys.executable, str(m.ROOT / 'scripts/measurement_rebaseline.py'), 'init'], check=True)
    for tool in ['bsc', 'rescript']:
        crate = 'compiler-rust' if tool == 'bsc' else 'rewatch'
        shutil.copy2(m.D / f'probe-source/{crate}/target/release/{tool}', m.D / f'bin/{tool}-P')
    (m.D / 'binary-hashes.json').write_text(json.dumps({p.name:m.sha(p) for p in sorted((m.D/'bin').iterdir())}, indent=2))
    m.clean('D', 1)
    (m.D / 'frozen-inputs.json').write_text(json.dumps(m.inputs(), sort_keys=True))
elif mode == 'run':
    assert not (m.D / 'runs.jsonl').exists(), 'No second cohort'
    assert json.loads((m.D / 'frozen-inputs.json').read_text()) == m.inputs(), 'Drift before cohort'
    for pos, (variant, workers) in enumerate([('D', 1), ('P', 1), ('D', 12), ('P', 12)], 1):
        row = m.run('diagnostic', 1, pos, variant, workers)
        assert row['js_sha256'] == EXPECTED
elif mode == 'verify':
    before = json.loads((m.D / 'frozen-inputs.json').read_text())
    after = m.inputs()
    (m.D / 'inputs-after.json').write_text(json.dumps(after, sort_keys=True))
    packages = ['@rescript/react', '@rescript/belt', '@jfrolich/ppx-spice',
                'rescript-debounce-react', 'rescript-nodejs', 'rescript-debounce',
                'bs-css', 'bs-css-dom', '@tella-fusion/webapp',
                '@tella-fusion/webapp/packages/tella-std',
                '@tella-fusion/webapp/node_modules/rescript-webapi']
    allowed = {str(m.T / 'node_modules' / p / 'lib/bs/compiler-info.json') for p in packages}
    allowed.add(str(m.T / 'node_modules/@tella-fusion/webapp/lib/bs/.sourcedirs.json'))
    changed = sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))
    result = dict(before_count=len(before), after_count=len(after), changed=changed,
                  unexpected=[p for p in changed if p not in allowed])
    (m.D / 'input-verification.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result))
    assert not result['unexpected']
elif mode == 'restore':
    subprocess.run([sys.executable, str(m.ROOT / 'scripts/measurement_rebaseline.py'), 'restore-generated'], check=True)
    backups = json.loads((m.D / 'backups.json').read_text())
    assert all(m.sha(m.T / p) == h for p, h in backups.items())
    status = subprocess.check_output(['git', '-C', str(m.T), 'status', '--porcelain=v1'])
    (m.D / 'tella-status-after.txt').write_bytes(status)
    assert status == (m.D / 'tella-status-before.txt').read_bytes()
else:
    raise SystemExit('setup|run|verify|restore')
