#!/usr/bin/env python3
"""One planned gate run, under the campaign heavy lock. Preserve all failures."""
from pathlib import Path
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
D = Path('/tmp/rescript-snapshot-projections-experiment')
os.environ['PATH'] = '/Users/jake/.cargo/bin:' + os.environ['PATH']
os.environ.pop('RUSTFLAGS', None)
rows = D / 'gates.jsonl'
assert not rows.exists(), 'Do not repeat final gates'

def run(name, args, timeout=600):
    with (D / f'logs/{name}.log').open('wb') as log:
        try:
            code = subprocess.run(args, cwd=ROOT, stdout=log, stderr=log, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            code = 124
    with rows.open('a') as f:
        f.write(json.dumps(dict(name=name, command=args, exit=code)) + '\n')
    print(name, code, flush=True)
    return code

for crate in ['compiler-rust', 'rewatch']:
    for release in [False, True]:
        args = ['cargo', 'build', '--locked', '--manifest-path', f'{crate}/Cargo.toml']
        if release:
            args.append('--release')
        if run(f'build-{crate}-' + ('release' if release else 'default'), args):
            raise SystemExit('Build failed; preserve and investigate')
for release in [False, True]:
    args = ['cargo', 'test', '--manifest-path', 'compiler-rust/Cargo.toml']
    if release:
        args.append('--release')
    label = 'release' if release else 'default'
    if run(f'compiler-{label}', args + ['--', '--show-output']):
        for target in [['--bins'], ['--test', 'comptime_tests'], ['--doc']]:
            run(f'compiler-{label}-remaining-{target[-1].lstrip("-")}', args + target + ['--', '--show-output'])
for release in [False, True]:
    run('rewatch-' + ('release' if release else 'default'), ['cargo', 'test', '--manifest-path', 'rewatch/Cargo.toml'] + (['--release'] if release else []) + ['--', '--show-output'])
for folder in ['diffs', 'ocaml', 'rust']:
    path = ROOT / '.parity-cache/tests' / folder
    if path.exists():
        for p in path.rglob('*'):
            if p.is_file():
                p.unlink()
for name, args in [
    ('typed', ['./scripts/test_typedtree_parity.sh', '--release']),
    ('raw', ['./scripts/test_lambda_parity.sh', '--release', '--raw']),
    ('optimized', ['./scripts/test_lambda_parity.sh', '--release']),
    ('js', ['./scripts/test_js_output_parity.sh', '--release']),
    ('diagnostics', ['./scripts/test_error_output_parity.sh', '--release']),
    ('external-js', ['./scripts/test_js_output_parity.sh', '--release', '--with-external']),
]:
    run(name, args, 600)
