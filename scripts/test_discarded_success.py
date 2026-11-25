#!/usr/bin/env python3
"""A discarded successful A must not affect A or its dependent B.

Build with: cargo build --manifest-path rewatch/Cargo.toml --features rescript-compiler/test-hooks
Then pass that executable and runtime explicitly. Each build has a 10-second bound.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rescript', required=True, type=Path)
    parser.add_argument('--runtime', required=True, type=Path)
    args = parser.parse_args()
    binary, runtime = args.rescript.resolve(), args.runtime.resolve()
    with tempfile.TemporaryDirectory(prefix='discarded-success-') as temporary:
        project = Path(temporary)
        (project / 'src').mkdir()
        (project / 'rescript.json').write_text(json.dumps({
            'name': 'discarded-success', 'sources': ['src'],
            'compiler-flags': ['-w +A', '-warn-error -A'],
            'package-specs': {'module': 'esmodule', 'in-source': True}, 'suffix': '.res.js',
        }))
        (project / 'src/A.res').write_text(
            'type t = {x: int}\nlet value: t = {x: 1}\n'
            '@deprecated("use value")\nlet old = value\n')
        (project / 'src/B.res').write_text('let result = A.old.x\n')
        env = dict(os.environ, RESCRIPT_RUNTIME=str(runtime), RESCRIPT_FULL_BUILD='1',
                   RESCRIPT_COMPILER_COUNTERS='1', NO_COLOR='1')
        for key in ('RESCRIPT_CHECK_MODE', 'RESCRIPT_TEST_DISCARD_UNIT', 'RESCRIPT_SIGNATURE_CHECK'):
            env.pop(key, None)
        snapshots = []
        for workers in (1, 4):
            for forced in (False, True):
                case = f'{workers}-{"explain" if forced else "discard"}'
                dump = project / f'dump-{case}'
                run_env = dict(env, RAYON_NUM_THREADS=str(workers))
                if forced:
                    run_env['RESCRIPT_CHECK_MODE'] = 'explain'
                else:
                    run_env['RESCRIPT_TEST_DISCARD_UNIT'] = 'A'
                subprocess.run([str(binary), 'clean'], cwd=project, env=run_env,
                               capture_output=True, check=True, timeout=10)
                built = subprocess.run([str(binary), 'build', '--dump', 'sig', '--dump-dir', str(dump)],
                                       cwd=project, env=run_env, capture_output=True, timeout=10)
                assert built.returncode == 0, built.stdout + built.stderr
                reruns = re.search(rb'\[compiler-counter\] explain_reruns=(\d+)', built.stderr)
                assert reruns and int(reruns[1]) == (0 if forced else 1), built.stderr
                signatures = {str(p.relative_to(dump)): p.read_bytes() for p in dump.rglob('*.sig')}
                assert any(Path(name).name == 'A.res.sig' for name in signatures), signatures.keys()
                javascript = {name: (project / f'src/{name}.res.js').read_bytes() for name in ('A', 'B')}
                log = (project / 'lib/rescript/.compiler.log').read_bytes()
                # Start/Done are build timestamps, not diagnostic bytes.
                warnings = re.sub(rb'(?m)^#(?:Start|Done)\(\d+\)\n', b'', log)
                assert b'use value' in warnings, warnings
                snapshots.append((signatures, javascript, warnings))
                for field, actual, expected in zip(('signatures', 'javascript', 'warnings'), snapshots[-1], snapshots[0]):
                    assert actual == expected, f'{case} {field}:\n{actual!r}\n!=\n{expected!r}'
                print(f'{case}: A signature, A/B JavaScript and warnings byte-equal; explain_reruns={int(reruns[1])}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
