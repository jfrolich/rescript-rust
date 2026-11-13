#!/usr/bin/env python3
"""Compare Success/recheck diagnostics with forced Explain, without changing snapshots.

Each compiler process has a ten-second bound. The third run observes counters
separately so instrumentation cannot change the diagnostic comparison.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def check(binary, fixture):
    """Three bounded compiler runs per fixture, no shared mutable test state."""
    args = [str(binary), 'bsc', '-w', '+A', '-bs-jsx', '4', '-I',
            str(ROOT / 'packages/@rescript/belt/lib/rescript'), '-color', 'always', str(fixture)]
    env = dict(os.environ)
    env.pop('RESCRIPT_COMPILER_COUNTERS', None)
    env.pop('RESCRIPT_CHECK_MODE', None)
    success = subprocess.run(args, env=env, capture_output=True, timeout=10)
    explain = subprocess.run(args, env={**env, 'RESCRIPT_CHECK_MODE': 'explain'},
                             capture_output=True, timeout=10)
    counted = subprocess.run(args, env={**env, 'RESCRIPT_COMPILER_COUNTERS': '1'},
                             capture_output=True, timeout=10)
    errors = []
    if (success.returncode, success.stdout, success.stderr) != (
            explain.returncode, explain.stdout, explain.stderr):
        errors.append('Success and Explain diagnostics differ')
    found = re.search(rb'\[compiler-counter\] explain_reruns=(\d+)', counted.stderr)
    reruns = int(found[1]) if found else None
    expected = (fixture.parent.parent / 'expected' / (fixture.name + '.expected')).read_text()
    has_error = "We've found a bug for you!" in expected or 'Syntax error!' in expected
    found_attempts = re.search(rb'\[compiler-counter\] check_attempts=(\d+)', counted.stderr)
    attempts = int(found_attempts[1]) if found_attempts else None
    if attempts is None or reruns is None:
        errors.append('missing attempt counters')
    elif has_error and attempts > 0 and reruns < 1:
        errors.append(f'expected error was not rechecked (check_attempts={attempts}, explain_reruns={reruns})')
    return fixture.name, reruns, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rescript', type=Path, default=ROOT / 'rewatch/target/debug/rescript')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('pattern', nargs='?', default='*.res')
    args = parser.parse_args()
    fixtures = sorted((ROOT / 'tests/build_tests/super_errors/fixtures').glob(args.pattern))
    results = []
    failed = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {pool.submit(check, args.rescript.resolve(), fixture): fixture for fixture in fixtures}
        for future in as_completed(pending):
            try:
                result = future.result()
            except subprocess.TimeoutExpired:
                result = (pending[future].name, None, ['compiler exceeded ten-second bound'])
            results.append(result)
            name, _, errors = result
            for error in errors:
                print(f'{name}: {error}', flush=True)
            failed += bool(errors)
    print(f'fixtures={len(results)} rechecked={sum(r == 1 for _, r, _ in results)} failures={failed}')
    return int(failed != 0)


if __name__ == '__main__':
    sys.exit(main())
