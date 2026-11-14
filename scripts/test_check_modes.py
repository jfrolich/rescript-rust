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
import shutil
import tempfile
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def check(binary, runtime, belt, fixture, work):
    """Three bounded compiler runs per fixture, no shared mutable test state."""
    isolated = work / fixture.stem
    isolated.mkdir()
    source = isolated / fixture.name
    shutil.copyfile(fixture, source)
    args = [str(binary), 'bsc', '-w', '+A', '-bs-jsx', '4', '-I',
            str(belt / 'lib/rescript'), '-color', 'always', str(source)]
    env = dict(os.environ, RESCRIPT_RUNTIME=str(runtime))
    env.pop('RESCRIPT_TEST_DISCARD_UNIT', None)
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
    elif has_error and (attempts == 0 or reruns < 1):
        errors.append(f'expected error was not rechecked (check_attempts={attempts}, explain_reruns={reruns})')
    return fixture.name, reruns, errors


def copy_sources(package, target):
    """Copy package inputs only; never consume a checkout's compiled outputs.

    bsc_registry compiles the package named by -I <package>/lib/rescript in
    memory. That directory need not exist and is not read for its .cmi files.
    """
    target.mkdir()
    for name in ('rescript.json', 'package.json'):
        source = package / name
        if source.is_file():
            shutil.copyfile(source, target / name)
    for source in package.rglob('*'):
        relative = source.relative_to(package)
        if any(part in ('lib', 'node_modules', '.git') for part in relative.parts):
            continue
        if source.is_file() and source.suffix in ('.res', '.resi'):
            destination = target / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rescript', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('pattern', nargs='?', default='*.res')
    args = parser.parse_args()
    fixtures = sorted((ROOT / 'tests/build_tests/super_errors/fixtures').glob(args.pattern))
    results = []
    failed = 0
    if not fixtures:
        parser.error('fixture pattern matched no sources')
    with tempfile.TemporaryDirectory(prefix='check-modes-') as temporary:
        work = Path(temporary)
        runtime, belt = work / 'runtime', work / 'belt'
        copy_sources(args.runtime.resolve(), runtime)
        copy_sources(ROOT / 'packages/@rescript/belt', belt)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {pool.submit(check, args.rescript.resolve(), runtime, belt, fixture, work): fixture for fixture in fixtures}
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
