#!/usr/bin/env python3
"""Failure-safe local process and restoration helpers for the fixed diagnostic."""
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
import traceback


def bounded(command, env, prefix, timeout):
    """Start one owned process group; preserve outputs even on timeout/interruption."""
    prefix = Path(prefix)
    assert not Path(str(prefix) + '.process.json').exists(), 'Preserve original attempt'
    start = time.perf_counter_ns()
    process = None
    stdout = stderr = b''
    error = None
    timed_out = False
    try:
        process = subprocess.Popen(command, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except BaseException as exc:
            error = exc
            timed_out = isinstance(exc, subprocess.TimeoutExpired)
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = process.communicate()  # Drain pipes and reap owned leader.
    except BaseException as exc:
        if error is None:
            error = exc
    row = dict(command=command, wall_ns=time.perf_counter_ns()-start,
               exit=process.returncode if process else None, timeout=timed_out,
               error=repr(error) if error else None)
    Path(str(prefix)+'.stdout').write_bytes(stdout)
    Path(str(prefix)+'.stderr').write_bytes(stderr)
    Path(str(prefix)+'.log').write_bytes(stdout+stderr)
    Path(str(prefix)+'.process.json').write_text(json.dumps(row, indent=2))
    if error and not timed_out:
        raise error
    return row, stdout+stderr


def restore_backups(root, backups_root, hashes, sha):
    """Attempt every original, including missing generated files; never hide failure."""
    errors = []
    for path, digest in hashes.items():
        try:
            backup = backups_root/path
            if sha(backup) != digest:
                raise ValueError(f'Backup changed: {path}')
            destination = root/path
            if not destination.is_file() or sha(destination) != digest:
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(backup, destination)
            if sha(destination) != digest:
                raise ValueError(f'Restoration mismatch: {path}')
        except Exception as exc:
            errors.append(exc)
    if errors:
        raise ExceptionGroup('Original-file restoration failed', errors)


def guarded(body, verify, restore, error_path):
    """Always restore, preserving the first error and recording later failures too."""
    failures = []
    result = None
    try:
        result = body()
    except BaseException as exc:
        failures.append(('body', exc, exc.__traceback__))
    finally:
        try:
            verify()
        except BaseException as exc:
            failures.append(('verification', exc, exc.__traceback__))
        finally:
            try:
                restore()
            except BaseException as exc:
                failures.append(('restoration', exc, exc.__traceback__))
    if failures:
        Path(error_path).write_text(json.dumps([
            dict(phase=phase, error=repr(exc), traceback=''.join(traceback.format_exception(type(exc), exc, tb)))
            for phase, exc, tb in failures], indent=2))
        raise failures[0][1].with_traceback(failures[0][2])
    return result


def clean(m, variant, workers, name):
    row, _ = bounded([str(m.D/f'bin/rescript-{variant}'), 'clean', str(m.WEB)],
                     m.env(variant, workers), m.D/f'logs/{name}', 120)
    if row['exit'] != 0 or row['timeout'] or row['error']:
        raise RuntimeError(f'Clean failed; original attempt preserved: {name}')


def attempt(m, pos, variant, workers):
    name = f'env-1-{pos}-{variant}-w{workers}'
    row = dict(stage='env', pair=1, position=pos, variant=variant, workers=workers)
    try:
        row['phase'] = 'clean'
        clean(m, variant, workers, name+'-clean')
        row['phase'] = 'build'
        row['load'] = os.getloadavg()
        process, log = bounded(['/usr/bin/time', '-lp']+m.command(variant),
                               m.env(variant, workers), m.D/f'logs/{name}', 180)
        row.update(process)
        text = log.decode(errors='replace')
        row['compiled_3248'] = 'Compiled 3248 modules' in text
        for line in text.splitlines():
            match = re.match(r'\s*(user|sys|real)\s+([\d.]+)$', line)
            if match:
                row[match[1]] = float(match[2])
            for key in ['maximum resident set size', 'instructions retired', 'cycles elapsed', 'peak memory footprint']:
                if line.strip().endswith(key):
                    row[key] = int(line.split()[0])
        if row['exit'] != 0 or row['timeout'] or row['error']:
            raise RuntimeError('Build failed or timed out; no replacement attempt')
        count, digest, manifest = m.outputs()
        (m.D/f'{name}-js.json').write_text(json.dumps(manifest, sort_keys=True))
        row.update(js_count=count, js_sha256=digest)
        if count != 5048 or not row['compiled_3248'] or digest != '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49':
            raise RuntimeError('Output mismatch; original attempt retained')
    except BaseException as exc:
        row['attempt_error'] = repr(exc)
        raise
    finally:
        with (m.D/'runs.jsonl').open('a') as f:
            f.write(json.dumps(row)+'\n')
        print(json.dumps(row), flush=True)
    return row
