#!/usr/bin/env python3
"""Canonical foreground entry: lock, preserve invocation, capture, then run a stage.

Re-exec through lockf rather than adding another supervisor process tree. The
existing measurement entry still owns its deadline and all compiler descendants.
"""
import sys
sys.dont_write_bytecode = True

import argparse
import contextlib
import json
import os
from pathlib import Path
import traceback
import uuid

import type_payload_inputs as inputs
import type_payload_supervisor as supervisor


LOCK = '/tmp/rescript-tella-heavy.lock'


def paths(root, mode, index):
    key = f'stage-{index}' if mode == 'stage' else 'analyze'
    prefix = root / 'provenance' / key
    return {name: Path(str(prefix) + suffix) for name, suffix in (
        ('command', '-command.json'), ('log', '-outer.log'),
        ('exit', '-outer.exit'), ('complete', '-outer.complete.json'))}


def validate_entry(root):
    if (root / 'EXPERIMENT_FAILED.json').exists():
        raise RuntimeError('experiment is permanently closed')
    own = Path(__file__).resolve()
    if own != root / 'protocol' / own.name:
        raise RuntimeError('run the archived entry point')
    seal = inputs.load(root / 'seal.json')
    admission = inputs.load(root / 'admission.json')
    if (admission['seal_sha256'] != inputs.sha(root / 'seal.json')
            or admission['plan_sha256'] != inputs.sha(root / 'plan.json')
            or seal['files'].get(str(own)) != inputs.sha(own)):
        raise RuntimeError('entry point or admission changed')


def validate_outer_prefix(root, mode, index):
    count = index if mode == 'stage' else 34
    for previous in range(count):
        names = paths(root, 'stage', previous)
        complete = inputs.load(names['complete'])
        if (complete['exit'] != 0 or names['exit'].read_text() != '0\n'
                or complete['command_sha256'] != inputs.sha(names['command'])
                or complete['log_sha256'] != inputs.sha(names['log'])):
            raise RuntimeError('previous outer execution is incomplete or changed')


def execute_locked(root, mode, index, token):
    validate_entry(root)
    names = paths(root, mode, index)
    command = inputs.load(names['command'])
    if (command['token'] != token or command['mode'] != mode
            or command['index'] != index
            or command['helper_sha256'] != inputs.sha(Path(__file__))
            or command['cwd'] != os.getcwd()):
        raise RuntimeError('locked invocation does not match its preserved command')
    validate_outer_prefix(root, mode, index)
    os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
    code = 0
    with names['log'].open('x') as log, contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
        try:
            import type_payload_measure
            sys.argv = ['type_payload_measure.py', '--root', str(root), mode]
            if mode == 'stage':
                sys.argv.append(str(index))
            type_payload_measure.main()
        except BaseException:
            code = 1
            traceback.print_exc()
        finally:
            log.flush()
            os.fsync(log.fileno())
    with names['exit'].open('x') as stream:
        stream.write(str(code) + '\n')
        stream.flush()
        os.fsync(stream.fileno())
    supervisor.publish(names['complete'], {
        'exit': code, 'token': token, 'mode': mode, 'index': index,
        'command_sha256': inputs.sha(names['command']),
        'log_sha256': inputs.sha(names['log']),
    })
    if code and not (root / 'EXPERIMENT_FAILED.json').exists():
        supervisor.publish(root / 'EXPERIMENT_FAILED.json', {
            'phase': 'canonical outer execution', 'mode': mode, 'index': index,
            'closed': True, 'reason': 'inner entry raised; see preserved outer log',
        })
    print(f'{mode} {index}: exit {code}; captured {names["log"]}')
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('mode', choices=('stage', 'analyze'))
    parser.add_argument('index', type=int, nargs='?')
    parser.add_argument('--locked-token', help=argparse.SUPPRESS)
    args = parser.parse_args()
    root = args.root.resolve()
    if ((args.mode == 'stage' and (args.index is None or not 0 <= args.index < 34))
            or (args.mode == 'analyze' and args.index is not None)):
        parser.error('stage needs an index 0..33; analyze takes no index')
    validate_entry(root)
    if args.locked_token:
        return execute_locked(root, args.mode, args.index, args.locked_token)
    validate_outer_prefix(root, args.mode, args.index)
    names = paths(root, args.mode, args.index)
    if any(path.exists() for path in names.values()):
        raise RuntimeError('outer replay or partial capture; do not retry')
    token = uuid.uuid4().hex
    argv = ['/usr/bin/lockf', '-k', LOCK, '/usr/bin/python3', str(Path(__file__).resolve()),
            '--root', str(root), args.mode]
    if args.mode == 'stage':
        argv.append(str(args.index))
    argv.extend(['--locked-token', token])
    cwd = inputs.load(root / 'plan.json')['repos']['worktree']
    supervisor.publish(names['command'], {
        'argv': argv, 'cwd': cwd, 'mode': args.mode, 'index': args.index,
        'token': token, 'helper_sha256': inputs.sha(Path(__file__)),
        'environment': {'PYTHONDONTWRITEBYTECODE': '1'},
        'runner_deadline_seconds': 420, 'required_tool_timeout_seconds': 600,
    })
    os.chdir(cwd)
    os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
    os.execve(argv[0], argv, os.environ.copy())


if __name__ == '__main__':
    sys.exit(main())
