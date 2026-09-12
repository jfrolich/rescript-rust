#!/usr/bin/env python3
"""Fixed, failure-stopping C/N comparison. Preparation never happens on launch."""
import argparse
import contextlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import signal
import statistics
import sys
import time
import traceback
import uuid

import type_payload_inputs as inputs
import type_payload_supervisor as supervisor


EXPECTED_JS = '1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49'


def schedule():
    rows = [{'name': 'qualification-' + variant, 'variant': variant,
             'workers': 12, 'timed': False, 'pair': None} for variant in ('C', 'N')]
    for pair in range(1, 9):
        for workers in ((12, 1) if pair % 2 else (1, 12)):
            for variant in (('C', 'N') if pair % 2 else ('N', 'C')):
                rows.append({'name': f'pair-{pair}-w{workers}-{variant}',
                             'variant': variant, 'workers': workers,
                             'timed': True, 'pair': pair})
    return rows


def metrics(stderr):
    result = {}
    for line in stderr.splitlines():
        match = re.fullmatch(r'\s*(real|user|sys)\s+([\d.]+)', line)
        if match:
            result[match[1]] = float(match[2])
        for name in ('maximum resident set size', 'instructions retired', 'cycles elapsed',
                     'peak memory footprint'):
            if line.strip().endswith(name):
                result[name] = int(line.split()[0])
    required = {'real', 'user', 'sys', 'maximum resident set size',
                'instructions retired', 'cycles elapsed'}
    if required - result.keys():
        raise RuntimeError('missing /usr/bin/time metrics: ' + repr(required - result.keys()))
    return result


@contextlib.contextmanager
def stage_deadline(seconds):
    """Leave time below the tool's 600s limit for reaping and restoration."""
    if signal.getitimer(signal.ITIMER_REAL) != (0.0, 0.0):
        raise RuntimeError('stage requires exclusive ownership of its alarm')
    previous_handler = signal.signal(signal.SIGALRM, supervisor.interrupt)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield lambda: signal.setitimer(signal.ITIMER_REAL, 0)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)


class Experiment:
    def __init__(self, root, inventory=None):
        self.root = Path(root).resolve()
        self.plan = inputs.load(self.root / 'plan.json')
        if self.plan['slots'] != schedule():
            raise RuntimeError('plan does not match the fixed 34-stage schedule')
        self.inventory = inventory if inventory is not None else inputs.Inventory(self.root)
        self.logs = self.root / 'logs'
        self.baseline = inputs.load(self.root / 'baseline.json')
        self.attempts = []
        self.cancel_deadline = lambda: None

    def verify_seal(self):
        seal = inputs.load(self.root / 'seal.json')
        admission = inputs.load(self.root / 'admission.json')
        if (admission['seal_sha256'] != inputs.sha(self.root / 'seal.json')
                or admission['plan_sha256'] != inputs.sha(self.root / 'plan.json')):
            raise RuntimeError('parent admission does not match plan/seal')
        for module in (__file__, inputs.__file__, supervisor.__file__):
            if str(Path(module).resolve()) not in seal['files']:
                raise RuntimeError('running helper is not sealed: ' + module)
        for name, digest in seal['files'].items():
            if inputs.sha(name) != digest:
                raise RuntimeError('sealed file changed: ' + name)
        if (self.root / 'EXPERIMENT_FAILED.json').exists():
            raise RuntimeError('experiment is closed after failure')
        if list(self.root.rglob('*.publishing-*')):
            raise RuntimeError('partial publication blocks further launches')

    def prefix(self, index):
        if isinstance(index, bool) or not isinstance(index, int) or not 0 <= index < 34:
            raise ValueError('stage index must be 0..33')
        expected = {row['name'] for row in schedule()[:index]}
        for suffix in ('.complete.json', '.started.json'):
            actual = {path.name[:-len(suffix)] for path in (self.root / 'stages').glob('*' + suffix)}
            if actual != expected:
                raise RuntimeError('partial/replayed/out-of-order stage prefix')
        for i, row in enumerate(schedule()[:index]):
            record = inputs.load(self.root / 'stages' / (row['name'] + '.complete.json'))
            if record['index'] != i or record['row'] != row:
                raise RuntimeError('completed prefix record changed')
        name = schedule()[index]['name']
        for directory in (self.logs, self.root / 'observations', self.root / 'qualification-outputs'):
            if list(directory.glob(name + '*')):
                raise RuntimeError('stage artifacts already exist: ' + name)
        if index == 0 and (self.root / 'execution-started.json').exists():
            raise RuntimeError('partial cohort admission blocks first-stage replay')
        if index > 0 and not (self.root / 'execution-started.json').is_file():
            raise RuntimeError('cohort admission missing')

    def record_snapshot(self, name, phase, metadata, restored=False):
        current = self.inventory.snapshot()
        prefix = self.root / 'observations' / (name + '.' + phase)
        supervisor.publish(str(prefix) + '.inventory.json', current)
        verdict = self.inventory.compare(self.baseline, current, metadata, restored)
        supervisor.publish(str(prefix) + '.verification.json', verdict)
        return verdict

    @staticmethod
    def require_snapshot(verdict):
        if not verdict['valid']:
            raise RuntimeError('input preservation failed: ' + repr(verdict['errors']))

    def env(self, row):
        env = os.environ.copy()
        for name in list(env):
            if name.startswith(('RESCRIPT_', 'MIMALLOC_', 'OTEL_', 'RUST_DEBUG_')):
                del env[name]
        env.pop('RUST_LOG', None)
        env.update(RESCRIPT_BSC_EXE=str(self.root / self.plan['binaries']['bsc-' + row['variant']]),
                   RESCRIPT_RUNTIME=str(self.inventory.runtime),
                   RAYON_NUM_THREADS=str(row['workers']), PYTHONDONTWRITEBYTECODE='1')
        return env

    def compiler(self, row):
        return str(self.root / self.plan['binaries']['rescript-' + row['variant']])

    def build(self, row):
        return ['/usr/bin/time', '-lp', self.compiler(row), 'build', '--in-process',
                '--no-timing', 'true', str(self.inventory.web)]

    def process(self, argv, name, row, token, timeout, children=()):
        attempt = {'name': name, 'result': None}
        self.attempts.append(attempt)
        result = supervisor.capture(argv, self.logs / name, env=self.env(row),
                                    timeout=timeout, token=token, children=children)
        attempt['result'] = result
        return result

    def child(self, index, token):
        self.verify_seal()
        if isinstance(index, bool) or not isinstance(index, int) or not 2 <= index < 34:
            raise ValueError('child index must be a timed stage')
        row = schedule()[index]
        name = row['name']
        started = inputs.load(self.root / 'stages' / (name + '.started.json'))
        if started['token'] != token or started['index'] != index:
            raise RuntimeError('child lacks its admitted timed stage')
        if (self.root / 'stages' / (name + '.complete.json')).exists():
            raise RuntimeError('child stage already completed')
        parent_path = self.logs / (name + '-hyperfine.pid.json')
        deadline = time.monotonic() + 3
        while not parent_path.exists() and time.monotonic() < deadline:
            time.sleep(.005)
        parent = inputs.load(parent_path)
        if parent['token'] != token or parent['pgid'] != os.getpgrp():
            raise RuntimeError('child does not belong to the admitted Hyperfine group')
        result = self.process(self.build(row), name + '-build', row, token, 180)
        supervisor.require_success(result)

    def observed_outputs(self, row):
        name = row['name']
        observed = self.inventory.outputs()
        supervisor.publish(self.root / 'observations' / (name + '.js.json'), observed)
        runtime = self.inventory.runtime_sources()
        supervisor.publish(self.root / 'observations' / (name + '.runtime.json'), runtime)
        if not row['timed']:
            for relative in observed['manifest']:
                target = self.root / 'qualification-outputs' / name / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as stream:
                    stream.write((self.inventory.web / relative).read_bytes())
        text = (self.logs / (name + '-build.stdout')).read_text(errors='replace')
        if (observed['count'] != 5048 or observed['sha256'] != EXPECTED_JS
                or 'Compiled 3248 modules' not in text
                or runtime != inputs.load(self.root / 'runtime-sources.json') or len(runtime) != 107):
            raise RuntimeError('JavaScript/module/runtime-source contract failed')
        if name != 'qualification-C':
            control = inputs.load(self.root / 'observations/qualification-C.js.json')
            if observed['manifest'] != control['manifest']:
                raise RuntimeError('JavaScript differs from this cohort control')
        return {'js_count': observed['count'], 'js_sha256': observed['sha256']}

    def run_stage(self, index):
        try:
            self.verify_seal()
            self.prefix(index)
            self.inventory.verify_protected()
        except BaseException as exc:
            failure = self.root / 'EXPERIMENT_FAILED.json'
            if not failure.exists():
                supervisor.publish(failure, {'phase': 'admission', 'index': index, 'error': repr(exc)})
            raise
        self.attempts = []
        row = schedule()[index]
        name = row['name']
        token = uuid.uuid4().hex
        if index == 0:
            supervisor.publish(self.root / 'execution-started.json', {
                'seal_sha256': inputs.sha(self.root / 'seal.json'), 'token': token})
        supervisor.publish(self.root / 'stages' / (name + '.started.json'), {
            'index': index, 'row': row, 'token': token})
        errors, result = [], None
        try:
            self.require_snapshot(self.record_snapshot(name, 'before-clean', self.inventory.metadata(), True))
            self.verify_seal()
            try:
                clean = self.process([self.compiler(row), 'clean', str(self.inventory.web)],
                                     name + '-clean', row, token, 120)
            finally:
                after_clean = self.record_snapshot(name, 'after-clean', set())
            supervisor.require_success(clean)
            self.require_snapshot(after_clean)
            self.verify_seal()
            build = None
            after_build = outputs = None
            try:
                if row['timed']:
                    command = shlex.join([sys.executable, str(Path(__file__).resolve()),
                                          '--root', str(self.root), 'child', str(index), token])
                    driver = self.process([
                        self.plan['hyperfine'], '--runs', '1', '--warmup', '0', '--export-json',
                        str(self.root / 'observations' / (name + '.hyperfine.json')), command],
                        name + '-hyperfine', row, token, 240,
                        children=[(self.logs / (name + '-build.pid.json'),
                                   self.logs / (name + '-build.process.json'))])
                    supervisor.require_success(driver)
                    build = inputs.load(self.logs / (name + '-build.process.json'))
                    hf = inputs.load(self.root / 'observations' / (name + '.hyperfine.json'))['results']
                    if len(hf) != 1 or hf[0]['exit_codes'] != [0] or len(hf[0]['times']) != 1:
                        raise RuntimeError('unexpected Hyperfine sample count or failure')
                else:
                    build = self.process(self.build(row), name + '-build', row, token, 180)
            finally:
                # Preserve both observations before restoration, even on failure.
                try:
                    after_build = self.record_snapshot(name, 'after-build', self.inventory.metadata())
                except BaseException as exc:
                    errors.append({'phase': 'after-build-inputs', 'error': repr(exc)})
                try:
                    outputs = self.observed_outputs(row)
                except BaseException as exc:
                    errors.append({'phase': 'after-build-outputs', 'error': repr(exc)})
            supervisor.require_success(build)
            if errors:
                raise RuntimeError('post-build observations failed')
            self.require_snapshot(after_build)
            self.verify_seal()
            result = {'index': index, 'row': row, 'token': token, 'build': build,
                      'metrics': metrics((self.logs / (name + '-build.stderr')).read_text(errors='replace')),
                      **outputs}
        except BaseException as exc:
            errors.append({'phase': 'body', 'error': repr(exc), 'traceback': traceback.format_exc()})
        # Never race restoration against an unobserved or still-running compiler.
        safe_to_restore = all(attempt.get('result') is not None
                              and attempt['result']['group_absent']
                              and attempt['result']['leader_reaped'] for attempt in self.attempts)
        self.cancel_deadline()
        if safe_to_restore:
            with supervisor.cleanup_without_reentrant_interrupts():
                try:
                    self.inventory.restore()
                    self.inventory.verify_protected()
                except BaseException as exc:
                    errors.append({'phase': 'restoration', 'error': repr(exc)})
                try:
                    final = self.inventory.snapshot()
                    supervisor.publish(self.root / 'observations' / (name + '.final.inventory.json'), final)
                    # Failure can leave metadata absent; success still requires all 12.
                    expected_metadata = (self.inventory.metadata() & final['inputs'].keys()
                                         if errors else self.inventory.metadata())
                    verdict = self.inventory.compare(self.baseline, final, expected_metadata, True)
                    supervisor.publish(self.root / 'observations' / (name + '.final.verification.json'), verdict)
                    self.require_snapshot(verdict)
                except BaseException as exc:
                    errors.append({'phase': 'final-inputs', 'error': repr(exc)})
        else:
            errors.append({'phase': 'cleanup', 'error': 'owned group state unresolved; human intervention required before restoration'})
        if errors:
            supervisor.publish(self.root / 'stages' / (name + '.failure.json'), errors)
            supervisor.publish(self.root / 'EXPERIMENT_FAILED.json', {'stage': name, 'errors': errors})
            raise RuntimeError('cohort stopped at ' + name)
        supervisor.publish(self.root / 'stages' / (name + '.complete.json'), result)
        return result

    def analyze(self):
        self.verify_seal()
        rows = schedule()
        expected = {row['name'] + '.complete.json' for row in rows}
        if {path.name for path in (self.root / 'stages').glob('*.complete.json')} != expected:
            raise RuntimeError('cohort is incomplete')
        records = [inputs.load(self.root / 'stages' / (row['name'] + '.complete.json')) for row in rows]
        for index, (record, row) in enumerate(zip(records, rows)):
            if record['index'] != index or record['row'] != row:
                raise RuntimeError('cohort record mismatch')
            supervisor.require_success(record['build'])
        summary = {'timed_builds': 32, 'qualification_builds': 2, 'modes': {}}
        for workers in (12, 1):
            cells = {}
            for variant in ('C', 'N'):
                values = [record['build']['wall_ns'] / 1e9 for record in records
                          if record['row']['timed'] and record['row']['workers'] == workers
                          and record['row']['variant'] == variant]
                if len(values) != 8:
                    raise RuntimeError('missing timed cell')
                cells[variant] = {'mean_s': statistics.mean(values), 'sd_s': statistics.stdev(values),
                                  'min_s': min(values), 'max_s': max(values)}
            deltas = []
            for pair in range(1, 9):
                pair_values = {record['row']['variant']: record['build']['wall_ns'] / 1e9
                               for record in records if record['row']['pair'] == pair
                               and record['row']['workers'] == workers}
                deltas.append(pair_values['N'] - pair_values['C'])
            mean = statistics.mean(deltas)
            half = 2.364624251 * statistics.stdev(deltas) / math.sqrt(8)
            summary['modes'][str(workers)] = {
                'cells': cells, 'paired_N_minus_C_s': deltas,
                'paired_ci95_s': [mean - half, mean + half],
                'improvement_percent': -100 * mean / cells['C']['mean_s']}
        self.inventory.verify_protected()
        self.require_snapshot(self.record_snapshot('aggregate', 'final', self.inventory.metadata(), True))
        supervisor.publish(self.root / 'summary.json', summary)
        supervisor.publish(self.root / 'execution-complete.json', {'summary_sha256': inputs.sha(self.root / 'summary.json')})
        return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('mode', choices=('stage', 'child', 'analyze'))
    parser.add_argument('index', type=int, nargs='?')
    parser.add_argument('token', nargs='?')
    args = parser.parse_args()
    experiment = Experiment(args.root)
    with supervisor.handle_interrupts(), stage_deadline(210 if args.mode == 'child' else 420) as cancel:
        experiment.cancel_deadline = cancel
        if args.mode == 'stage':
            result = experiment.run_stage(args.index)
        elif args.mode == 'child':
            result = experiment.child(args.index, args.token)
        else:
            result = experiment.analyze()
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
