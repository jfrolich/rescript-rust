import json
import os
from pathlib import Path
import tempfile
import sys
import unittest
from unittest import mock

import type_payload_inputs as inputs
import type_payload_measure as measure
import type_payload_supervisor as supervisor


TIME_OUTPUT = 'real 1.0\nuser 0.8\nsys 0.1\n100 maximum resident set size\n200 instructions retired\n300 cycles elapsed\n'


def save(path, value):
    Path(path).write_text(json.dumps(value))


class FakeInventory:
    def __init__(self, root):
        self.root = root
        self.web = root / 'web'
        self.web.mkdir()
        (self.web / 'Example.js').write_text('export const example = 1;\n')
        self.runtime = root / 'runtime'
        self.present = self.metadata()
        self.restored = True
        self.fail_restore = False
        self.drift = False
        self.bad_output = False
        self.restore_calls = 0

    def metadata(self):
        return {'metadata-' + str(i) for i in range(12)}

    def snapshot(self):
        return {'inputs': {name: 'metadata' for name in self.present},
                'restored': self.restored, 'drift': self.drift}

    def compare(self, baseline, current, metadata, restored=False):
        valid = (set(current['inputs']) == set(metadata) and not current['drift']
                 and (not restored or current['restored']))
        return {'valid': valid, 'errors': [] if valid else ['synthetic mismatch']}

    def verify_protected(self):
        if not self.restored:
            raise RuntimeError('synthetic unrestored files')

    def restore(self):
        self.restore_calls += 1
        if self.fail_restore:
            raise RuntimeError('synthetic restoration failure')
        self.restored = True

    def outputs(self):
        return {'count': 5048, 'sha256': 'wrong' if self.bad_output else measure.EXPECTED_JS,
                'manifest': {'Example.js': inputs.sha(self.web / 'Example.js')}}

    def runtime_sources(self):
        return {'runtime-' + str(i): 'source-hash' for i in range(107)}


class StageTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix='type-payload-stage-fixture-'))
        for name in ('logs', 'observations', 'stages', 'qualification-outputs'):
            (self.root / name).mkdir()
        self.inventory = FakeInventory(self.root)
        self.sentinel = self.root / 'sealed-source'
        self.sentinel.write_text('original')
        plan = {'slots': measure.schedule(), 'hyperfine': '/unused/hyperfine',
                'binaries': {name + '-' + variant: name + '-' + variant
                             for name in ('bsc', 'rescript') for variant in ('C', 'N')}}
        save(self.root / 'plan.json', plan)
        save(self.root / 'baseline.json', self.inventory.snapshot())
        save(self.root / 'runtime-sources.json', self.inventory.runtime_sources())
        sealed = [Path(module).resolve() for module in
                  (measure.__file__, inputs.__file__, supervisor.__file__)]
        sealed += [self.sentinel, self.root / 'plan.json', self.root / 'baseline.json',
                   self.root / 'runtime-sources.json']
        save(self.root / 'seal.json', {'files': {str(path): inputs.sha(path) for path in sealed}})
        save(self.root / 'admission.json', {
            'seal_sha256': inputs.sha(self.root / 'seal.json'),
            'plan_sha256': inputs.sha(self.root / 'plan.json')})
        self.experiment = measure.Experiment(self.root, self.inventory)
        self.calls = []
        self.fail_build = False
        self.live_build = False
        self.drift_after_clean = False
        self.drift_after_build = False
        self.extra_hyperfine_sample = False
        self.patch = mock.patch.object(supervisor, 'capture', side_effect=self.capture)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def capture(self, argv, prefix, **kwargs):
        self.calls.append(argv)
        build = 'build' in argv
        if argv[0] == '/unused/hyperfine':
            import shlex
            command = shlex.split(argv[-1])
            index, token = int(command[-2]), command[-1]
            save(str(prefix) + '.pid.json', {'pgid': os.getpgrp(), 'token': token})
            self.experiment.child(index, token)
            export = argv[argv.index('--export-json') + 1]
            save(export, {'results': [{'times': [1.0, 1.0] if self.extra_hyperfine_sample else [1.0],
                                       'exit_codes': [0]}]})
        elif build:
            self.inventory.present = self.inventory.metadata()
            self.inventory.restored = False
            if self.drift_after_build:
                self.inventory.drift = True
        elif 'clean' in argv:
            self.inventory.present = set()
            if self.drift_after_clean:
                self.sentinel.write_text('changed')
        else:
            raise AssertionError('unexpected fake process command')
        Path(str(prefix) + '.stdout').write_text('Compiled 3248 modules\n' if build else '')
        Path(str(prefix) + '.stderr').write_text(TIME_OUTPUT if build else '')
        result = {'exit': 1 if build and self.fail_build else 0, 'timeout': False,
                'error': 'synthetic build failure' if build and self.fail_build else None,
                'cleanup_errors': [], 'leader_reaped': not (build and self.live_build),
                'group_absent': not (build and self.live_build),
                'wall_ns': 800000000 if build and any('rescript-N' in arg for arg in argv) else 1000000000,
                'argv': argv, 'token': kwargs['token']}
        save(str(prefix) + '.process.json', result)
        return result

    def test_fixed_balanced_schedule(self):
        rows = measure.schedule()
        self.assertEqual(len(rows), 34)
        for workers in (1, 12):
            for variant in ('C', 'N'):
                self.assertEqual(sum(r['timed'] and r['workers'] == workers and r['variant'] == variant for r in rows), 8)
        for pair in range(1, 9):
            variants = ['C', 'N'] if pair % 2 else ['N', 'C']
            for workers in (1, 12):
                self.assertEqual([r['variant'] for r in rows if r['pair'] == pair and r['workers'] == workers], variants)

    def test_two_qualifications_restore_between_slots(self):
        self.experiment.run_stage(0)
        self.assertTrue(self.inventory.restored)
        self.experiment.run_stage(1)
        self.assertEqual(len(self.calls), 4)
        self.assertEqual(self.inventory.restore_calls, 2)
        self.assertEqual(len(list((self.root / 'stages').glob('*.complete.json'))), 2)

    def test_complete_fake_cohort_uses_exactly_32_timed_builds(self):
        for index in range(34):
            self.experiment.run_stage(index)
        summary = self.experiment.analyze()
        self.assertEqual(summary['timed_builds'], 32)
        self.assertEqual(summary['qualification_builds'], 2)
        self.assertEqual(sum('build' in argv for argv in self.calls), 34)
        self.assertEqual(sum('clean' in argv for argv in self.calls), 34)
        self.assertEqual(sum(argv[0] == '/unused/hyperfine' for argv in self.calls), 32)
        self.assertAlmostEqual(summary['modes']['12']['improvement_percent'], 20)
        self.assertTrue((self.root / 'execution-complete.json').exists())

    def test_extra_hyperfine_sample_closes_cohort(self):
        self.experiment.run_stage(0)
        self.experiment.run_stage(1)
        self.extra_hyperfine_sample = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(2)
        self.assertTrue((self.root / 'observations/pair-1-w12-C.after-build.inventory.json').exists())
        self.assertFalse((self.root / 'stages/pair-1-w12-C.complete.json').exists())
        self.assertTrue(self.inventory.restored)

    def test_drift_between_stages_is_permanent_failure(self):
        self.experiment.run_stage(0)
        self.sentinel.write_text('changed')
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(1)
        self.sentinel.write_text('original')
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(1)
        self.assertEqual(len(self.calls), 2)

    def test_actual_main_rejects_seal_drift_before_launch(self):
        self.sentinel.write_text('changed')
        with mock.patch.object(inputs, 'Inventory', return_value=self.inventory), mock.patch.object(sys, 'argv',
                ['type_payload_measure.py', '--root', str(self.root), 'stage', '0']):
            with self.assertRaises(RuntimeError):
                measure.main()
        self.assertEqual(self.calls, [])

    def test_seal_drift_zero_launch(self):
        self.sentinel.write_text('changed')
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(self.calls, [])

    def test_out_of_order_zero_launch(self):
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(1)
        self.assertEqual(self.calls, [])

    def test_partial_root_zero_launch(self):
        save(self.root / 'execution-started.json', {'partial': True})
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(self.calls, [])

    def test_partial_log_zero_launch(self):
        (self.root / 'logs/qualification-C-build.stdout').write_text('partial')
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(self.calls, [])

    def test_completed_stage_never_replays(self):
        self.experiment.run_stage(0)
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(len(self.calls), 2)

    def test_drift_between_clean_and_build_blocks_build(self):
        self.drift_after_clean = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(len(self.calls), 1)
        self.assertEqual(self.inventory.restore_calls, 1)
        self.assertTrue((self.root / 'EXPERIMENT_FAILED.json').is_file())

    def test_failed_build_keeps_after_build_inventory_and_manifest(self):
        self.fail_build = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertTrue((self.root / 'observations/qualification-C.after-build.inventory.json').is_file())
        self.assertTrue((self.root / 'observations/qualification-C.js.json').is_file())
        self.assertTrue(self.inventory.restored)
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(1)
        self.assertEqual(len(self.calls), 2)

    def test_source_drift_after_build_is_not_hidden_by_restoration(self):
        self.drift_after_build = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertTrue(self.inventory.restored)
        self.assertFalse((self.root / 'stages/qualification-C.complete.json').exists())

    def test_restoration_failure_closes_cohort(self):
        self.inventory.fail_restore = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertFalse(self.inventory.restored)
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(1)
        self.assertEqual(len(self.calls), 2)

    def test_output_failure_is_not_success(self):
        self.inventory.bad_output = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertTrue((self.root / 'observations/qualification-C.js.json').exists())
        self.assertFalse((self.root / 'stages/qualification-C.complete.json').exists())

    def test_no_restoration_race_with_live_compiler(self):
        self.live_build = True
        with self.assertRaises(RuntimeError):
            self.experiment.run_stage(0)
        self.assertEqual(self.inventory.restore_calls, 0)
        self.assertTrue((self.root / 'EXPERIMENT_FAILED.json').exists())

    def test_child_cannot_launch_without_admitted_stage(self):
        with self.assertRaises(FileNotFoundError):
            self.experiment.child(2, 'wrong')
        self.assertEqual(self.calls, [])

    def test_analyze_refuses_incomplete_cohort(self):
        with self.assertRaises(RuntimeError):
            self.experiment.analyze()
        self.assertEqual(self.calls, [])


class DeadlineTests(unittest.TestCase):
    def test_deadline_interrupts_and_reaps_actual_process(self):
        root = Path(tempfile.mkdtemp(prefix='type-payload-deadline-fixture-'))
        with measure.stage_deadline(.1):
            result = supervisor.capture([sys.executable, '-c', 'import time;time.sleep(30)'],
                                        root / 'command', env=os.environ.copy(), timeout=3,
                                        term_grace=.3, kill_grace=3)
        self.assertIn('SupervisorInterrupted', result['error'])
        self.assertTrue(result['leader_reaped'])
        self.assertTrue(result['group_absent'])
        self.assertFalse(result['cleanup_errors'])


class InputTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix='type-payload-input-fixture-'))
        self.author = self.root / 'author.res'
        self.author.write_text('let value = 1')
        self.copy = self.root / 'lib/bs/author.res'
        self.ledger = {str(self.copy): {'removed_sha256': inputs.sha(self.author),
                                      'surviving_same_package_sources': [str(self.author)]}}

    def test_absent_copy_requires_authored_source(self):
        normalized, evidence = inputs.classify_copies({}, self.ledger)
        self.assertEqual(normalized, {})
        self.assertFalse(evidence[str(self.copy)]['copy_present'])
        self.author.unlink()
        with self.assertRaises(RuntimeError):
            inputs.classify_copies({}, self.ledger)

    def test_unchanged_copy_still_checks_authored_source(self):
        recorded = {str(self.copy): inputs.sha(self.author)}
        normalized, evidence = inputs.classify_copies(recorded, self.ledger)
        self.assertEqual(normalized, {})
        self.assertTrue(evidence[str(self.copy)]['copy_present'])
        self.author.write_text('changed')
        with self.assertRaises(RuntimeError):
            inputs.classify_copies(recorded, self.ledger)

    def test_corrupt_copy_fails(self):
        with self.assertRaises(RuntimeError):
            inputs.classify_copies({str(self.copy): 'wrong'}, self.ledger)

    def test_equal_bytes_still_restore_original_mtime(self):
        backup = self.root / 'backup'
        backup.write_bytes(self.author.read_bytes())
        state = inputs.file_state(backup)
        os.utime(self.author, ns=(state['mtime_ns'] + 10000, state['mtime_ns'] + 10000))
        inventory = object.__new__(inputs.Inventory)
        inventory.root = self.root
        inventory.protected = {str(self.author): {'kind': 'generated', 'backup': 'backup', 'state': state}}
        inventory.restore()
        inventory.verify_protected()
        self.assertEqual(inputs.file_state(self.author), state)

    def test_corrupt_backup_never_overwrites_live_file(self):
        backup = self.root / 'backup'
        backup.write_bytes(self.author.read_bytes())
        state = inputs.file_state(backup)
        backup.write_text('corrupt')
        inventory = object.__new__(inputs.Inventory)
        inventory.root = self.root
        inventory.protected = {str(self.author): {'kind': 'generated', 'backup': 'backup', 'state': state}}
        before = inputs.file_state(self.author)
        with self.assertRaises(RuntimeError):
            inventory.restore()
        self.assertEqual(inputs.file_state(self.author), before)


if __name__ == '__main__':
    unittest.main()
