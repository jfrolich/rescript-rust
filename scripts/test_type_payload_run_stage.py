"""Actual lockf/re-exec/capture tests with a fake inner runner, never a compiler."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


@unittest.skipUnless(Path('/usr/bin/lockf').exists(), 'requires native lockf')
class OuterEntryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='payload-outer-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        protocol = self.root / 'protocol'
        protocol.mkdir()
        (self.root / 'provenance').mkdir()
        source = Path(__file__).parent
        for name in ('type_payload_run_stage.py', 'type_payload_inputs.py', 'type_payload_supervisor.py'):
            shutil.copy2(source / name, protocol / name)
        self.entry = protocol / 'type_payload_run_stage.py'
        # Only the lock pathname differs; do not contend with a real campaign.
        self.entry.write_text(self.entry.read_text().replace('/tmp/rescript-tella-heavy.lock', str(self.root / 'test.lock')))
        (protocol / 'type_payload_measure.py').write_text('''import os, sys
from pathlib import Path

def main():
    root = Path(sys.argv[sys.argv.index('--root') + 1])
    print('fake runner', os.environ.get('PYTHONDONTWRITEBYTECODE'), sys.dont_write_bytecode)
    print('captured stderr', file=sys.stderr)
    if (root / 'interrupt').exists():
        raise KeyboardInterrupt('synthetic interrupt')
    if (root / 'fail').exists():
        raise RuntimeError('synthetic failure')
''')
        self.save('plan.json', {'repos': {'worktree': str(self.root)}})
        self.save('seal.json', {'files': {str(self.entry): self.sha(self.entry)}})
        self.save('admission.json', {'seal_sha256': self.sha(self.root / 'seal.json'),
                                    'plan_sha256': self.sha(self.root / 'plan.json')})

    def save(self, name, value):
        (self.root / name).write_text(json.dumps(value))

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def run_entry(self, index=0, extra=()):
        env = os.environ.copy()
        env.pop('PYTHONDONTWRITEBYTECODE', None)
        return subprocess.run(['/usr/bin/python3', str(self.entry), '--root', str(self.root),
                               'stage', str(index), *extra], env=env, capture_output=True, timeout=10)

    def test_capture_env_and_real_reexec_without_shell_redirection(self):
        result = self.run_entry()
        self.assertEqual(result.returncode, 0, result.stderr)
        files = self.root / 'provenance'
        text = (files / 'stage-0-outer.log').read_text()
        self.assertIn('fake runner 1 True', text)
        self.assertIn('captured stderr', text)
        command = json.loads((files / 'stage-0-command.json').read_text())
        self.assertEqual(command['argv'][:2], ['/usr/bin/lockf', '-k'])
        self.assertEqual((files / 'stage-0-outer.exit').read_text(), '0\n')
        self.assertFalse(list(self.root.rglob('*.pyc')))

    def test_replay_cannot_replace_capture(self):
        self.assertEqual(self.run_entry().returncode, 0)
        before = {p.name: self.sha(p) for p in (self.root / 'provenance').iterdir()}
        self.assertNotEqual(self.run_entry().returncode, 0)
        self.assertEqual(before, {p.name: self.sha(p) for p in (self.root / 'provenance').iterdir()})

    def test_partial_capture_blocks_later_stage(self):
        self.assertEqual(self.run_entry().returncode, 0)
        (self.root / 'provenance/stage-0-outer.exit').unlink()
        self.assertNotEqual(self.run_entry(1).returncode, 0)
        self.assertFalse((self.root / 'provenance/stage-1-command.json').exists())

    def test_inner_failure_is_captured_and_closes_cohort(self):
        (self.root / 'fail').touch()
        self.assertNotEqual(self.run_entry().returncode, 0)
        self.assertIn('synthetic failure', (self.root / 'provenance/stage-0-outer.log').read_text())
        self.assertEqual((self.root / 'provenance/stage-0-outer.exit').read_text(), '1\n')
        self.assertTrue((self.root / 'EXPERIMENT_FAILED.json').exists())
        self.assertNotEqual(self.run_entry(1).returncode, 0)

    def test_interrupt_retains_capture_and_closes(self):
        (self.root / 'interrupt').touch()
        self.assertNotEqual(self.run_entry().returncode, 0)
        self.assertIn('synthetic interrupt', (self.root / 'provenance/stage-0-outer.log').read_text())
        self.assertTrue((self.root / 'EXPERIMENT_FAILED.json').exists())

    def test_changed_entry_rejected_before_launch(self):
        self.entry.write_text(self.entry.read_text() + '\n# changed\n')
        self.assertNotEqual(self.run_entry().returncode, 0)
        self.assertEqual(list((self.root / 'provenance').iterdir()), [])

    def test_wrong_locked_token_cannot_execute(self):
        self.assertEqual(self.run_entry().returncode, 0)
        before = (self.root / 'provenance/stage-0-outer.log').read_bytes()
        self.assertNotEqual(self.run_entry(extra=('--locked-token', 'foreign')).returncode, 0)
        self.assertEqual((self.root / 'provenance/stage-0-outer.log').read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
