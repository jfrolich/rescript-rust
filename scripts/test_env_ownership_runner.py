#!/usr/bin/env python3
"""Focused failure-path tests. No compiler, clean command or corpus build runs."""
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import tempfile
import types
import unittest
from unittest.mock import Mock, patch
import env_ownership_runner as runner


class RunnerFailures(unittest.TestCase):
    def test_timeout_kills_owned_group_reaps_and_preserves_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix=Path(directory)/'attempt'
            process=Mock(pid=4321, returncode=-9)
            process.communicate.side_effect=[subprocess.TimeoutExpired(['fake'],1,output=b'partial'),(b'partial stdout',b'partial stderr')]
            with patch.object(runner.subprocess,'Popen',return_value=process) as spawn, patch.object(runner.os,'killpg') as kill:
                row,log=runner.bounded(['fake'],{},prefix,1)
            self.assertTrue(spawn.call_args.kwargs['start_new_session'])
            kill.assert_called_once_with(4321,signal.SIGKILL)
            self.assertEqual(process.communicate.call_count,2)
            self.assertTrue(row['timeout']);self.assertEqual(row['exit'],-9)
            self.assertEqual(log,b'partial stdoutpartial stderr')
            self.assertEqual(Path(str(prefix)+'.stdout').read_bytes(),b'partial stdout')
            self.assertTrue(json.loads(Path(str(prefix)+'.process.json').read_text())['timeout'])

    def test_spawn_failure_preserves_attempt(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix=Path(directory)/'spawn'
            with patch.object(runner.subprocess,'Popen',side_effect=FileNotFoundError('missing')):
                with self.assertRaises(FileNotFoundError):runner.bounded(['missing'],{},prefix,1)
            row=json.loads(Path(str(prefix)+'.process.json').read_text())
            self.assertIsNone(row['exit']);self.assertIn('missing',row['error'])

    def test_inventory_failure_still_restores_missing_original_and_preserves_first_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'backup').mkdir();(root/'backup/original.gen.ts').write_bytes(b'original')
            digest=hashlib.sha256(b'original').hexdigest()
            sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
            first=RuntimeError('original build failure')
            def body():raise first
            def verify():raise ValueError('inventory failure')
            def restore():runner.restore_backups(root/'corpus',root/'backup',{'original.gen.ts':digest},sha)
            with self.assertRaises(RuntimeError) as raised:runner.guarded(body,verify,restore,root/'failure.json')
            self.assertIs(raised.exception,first)
            self.assertEqual((root/'corpus/original.gen.ts').read_bytes(),b'original')
            self.assertEqual([x['phase'] for x in json.loads((root/'failure.json').read_text())],['body','verification'])

    def test_inventory_failure_does_not_become_success(self):
        with tempfile.TemporaryDirectory() as directory:
            restore=Mock()
            with self.assertRaises(ValueError):
                runner.guarded(lambda:None,lambda:(_ for _ in ()).throw(ValueError('inventory')),restore,Path(directory)/'failure.json')
            restore.assert_called_once()

    def test_clean_timeout_records_failed_row_and_never_builds(self):
        with tempfile.TemporaryDirectory() as directory:
            m=types.SimpleNamespace(D=Path(directory),WEB=Path('/unused'),env=lambda v,w:{})
            with patch.object(runner,'bounded',return_value=({'exit':-9,'timeout':True,'error':'timeout'},b'')) as bounded:
                with self.assertRaises(RuntimeError):runner.attempt(m,1,'D',1)
            self.assertEqual(bounded.call_count,1)
            self.assertEqual(bounded.call_args.args[0][1],'clean')
            row=json.loads((m.D/'runs.jsonl').read_text());self.assertEqual(row['phase'],'clean')
            self.assertIn('attempt_error',row)

    def test_build_timeout_records_failed_row_and_no_output_inspection(self):
        with tempfile.TemporaryDirectory() as directory:
            m=types.SimpleNamespace(D=Path(directory),WEB=Path('/unused'),env=lambda v,w:{},command=lambda v:['fake'],outputs=Mock())
            with patch.object(runner,'clean'),patch.object(runner,'bounded',return_value=({'exit':-9,'timeout':True,'error':'timeout','wall_ns':123},b'partial')):
                with self.assertRaises(RuntimeError):runner.attempt(m,1,'P',1)
            m.outputs.assert_not_called()
            row=json.loads((m.D/'runs.jsonl').read_text());self.assertTrue(row['timeout']);self.assertEqual(row['wall_ns'],123)


if __name__=='__main__':unittest.main(verbosity=2)
