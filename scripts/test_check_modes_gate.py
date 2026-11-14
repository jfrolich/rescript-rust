#!/usr/bin/env python3
"""Unit tests of the fixture gate itself (no compiler or build outputs needed)."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import test_check_modes as gate


class CheckModesGate(unittest.TestCase):
    def test_checker_entry_and_error_retry_rules(self):
        # Default attempts, Explain attempts, reruns, failure, frontend-only.
        for attempts, explain_attempts, reruns, fails, frontend in (
            (0, 0, 0, False, True),
            (0, 1, 0, True, False),
            (1, 0, 0, True, False),
            (1, 1, 0, True, False),
            (2, 1, 1, False, False),
        ):
            with self.subTest(attempts=attempts, explain_attempts=explain_attempts), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                fixtures, work = root / 'fixtures', root / 'work'
                for directory in (fixtures, work):
                    directory.mkdir()
                fixture = fixtures / 'Error.res'
                fixture.write_text('let bad: bool = 1')
                diagnostic = subprocess.CompletedProcess([], 1, b'', b"We've found a bug for you!")
                counted = subprocess.CompletedProcess([], 1, b'', (
                    f'[compiler-counter] check_attempts={attempts}\n'
                    f'[compiler-counter] explain_reruns={reruns}\n').encode())
                explained = subprocess.CompletedProcess([], 1, b'', (
                    f'[compiler-counter] check_attempts={explain_attempts}\n').encode())
                with patch.object(gate.subprocess, 'run', side_effect=[diagnostic, diagnostic, counted, explained]):
                    _, _, frontend_only, errors = gate.check(Path('/compiler'), root, root, fixture, work)
                self.assertEqual(bool(errors), fails)
                self.assertEqual(frontend_only, frontend)

    def test_equal_frontend_entry_does_not_exempt_output_differences(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = root / 'Syntax.res'
            fixture.write_text('let =')
            work = root / 'work'
            work.mkdir()
            success = subprocess.CompletedProcess([], 1, b'', b'first diagnostic')
            explain = subprocess.CompletedProcess([], 1, b'', b'different diagnostic')
            counts = subprocess.CompletedProcess([], 1, b'',
                b'[compiler-counter] check_attempts=0\n[compiler-counter] explain_reruns=0\n')
            with patch.object(gate.subprocess, 'run', side_effect=[success, explain, counts, counts]):
                _, _, frontend, errors = gate.check(Path('/compiler'), root, root, fixture, work)
            self.assertTrue(frontend)
            self.assertIn('Success and Explain diagnostics differ', errors)

    def test_source_copy_excludes_build_outputs(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary) / 'package'
            (package / 'src').mkdir(parents=True)
            (package / 'lib').mkdir()
            (package / 'src/A.res').write_text('let value = 1')
            (package / 'src/A.cmi').write_bytes(b'stale')
            (package / 'lib/Stale.res').write_text('not an input')
            (package / 'rescript.json').write_text('{}')
            copied = Path(temporary) / 'copy'
            gate.copy_sources(package, copied)
            self.assertEqual(sorted(str(p.relative_to(copied)) for p in copied.rglob('*') if p.is_file()),
                             ['rescript.json', 'src/A.res'])


if __name__ == '__main__':
    unittest.main()
