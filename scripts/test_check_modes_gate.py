#!/usr/bin/env python3
"""Unit tests of the fixture gate itself (no compiler or build outputs needed)."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import test_check_modes as gate


class CheckModesGate(unittest.TestCase):
    def test_error_without_attempts_fails(self):
        for attempts, reruns, fails in ((0, 0, True), (1, 0, True), (2, 1, False)):
            with self.subTest(attempts=attempts), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                fixtures, expected, work = root / 'fixtures', root / 'expected', root / 'work'
                for directory in (fixtures, expected, work):
                    directory.mkdir()
                fixture = fixtures / 'Error.res'
                fixture.write_text('let bad: bool = 1')
                (expected / 'Error.res.expected').write_text("We've found a bug for you!")
                diagnostic = subprocess.CompletedProcess([], 1, b'', b'a diagnostic')
                counted = subprocess.CompletedProcess([], 1, b'', (
                    f'[compiler-counter] check_attempts={attempts}\n'
                    f'[compiler-counter] explain_reruns={reruns}\n').encode())
                with patch.object(gate.subprocess, 'run', side_effect=[diagnostic, diagnostic, counted]):
                    _, _, errors = gate.check(Path('/compiler'), root, root, fixture, work)
                self.assertEqual(bool(errors), fails)

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
