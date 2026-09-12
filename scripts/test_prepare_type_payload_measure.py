from pathlib import Path
import tempfile
import unittest
from unittest import mock

import prepare_type_payload_measure as prepare


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix='type-payload-preparation-fixture-'))
        self.patch = mock.patch.object(prepare, 'CAMPAIGN', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_rejects_path_escape_before_any_copy_or_git_command(self):
        with mock.patch.object(prepare, 'copy_new') as copy, mock.patch.object(prepare.inputs, 'git') as git:
            with self.assertRaises(ValueError):
                prepare.prepare('../outside', self.root / 'candidate-bin', '0' * 40)
            copy.assert_not_called()
            git.assert_not_called()

    def test_rejects_candidate_outside_campaign(self):
        with self.assertRaises(ValueError):
            prepare.prepare('comparison-test', self.root.parent / 'other-bin', '0' * 40)
        self.assertFalse((self.root / 'comparison-test').exists())

    def test_never_reuses_existing_root(self):
        target = self.root / 'comparison-test'
        target.mkdir()
        marker = target / 'partial'
        marker.write_text('preserve')
        with self.assertRaises(RuntimeError):
            prepare.prepare('comparison-test', self.root / 'candidate-bin', '0' * 40)
        self.assertEqual(marker.read_text(), 'preserve')

    def test_low_space_does_not_clean_or_create_root(self):
        with mock.patch.object(prepare.shutil, 'disk_usage', return_value=mock.Mock(free=1)):
            with self.assertRaises(RuntimeError):
                prepare.prepare('comparison-test', self.root / 'candidate-bin', '0' * 40)
        self.assertFalse((self.root / 'comparison-test').exists())

    def test_copy_collision_preserves_existing_bytes(self):
        source, target = self.root / 'source', self.root / 'target'
        source.write_text('new')
        target.write_text('original')
        with self.assertRaises(RuntimeError):
            prepare.copy_new(source, target)
        self.assertEqual(target.read_text(), 'original')


if __name__ == '__main__':
    unittest.main()
