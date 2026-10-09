"""Publication regressions exercise the real packager using disposable fixtures."""
from pathlib import Path
import contextlib
import importlib.util
import io
import json
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from publication_policy import approved_files, validate_publication_paths, check_archive

spec = importlib.util.spec_from_file_location('packager', Path(__file__).resolve().parents[1] / 'scripts/package-native-tightening.py')
packager = importlib.util.module_from_spec(spec)
spec.loader.exec_module(packager)


class PublicationPackaging(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.proof = self.root / 'proofs' / packager.ID
        self.public = self.root / 'public/proofs' / packager.ID
        names = sorted(set(packager.EXPORTS.values()) | {'compressed/LICENSE',
                       'compressed/third-party-notices/mathlib.txt', 'publication-files.json'})
        for name in names:
            path = self.proof / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('Reviewed fixture\n')
        (self.proof / 'publication-files.json').write_text(json.dumps(names, indent=2) + '\n')
        self.package()

    def package(self):
        with contextlib.redirect_stdout(io.StringIO()):
            packager.package_snapshot(self.root)

    def outputs(self):
        return {p.name: p.read_bytes() for p in self.public.iterdir()}

    def test_deterministic_and_exact_archive(self):
        before = self.outputs()
        allowlist = (self.proof / 'publication-files.json').read_bytes()
        self.package()
        self.assertEqual(before, self.outputs())
        self.assertEqual(allowlist, (self.proof / 'publication-files.json').read_bytes())
        manifest = json.loads((self.public / 'source-sha256.json').read_text())
        check_archive(self.public / 'source-public.tar.gz', self.proof, manifest)
        self.assertIn('compressed/LICENSE', manifest)
        self.assertIn('compressed/third-party-notices/mathlib.txt', manifest)

    def test_extra_source_is_not_adopted(self):
        before = self.outputs()
        allowlist = (self.proof / 'publication-files.json').read_bytes()
        (self.proof / 'internal-notes.txt').write_text('Unreviewed private draft\n')
        with self.assertRaisesRegex(ValueError, 'reviewed publication allowlist'):
            self.package()
        self.assertEqual(before, self.outputs())
        self.assertEqual(allowlist, (self.proof / 'publication-files.json').read_bytes())

    def test_extra_download_is_not_adopted(self):
        (self.public / 'internal-notes.txt').write_text('Unreviewed private draft\n')
        before = self.outputs()
        with self.assertRaisesRegex(ValueError, 'Unexpected file'):
            self.package()
        self.assertEqual(before, self.outputs())

    def test_workspace_mode_rejects_leftovers_before_reading_inputs(self):
        before = self.outputs()
        (self.proof / 'internal-notes.txt').write_text('Unreviewed private draft\n')
        with patch.object(packager, 'ROOT', self.root), patch.object(sys, 'argv',
                ['packager', '--workspace', str(self.root / 'nonexistent-workspace')]):
            with self.assertRaisesRegex(ValueError, 'reviewed publication allowlist'):
                packager.main()
        self.assertEqual(before, self.outputs())

    def test_symlink_source_is_rejected(self):
        original = self.proof / 'README.md'
        original.unlink()
        original.symlink_to(self.proof / 'NOTICE')
        before = self.outputs()
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.package()
        self.assertEqual(before, self.outputs())

    def test_symlink_download_is_rejected(self):
        path = self.public / 'README.txt'
        path.unlink()
        path.symlink_to(self.proof / 'README.md')
        with self.assertRaisesRegex(ValueError, 'Unexpected file'):
            self.package()

    def test_case_collisions_fail_on_every_host(self):
        for names in [
            ['compressed/LICENSE', 'compressed/license/mathlib.txt'],
            ['a/Foo.lean', 'a/foo.lean'],
            ['a/Foo/one.lean', 'a/foo/two.lean'],
            ['a', 'a/child.lean'],
            ['caf\u00e9.lean', 'cafe\u0301.lean'],
        ]:
            with self.subTest(names=names), self.assertRaises(ValueError):
                validate_publication_paths(sorted(names))

    def test_unsafe_allowlist_paths(self):
        for names in [[], [3], [''], ['.'], ['../escape'], ['/absolute'], ['a\\b'], ['a', 'a']]:
            with self.subTest(names=names), self.assertRaises(ValueError):
                validate_publication_paths(names)

    def test_archive_cannot_authorize_case_collision(self):
        manifest = {'compressed/LICENSE': 'unused', 'compressed/license/notice.txt': 'unused'}
        with self.assertRaisesRegex(ValueError, 'collision'):
            check_archive(self.public / 'source-public.tar.gz', self.proof, manifest)


if __name__ == '__main__':
    unittest.main()
