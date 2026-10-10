"""Data-ingestion regressions. These tests do not claim to verify Lean proofs."""
import hashlib
import importlib.util
import io
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('liu_replay', ROOT / 'verifier/liu/replay.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


def archive(members):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w:gz') as tar:
        for name, data, kind in members:
            item = tarfile.TarInfo(name)
            if kind == 'symlink':
                item.type = tarfile.SYMTYPE
                item.linkname = '/tmp/not-allowed'
                tar.addfile(item)
            else:
                item.size = len(data)
                tar.addfile(item, io.BytesIO(data))
    return output.getvalue()


def pin(data, destination='Candidate/Main.lean'):
    return {'path': destination, 'sha256': hashlib.sha256(data).hexdigest()}


class ReplayDataSafety(unittest.TestCase):
    def test_author_python_remains_inert_data(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            marker = root / 'executed'
            python = f'from pathlib import Path\nPath({str(marker)!r}).write_text("executed")\nraise RuntimeError("author code ran")\n'.encode()
            payload = archive([('repo/verify.py', python, 'file')])
            # No eval/import/runpy/subprocess is needed to ingest even this file.
            with patch('subprocess.run', side_effect=AssertionError('host execution')), patch('subprocess.check_output', side_effect=AssertionError('host execution')):
                replay.unpack_selected(payload, {'verify.py': pin(python, 'verify.py')}, root / 'source')
            self.assertFalse(marker.exists())
            self.assertEqual((root / 'source/verify.py').read_bytes(), python)

    def test_source_changes_cannot_reuse_a_hash(self):
        with tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                replay.unpack_selected(archive([('repo/Main.lean', b'axiom p : False', 'file')]), {'Main.lean': pin(b'theorem p : True := trivial')}, Path(raw))

    def test_unsafe_paths_are_rejected_even_in_unused_archive_entries(self):
        for name in ['../escape', '/absolute', 'repo/../../escape', 'repo\\escape', 'repo//escape', './repo/escape', 'repo/\nfile']:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as raw:
                with self.assertRaises(ValueError):
                    replay.unpack_selected(archive([(name, b'x', 'file')]), {}, Path(raw))

    def test_oversized_archive_member_is_rejected_before_decompression(self):
        payload = io.BytesIO()
        with tarfile.open(fileobj=payload, mode='w:gz') as tar:
            item = tarfile.TarInfo('repo/Main.lean')
            item.size = 10 * 1024**2 + 1
            tar.addfile(item)
        with tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(ValueError, 'resource limit'):
                replay.unpack_selected(payload.getvalue(), {}, Path(raw))

    def test_no_links_duplicates_or_missing_files(self):
        expected = {'Main.lean': pin(b'x')}
        examples = [
            [('repo/Main.lean', b'', 'symlink')],
            [('repo/Main.lean', b'x', 'file'), ('repo/Main.lean', b'x', 'file')],
            [('repo/Other.lean', b'x', 'file')],
        ]
        for members in examples:
            with self.subTest(members=members), tempfile.TemporaryDirectory() as raw:
                with self.assertRaises(ValueError):
                    replay.unpack_selected(archive(members), expected, Path(raw))

    def test_hash_pins_cannot_write_outside_source(self):
        with tempfile.TemporaryDirectory() as raw:
            with self.assertRaises(ValueError):
                replay.unpack_selected(archive([('repo/Main.lean', b'x', 'file')]), {'Main.lean': pin(b'x', '../escape')}, Path(raw))
            self.assertFalse((Path(raw).parent / 'escape').exists())

    def test_import_graph_handles_nested_comments_without_evaluating_source(self):
        source = '/- import Fake.Outer /- import Fake.Inner -/ -/\nmodule\npublic import all A.B C.D -- discarded\n/- x -/ import E.F\nnamespace X\n#eval unsafePayload\n'
        self.assertEqual(replay.imports(source), ['A.B', 'C.D', 'E.F'])
        with self.assertRaisesRegex(ValueError, 'Unsafe module'):
            replay.imports('import ../../escape')

    def test_canonical_contract_preserves_quantifiers_pole_and_function(self):
        challenge, solution = replay.canonical_sources()
        self.assertIn('{q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}', challenge)
        self.assertIn('(hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0', challenge)
        self.assertIn('((1507 - 2 * Real.sqrt 921) / 1653 : ℝ) < s.re', challenge)
        self.assertNotIn('CombinedPaper', challenge)
        self.assertNotIn('RHZeroFreeExtension', challenge)
        self.assertNotIn('sorry', solution)
        self.assertEqual(replay.AXIOMS, {'propext', 'Classical.choice', 'Quot.sound'})

    def test_unsupported_host_fails_before_reading_profile_or_spawning(self):
        with patch.object(replay.sys, 'platform', 'darwin'), patch('subprocess.run', side_effect=AssertionError('spawn')), tempfile.TemporaryDirectory() as raw:
            with self.assertRaisesRegex(ValueError, 'unprivileged Linux'):
                replay.run(Path(raw)/'missing.json', Path(raw)/'work')
            self.assertFalse((Path(raw)/'work').exists())


if __name__ == '__main__':
    unittest.main()
