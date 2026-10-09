import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';

test('publication rejects private metadata, unreviewed files and forged archive members', () => {
  const result = spawnSync('python3', ['-c', String.raw`
import sys, tempfile, json, io, tarfile, hashlib
from pathlib import Path
sys.path.insert(0, 'scripts')
from publication_policy import check_content, approved_files, check_archive, check_publication

def rejects(fn):
    try: fn()
    except (ValueError, UnicodeError): return
    raise AssertionError('Unsafe publication was accepted')

for value in [
    '/' + 'Users/example/project/',
    '/' + 'scratch/userdata/example/project/',
    '/' + '.ssh/id_ed25519',
    'CODEX_' + 'HOME=/private/auth',
    'Session ' + '12345678-1234-1234-1234-123456789012',
    'gh' + 'p_' + 'a' * 36,
]:
    rejects(lambda: check_content('evidence.log', value.encode()))
for name in ['FORMALIZATION_PROMPT.txt', 'auth.json', '.env.local', '20261009T000000Z-checkpoint.json']:
    rejects(lambda: check_content(name, b'{}'))
check_content('proof.log', b'{"key":"' + b'a'*64 + b'","cwd":"/work/qrh-proof"}')
with tempfile.TemporaryDirectory() as d:
    root = Path(d); proof = root/'proof'; proof.mkdir()
    (proof/'proof.lean').write_text('-- mathematical source\n')
    (proof/'publication-files.json').write_text(json.dumps(['proof.lean', 'publication-files.json']))
    approved_files(proof)
    (proof/'unreviewed.txt').write_text('unexpected')
    rejects(lambda: approved_files(proof)); (proof/'unreviewed.txt').unlink()
    (proof/'link').symlink_to(proof/'proof.lean')
    rejects(lambda: approved_files(proof)); (proof/'link').unlink()
    original = (proof/'publication-files.json').read_text()
    (proof/'publication-files.json').write_text(json.dumps(['../escape']))
    rejects(lambda: approved_files(proof))
    (proof/'publication-files.json').write_text(original)
    data = (proof/'proof.lean').read_bytes()
    manifest = {'proof.lean': hashlib.sha256(data).hexdigest()}
    archive=root/'bundle.tar.gz'
    def write(members):
        with tarfile.open(archive, 'w:gz') as tar:
            for name, content, kind in members:
                info=tarfile.TarInfo(name); info.type=kind; info.size=len(content)
                tar.addfile(info, io.BytesIO(content))
    good=('proof/proof.lean',data,tarfile.REGTYPE)
    write([good]);check_archive(archive,proof,manifest)
    for members in [[good,good], [('proof/../escape',data,tarfile.REGTYPE)], [('proof/proof.lean',b'changed',tarfile.REGTYPE)], [('proof/proof.lean',b'',tarfile.SYMTYPE)], []]:
        write(members);rejects(lambda: check_archive(archive,proof,manifest))
print('Privacy patterns, publication allowlist, symlinks, traversal, duplicates, stale digests and missing files checked.')
`], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr || result.stdout);
});
