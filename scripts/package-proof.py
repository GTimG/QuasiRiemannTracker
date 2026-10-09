"""Package only the reviewed publication allowlist; never gather arbitrary files.

Run after an explicit maintainer review. The normal build checks existing evidence
and does not regenerate its checksums or imply a new mathematical verification.
"""
from pathlib import Path
import gzip
import hashlib
import json
import tarfile
from publication_policy import approved_files, check_archive

root = Path(__file__).resolve().parents[1]
proof = root / 'proofs/qrh-20261009'
public = root / 'public/proofs/qrh-20261009'
assert hashlib.sha256((proof / 'inputs/qrh-formalization-handoff-20261009/accepted-answer.tex').read_bytes()).hexdigest() == 'c8b9994d6a55521b53fe4664ba190e46dc0a02f7d85221e25d39efa4dcd34de9'
files = {name: hashlib.sha256((proof / name).read_bytes()).hexdigest() for name in approved_files(proof)}
archive = public / 'source-public.tar.gz'
with archive.open('wb') as f, gzip.GzipFile(filename='', mode='wb', fileobj=f, mtime=0) as gz, tarfile.open(fileobj=gz, mode='w') as tar:
    for name in files:
        p = proof / name
        info = tar.gettarinfo(str(p), arcname=proof.name + '/' + name)
        info.uid = info.gid = 0
        info.uname = info.gname = ''
        info.mtime = 0
        info.mode = 0o644
        with p.open('rb') as src:
            tar.addfile(info, src)
check_archive(archive, proof, files)
(root / 'proofs/qrh-20261009.sha256.json').write_text(json.dumps(files, indent=2) + '\n')
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
(public / 'SHA256SUMS.txt').write_text(digest + '  ' + archive.name + '\n')
print(f'Packaged {len(files)} reviewed files; SHA256 {digest}')
