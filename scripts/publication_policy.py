"""Validate public evidence without executing proof or submission code."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import tarfile
import subprocess

# Generic classes, never a list of the maintainer's private values.
PATTERNS = {
    'personal workspace': re.compile(r'/(?:Users|scratch/userdata)/[^/\s\"\']+/'),
    'SSH identity': re.compile(r'/\.ssh/(?:id_|config\b)|-----BEGIN (?:OPENSSH |RSA |EC |DSA )?PRIVATE KEY-----'),
    'credential directory assignment': re.compile(r'\bCODEX_HOME\s*[:=]\s*[\"\']?/'),
    'credential token': re.compile(r'\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,}|sk-(?:proj-|ant-)?[A-Za-z0-9_-]{40,})'),
    'agent session': re.compile(r'(?:session|thread|resume)[^\n]{0,160}\b[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}\b', re.I),
}
OPERATIONAL = re.compile(r'^(?:FORMALIZATION_PROMPT\.txt|PROGRESS\.txt|auth\.json|\.env.*|.*-events\.jsonl|\d{8}T.*|preflight-.*|launcher\.log|continuation\.log|final-resources\.json|space-cleanup-.*)$')


def check_content(name, data):
    if OPERATIONAL.fullmatch(PurePosixPath(name).name):
        raise ValueError(f'Operational file is not publishable: {name}')
    text = data.decode('utf-8')
    for label, pattern in PATTERNS.items():
        if pattern.search(text):
            # Never echo the sensitive value to CI logs.
            raise ValueError(f'Publication rejected ({label}): {name}')


def approved_files(proof):
    names = json.loads((proof / 'publication-files.json').read_text())
    if not isinstance(names, list) or not names or names != sorted(set(names)):
        raise ValueError('Publication allowlist must be a nonempty sorted unique list')
    for name in names:
        path = PurePosixPath(name)
        if not isinstance(name, str) or path.is_absolute() or '..' in path.parts or str(path) != name or '\\' in name:
            raise ValueError('Unsafe publication path')
    actual = set()
    for p in proof.rglob('*'):
        if p.is_symlink():
            raise ValueError('Symlink in proof publication tree')
        if p.is_file():
            actual.add(p.relative_to(proof).as_posix())
    if actual != set(names):
        raise ValueError('Proof tree differs from the reviewed publication allowlist')
    for name in names:
        check_content(name, (proof / name).read_bytes())
    return names


def check_archive(archive, proof, manifest):
    expected = {f'{proof.name}/{name}': digest for name, digest in manifest.items()}
    seen = set()
    total = 0
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            if not member.isfile() or member.name not in expected or member.name in seen:
                raise ValueError('Unexpected, unsafe or duplicate archive member')
            total += member.size
            if total > 100 * 1024 * 1024 or member.size > 10 * 1024 * 1024:
                raise ValueError('Archive resource limit exceeded')
            if member.uid or member.gid or member.uname or member.gname:
                raise ValueError('Archive includes machine identity metadata')
            data = tar.extractfile(member).read()
            check_content(member.name, data)
            if hashlib.sha256(data).hexdigest() != expected[member.name]:
                raise ValueError('Archive member differs from published manifest')
            seen.add(member.name)
    if seen != set(expected):
        raise ValueError('Archive is incomplete')


def check_native_tightening(root):
    """Authenticate native evidence while preserving its pending checker status."""
    from fractions import Fraction
    name = 'nielstron-20261009-tightening'
    proof = root / 'proofs' / name
    public = root / 'public/proofs' / name
    names = approved_files(proof)
    manifest = json.loads((root / 'proofs' / (name + '.sha256.json')).read_text())
    if set(names) != set(manifest):
        raise ValueError('Native proof publication manifest and allowlist differ')
    for path, digest in manifest.items():
        if hashlib.sha256((proof / path).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Native source checksum mismatch: {path}')
    collection = json.loads((public / 'collection.json').read_text())
    if collection['status'] != 'verification-pending':
        raise ValueError('Native evidence cannot mint external checker verification')
    if set(collection['files']) != {p.name for p in public.iterdir() if p.name != 'collection.json'}:
        raise ValueError('Native public evidence collection is incomplete')
    for path, digest in collection['files'].items():
        if PurePosixPath(path).name != path or hashlib.sha256((public / path).read_bytes()).hexdigest() != digest:
            raise ValueError('Native public evidence checksum mismatch')
    for target, source in collection['snapshot_exports'].items():
        if source not in manifest or (public / target).read_bytes() != (proof / source).read_bytes():
            raise ValueError('Native evidence export differs from snapshot')
    if json.loads((public / 'source-sha256.json').read_text()) != manifest:
        raise ValueError('Native public source manifest differs')
    archive = public / 'source-public.tar.gz'
    check_archive(archive, proof, manifest)
    digest, archive_name = (public / 'SHA256SUMS.txt').read_text().strip().split('  ')
    if archive_name != archive.name or hashlib.sha256(archive.read_bytes()).hexdigest() != digest:
        raise ValueError('Native archive checksum mismatch')
    record = next(r for r in json.loads((root / 'catalogue/results.json').read_text())['records'] if r['id'] == name)
    report = json.loads((proof / 'compressed/audit/tightening-verification.json').read_text())
    # The native collection remains an immutable historical pending report.
    # A current catalogue upgrade requires a separate authenticated kernel dossier.
    subprocess.run(['node', str(root / 'scripts/check-native-kernels.mjs')], check=True)
    theta = f"{record['theta']['numerator']}/{record['theta']['denominator']}"
    if report['status'] != 'PASS' or report['threshold'] != theta:
        raise ValueError('Native target report does not match catalogue boundary')
    if not all(report[k] for k in ('original_exact_three_targets_proved', 'tighter_exact_three_targets_proved',
                                  'strict_improvement_proved_in_lean', 'specification_compiled_without_QRH_imports')):
        raise ValueError('Native target evidence is incomplete')
    if Fraction(report['original_threshold']) - Fraction(theta) != Fraction(report['exact_improvement']) or Fraction(report['exact_improvement']) <= 0:
        raise ValueError('Native improvement is not exact and positive')
    for axioms in report['declarations'].values():
        if set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Unexpected native proof axiom')
    changes = {p['path']: p for p in json.loads((proof / 'publication-transformations.json').read_text())['changes']}
    for path, artifact in report['artifacts'].items():
        if path.startswith('build/'):
            continue  # Compiled objects are explicitly excluded; source and logs are authenticated.
        name_in_snapshot = 'compressed/' + path
        original = changes.get(name_in_snapshot, {}).get('original_sha256', manifest.get(name_in_snapshot))
        if original != artifact['sha256']:
            raise ValueError(f'Native gate artifact hash mismatch: {path}')
    counts = json.loads((proof / 'compressed/audit/token-counts.json').read_text())['qrh_package']
    if sum(p['after_tokens'] for p in counts['files']) != counts['after_tokens']:
        raise ValueError('Native source token totals disagree')
    for item in counts['files']:
        if item.get('after_sha256') != manifest.get('compressed/formalization/' + item['path']):
            raise ValueError('Native token report and published source differ')
    return len(names)


def check_publication(root):
    proof = root / 'proofs/qrh-20261009'
    names = approved_files(proof)
    manifest = json.loads((root / 'proofs/qrh-20261009.sha256.json').read_text())
    if set(manifest) != set(names):
        raise ValueError('Publication manifest and allowlist differ')
    for name, digest in manifest.items():
        if hashlib.sha256((proof / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Publication checksum mismatch: {name}')
    public = root / 'public/proofs/qrh-20261009'
    if (public / 'source.tar.gz').exists():
        raise ValueError('Retired archive must not be published')
    archive = public / 'source-public.tar.gz'
    check_archive(archive, proof, manifest)
    digest, name = (public / 'SHA256SUMS.txt').read_text().strip().split('  ')
    if name != archive.name or hashlib.sha256(archive.read_bytes()).hexdigest() != digest:
        raise ValueError('Archive checksum mismatch')
    native_count = check_native_tightening(root)
    for directory in [root / 'public/proofs', root / 'evidence']:
        for path in directory.rglob('*'):
            if path.is_symlink():
                raise ValueError('Symlink in public evidence')
            if path.is_file() and path.suffix not in ('.gz', '.png', '.jpg', '.pdf'):
                check_content(path.relative_to(root).as_posix(), path.read_bytes())
    return len(names) + native_count


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    print(f'Publication checks passed: {check_publication(root)} reviewed files and exact archive contents.')
