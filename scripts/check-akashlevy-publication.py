"""Validate publication packaging and require independent acceptance for verified status.

The default mode is read-only and never runs Lean, Lake, Comparator or a kernel. It
checks the reviewed allowlist and snapshot manifest, the public downloads, their
archive and checksums, retains the historical author-side report, and scans every
published file (snapshot files, archive members, public
downloads and the manuscript PDF) for private metadata: the shared publication
patterns plus local temporary and agent scratch paths, bare UUIDs and e-mail
addresses other than GitHub and Anthropic no-reply addresses.

--regenerate rewrites only derived files from the reviewed snapshot (the snapshot
manifest, public copies of snapshot files, source-sha256.json, source-public.tar.gz,
SHA256SUMS.txt and collection.json). It never edits or extends the allowlist.
"""
from datetime import datetime
from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import io
import json
import re
import sys
import subprocess
import tarfile
import zlib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from publication_policy import PATTERNS, approved_files, check_archive, check_content  # noqa: E402

ID = 'akashlevy-20261009-weighted-numerator'
REPLAY_PREFIX = 'proofs/akashlevy-20261010-safe-replay/'
REPLAY_REFERENCES = {'result.json', 'logs/judge.log', 'README.txt',
                     'contract-audit.json', 'controls/control-results.json'}
THETA = '10499/12000'
NAMES = ['QRHPalomar.allDirichlet', 'QRHPalomar.zeta', 'QRHPalomar.allHecke']
AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
KERNELS = ['Lean default', 'nanoda', 'con-ron']
STATUSES = ('framework-verified', 'verification-pending')
TEMPLATE = 'public/proofs/palomar-20261009/qrh/src/Challenge.lean'
TEMPLATE_SHA256 = 'eee59775c5f4f892199f7456f85f7664a14ef3010fc1b3df97ed2c0f8a1db4e6'
TEMPLATE_LITERAL = '874957019421 / 1000000000000'
RELEASE_SHA256 = 'e721cf30671d3830fa6120c7b1a4e6b22624650ce1d618c0ca28a4889f5ef324'
# Binaries of the recorded run (darwin_aarch64 release, Lean 4.34.1, lean4export 076e8e57).
TOOLS = {
    'lake': 'd2d63c80ca10bd2cc9557d11d59221b95c6eefb078c9652a11ef887ab8a068a5',
    'lean': 'd1d9c26a539f54fe839d2aa7760bf1ac1dd76a30b26e2c9684bebf2900038fcf',
    'leanexport': 'f533d8829d2f6507816a3c784055bf2eb8f9a7e53a3134affbe320eba5dc27c1',
    'leanchecker': '41662275cb7d624d0f0fdf8cb3dc7d5c15e99b233be3ebec576a5c38df181844',
    'nanoda_bin': '85daddc584afe0d8fa28e18d4c566219bc3c8ddd8b0d43b90285a8f5b35faf2c',
    'con-ron': '7e04504e38276e0e2edb9b4fa992a9206424091b3cfa509ebe8024696b4ad8b0',
    'source_lean': '1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554',
    'lean4export': '17da1e168bf5d41484c940e41c1f68230798ebb38d09174b564e955895279d0f',
}
ENTRYPOINT = {'module': 'WeightedQRH.Statements',
              'declaration': 'OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re'}
NEGATIVE = 'evidence/comparator/WeightedQRHNegControl'
ZETA = 'formalization/ComparatorChallenges/WeightedQRHZeta'
DRIVER = 'formalization/kernels/judge_three_kernels.py'
K = 'evidence/kernels/'
# Statement-definition files compared by Comparator: pinned upstream blobs.
DEFINITIONS = {
    'lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean':
        ('openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
         '9871d175749b34ec40cf66ccc14b4faa0a9ef08831cb3fa901c944e57c7b9ec6'),
    'lean/OAI/NumberTheory/DirichletL/Hecke/IdealBridge.lean':
        ('openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
         '6c1fc33b7372108323bf3af3d4ab6f6e454ea9896b89e78964463a8e35df735f'),
    'Mathlib/NumberTheory/LSeries/DirichletContinuation.lean':
        ('mathlib d13f23b723b8a846827a245b89c10fc7d3f11612',
         '7ef38fb53f462e19dfd6746fc1826423e55bb5e2672c2b5667e2fd4889f401b6'),
    'Mathlib/NumberTheory/LSeries/RiemannZeta.lean':
        ('mathlib d13f23b723b8a846827a245b89c10fc7d3f11612',
         '8d24b729a30f1fef0820f0f7c9cdbb5910df30dfac2c597eb666794bead08b1c'),
}
SNAPSHOT_EXPORTS = {
    'README.txt': 'README.md',
    'NOTICE.txt': 'NOTICE',
    'PUBLICATION.txt': 'PUBLICATION.md',
    'weighted_numerator_proof.tex': 'manuscript/weighted_numerator_proof.tex',
    'weighted_numerator_lemma.tex': 'manuscript/weighted_numerator_lemma.tex',
    'Challenge.lean': K + 'src/Challenge.lean',
    'Solution.lean': K + 'src/Solution.lean',
    'comparator.json': K + 'comparator.json',
    'judge.log': K + 'judge.log',
    'result.json': K + 'result.json',
    'control-results.json': K + 'control-results.json',
    'export-targets.json': K + 'export-targets.json',
    'challenge-source-audit.json': K + 'challenge-source-audit.json',
}
PUBLIC_ONLY = {'manuscript.pdf'}
DERIVED = {'source-sha256.json', 'source-public.tar.gz', 'SHA256SUMS.txt', 'collection.json'}
PUBLIC_FILES = set(SNAPSHOT_EXPORTS) | PUBLIC_ONLY | DERIVED
ENDPOINTS = ['WeightedQRH.beta_le_theta', 'WeightedQRH.hecke_nonzero', 'WeightedQRH.dirichlet_nonzero',
             'WeightedQRH.zeta_nonzero', 'OAI.riemannZeta_ne_zero_of_10499_12000_lt_re',
             'OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re',
             'OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_10499_12000_lt_re']
ACCEPTS = [f'{k} kernel accepts the solution' for k in ('con-ron', 'nanoda', 'Lean default')]
REJECTS = [f'{k} kernel rejected the solution' for k in ('con-ron', 'nanoda', 'Lean default')]
OKAY = 'Your solution is okay!'
MISMATCH = 'Challenge and solution theorem statement do not match'
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|unsafe|implemented_by|extern|skipKernelTC|native_decide|ofReduceBool|'
                       r'trustCompiler|run_cmd|run_elab|run_meta|addDecl|elab|macro_rules|macro|syntax|opaque|'
                       r'partial|csimp|initialize|#eval)\b')
HEX64 = re.compile(r'^[0-9a-f]{64}$')
# Private metadata beyond the shared publication PATTERNS (which this script does not change).
PRIVATE = {
    'local temporary path': re.compile(r'/private/(?:tmp|var)/|/var/folders/'),
    'agent scratch path': re.compile(r'claude-[0-9]+|scratchpad', re.I),
    'bare UUID': re.compile(r'\b[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}\b'),
}
EMAIL = re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}')
EMAIL_ALLOWED = re.compile(r'(?:[A-Za-z0-9._%+-]+@users\.noreply\.github\.com|noreply@anthropic\.com)')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def demand(condition, message):
    if not condition:
        raise ValueError(message)


def manifest_text(manifest):
    return json.dumps(manifest, indent=2) + '\n'


def strip_lean(text):
    """Remove (nested) block comments, line comments and string literal contents."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('-/', i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append('\n' if text[i] == '\n' else '')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append('""')
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def scan_private(name, text):
    """Reject private metadata that the shared PATTERNS do not cover."""
    for label, pattern in PRIVATE.items():
        if pattern.search(text):
            # Never echo the sensitive value.
            raise ValueError(f'Publication rejected ({label}): {name}')
    if any(not EMAIL_ALLOWED.fullmatch(m.group(0)) for m in EMAIL.finditer(text)):
        raise ValueError(f'Publication rejected (e-mail address): {name}')


def scan_archive(archive):
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            scan_private(member.name, tar.extractfile(member).read().decode('utf-8'))


def scan_pdf(name, data):
    """PDFs skip the UTF-8 scan: inspect raw and Flate-decoded streams for private metadata."""
    demand(data.startswith(b'%PDF-'), f'Not a PDF: {name}')
    blobs = [data]
    for match in re.finditer(rb'stream\r?\n(.*?)\r?\nendstream', data, re.S):
        try:
            blobs.append(zlib.decompress(match.group(1)))
        except zlib.error:
            pass
    text = b'\n'.join(blobs).decode('latin-1')
    for label, pattern in PATTERNS.items():
        if pattern.search(text):
            raise ValueError(f'Publication rejected ({label}): {name}')
    scan_private(name, text)


def axiom_sets(log):
    found = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        found[name] = {a.strip() for a in body.split(',') if a.strip()}
    return found


def build_archive(proof, names):
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode='wb', filename='', mtime=0) as zipped:
        with tarfile.open(fileobj=zipped, mode='w', format=tarfile.USTAR_FORMAT) as tar:
            for name in names:
                data = (proof / name).read_bytes()
                item = tarfile.TarInfo(f'{ID}/{name}')
                item.size, item.mode, item.mtime = len(data), 0o644, 0
                tar.addfile(item, io.BytesIO(data))
    return buffer.getvalue()


def regenerate(root, status):
    proof, public = root / 'proofs' / ID, root / 'public/proofs' / ID
    names = approved_files(proof)
    for name in names:
        scan_private(name, (proof / name).read_text())
    demand(set(SNAPSHOT_EXPORTS.values()) <= set(names), 'A public export is outside the reviewed allowlist')
    public.mkdir(parents=True, exist_ok=True)
    for path in public.iterdir():
        demand(path.is_file() and not path.is_symlink() and path.name in PUBLIC_FILES,
               f'Unexpected public file: {path.name}')
    for name in PUBLIC_ONLY:
        demand((public / name).is_file(), f'Missing reviewed public file: {name}')
    if status is None:
        status = json.loads((public / 'collection.json').read_text())['status']
    demand(status in STATUSES, 'Invalid collection status')
    manifest = {name: sha((proof / name).read_bytes()) for name in names}
    (root / 'proofs' / (ID + '.sha256.json')).write_text(manifest_text(manifest))
    for target, source in SNAPSHOT_EXPORTS.items():
        (public / target).write_bytes((proof / source).read_bytes())
    (public / 'source-sha256.json').write_text(manifest_text(manifest))
    archive = build_archive(proof, names)
    (public / 'source-public.tar.gz').write_bytes(archive)
    check_archive(public / 'source-public.tar.gz', proof, manifest)
    (public / 'SHA256SUMS.txt').write_text(sha(archive) + '  source-public.tar.gz\n')
    files = {name: sha((public / name).read_bytes()) for name in sorted(PUBLIC_FILES - {'collection.json'})}
    collection = {'status': status, 'files': files, 'snapshot_exports': SNAPSHOT_EXPORTS}
    (public / 'collection.json').write_text(json.dumps(collection, indent=2) + '\n')
    print(json.dumps({'snapshot_files': len(names), 'archive_sha256': sha(archive), 'status': status}))


def check(root, catalogue_path):
    proof, public = root / 'proofs' / ID, root / 'public/proofs' / ID
    # 1. Reviewed snapshot: allowlist equals the files on disk; each file passes the privacy scans.
    names = approved_files(proof)
    for name in names:
        scan_private(name, (proof / name).read_text())
    manifest_file = root / 'proofs' / (ID + '.sha256.json')
    manifest = json.loads(manifest_file.read_text())
    demand(list(manifest) == names, 'Snapshot manifest and allowlist differ')
    demand(manifest_file.read_text() == manifest_text(manifest), 'Snapshot manifest is not canonical JSON')
    for name, digest in manifest.items():
        demand(sha((proof / name).read_bytes()) == digest, f'Snapshot checksum mismatch: {name}')
    read = lambda name: (proof / name).read_text()
    load = lambda name: json.loads(read(name))
    lean = [n for n in names if n.endswith('.lean')]
    demand(len([n for n in lean if n.startswith('formalization/WeightedQRH/')]) == 228, 'Expected 228 proof modules')
    demand(len([n for n in lean if n.startswith('formalization/ComparatorChallenges/')]) == 3,
           'Expected 3 challenge modules')
    for name in lean:
        if not name.startswith('formalization/'):
            continue
        hits = FORBIDDEN.findall(strip_lean(read(name)))
        allowed = name.startswith('formalization/ComparatorChallenges/') and set(hits) == {'sorry'}
        demand(not hits or allowed, f'Forbidden Lean keyword in {name}')

    # 2. Publication transformations: recorded, published bytes authenticated, sources unchanged.
    changes = {c['path']: c for c in load('publication-transformations.json')['changes']}
    for path, change in changes.items():
        demand(path in manifest and change['published_sha256'] == manifest[path]
               and HEX64.match(change['original_sha256']) and change['original_sha256'] != change['published_sha256'],
               f'Invalid publication transformation: {path}')
        demand(path.endswith(('.json', '.log', '.txt')) or path == 'evidence/isolated-rebuild/run_comparator.sh',
               f'Source bytes must not be transformed: {path}')
    original = lambda path: changes.get(path, {}).get('original_sha256', manifest.get(path))

    # 3. Public downloads, archive and checksums.
    demand(public.is_dir() and not public.is_symlink(), 'Missing public evidence directory')
    entries = list(public.iterdir())
    demand(all(p.is_file() and not p.is_symlink() for p in entries), 'Public evidence must be flat regular files')
    inventory = {p.name for p in entries}
    demand(inventory == PUBLIC_FILES, 'Public evidence inventory differs from the reviewed list')
    collection = json.loads((public / 'collection.json').read_text())
    demand(set(collection) == {'status', 'files', 'snapshot_exports'} and collection['status'] in STATUSES,
           'Invalid public collection')
    demand(set(collection['files']) == inventory - {'collection.json'}, 'Public collection is incomplete')
    for name, digest in collection['files'].items():
        demand(PurePosixPath(name).name == name and sha((public / name).read_bytes()) == digest,
               f'Public checksum mismatch: {name}')
    demand(collection['snapshot_exports'] == SNAPSHOT_EXPORTS, 'Unexpected public snapshot exports')
    for target, source in SNAPSHOT_EXPORTS.items():
        demand(source in manifest and (public / target).read_bytes() == (proof / source).read_bytes(),
               f'Public copy differs from snapshot: {target}')
    demand((public / 'source-sha256.json').read_bytes() == manifest_file.read_bytes(),
           'Public source manifest differs from the snapshot manifest')
    archive = public / 'source-public.tar.gz'
    check_archive(archive, proof, manifest)
    scan_archive(archive)
    demand((public / 'SHA256SUMS.txt').read_text() == sha(archive.read_bytes()) + '  source-public.tar.gz\n',
           'Archive checksum mismatch')
    for name in sorted(inventory):
        data = (public / name).read_bytes()
        if name.endswith('.pdf'):
            scan_pdf(name, data)
        elif not name.endswith('.gz'):
            check_content(name, data)
            scan_private(name, data.decode('utf-8'))

    # 4. The recorded three-kernel run.
    report = load(K + 'result.json')
    demand(report['status'] == 'PASS' and report['theta'] == THETA, 'Kernel report is not a PASS at 10499/12000')
    demand(report['declarations'] == NAMES and report['kernels'] == KERNELS
           and sorted(report['allowed_axioms']) == AXIOMS, 'Kernel report scope differs')
    demand(report['judge_exit_code'] == 0 and report['preflight'] == 'passed'
           and report['acceptance_markers'] == {k: True for k in ('con-ron', 'nanoda', 'Lean default')},
           'Kernel acceptance is incomplete')
    verified_at = report['verified_at_utc']
    demand(datetime.fromisoformat(verified_at).utcoffset().total_seconds() == 0, 'Verification time is not UTC')
    phases = {p['name']: p for p in report['phases']}
    demand(phases['preflight-controls']['passed'] is True and phases['judge']['exit_code'] == 0
           and all(phases[f'{s}-{m}']['exit_code'] == 0 for s in ('compile', 'export') for m in ('Challenge', 'Solution'))
           and all(phases[f'export-{m}']['header_ok'] is True for m in ('Challenge', 'Solution')),
           'A kernel-run phase failed')
    for export in ('Challenge', 'Solution'):
        item = report['exports'][export]
        demand(HEX64.match(item['sha256']) and item['bytes'] > 0, f'Missing {export} export record')
    for path, digest in report['artifacts'].items():
        demand(original(K + path) == digest, f'Kernel artifact differs from the recorded run: {path}')
    template = (root / TEMPLATE).read_bytes()
    demand(sha(template) == TEMPLATE_SHA256 and template.decode().count(TEMPLATE_LITERAL) == 3,
           'Tracker challenge template changed')
    challenge = read(K + 'src/Challenge.lean')
    demand(challenge == template.decode().replace(TEMPLATE_LITERAL, '10499 / 12000'),
           'Challenge is not the fixed template with only the literal replaced')
    demand(report['challenge_template_sha256'] == TEMPLATE_SHA256
           and report['challenge_sha256'] == manifest[K + 'src/Challenge.lean']
           and report['solution_sha256'] == manifest[K + 'src/Solution.lean'], 'Kernel sources differ from report')
    solution = read(K + 'src/Solution.lean')
    lines = [line for line in solution.split('\n') if line != 'import WeightedQRH.Statements']
    demand(len(lines) == len(solution.split('\n')) - 1
           and '\n'.join('  sorry' if line.startswith('  exact ') else line for line in lines) == challenge
           and not FORBIDDEN.findall(strip_lean(solution)), 'Solution does not restate the exact challenge')
    demand('WeightedQRH' not in report['challenge_LEAN_PATH']
           and '/work/qrh-proof/formalization' not in report['challenge_LEAN_PATH'],
           'Challenge search path includes the proof')
    config = load(K + 'comparator.json')
    kernels = config['external_kernels']
    demand(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution'
           and config['theorem_names'] == NAMES and config['definition_names'] == []
           and sorted(config['permitted_axioms']) == AXIOMS and set(kernels) == {'nanoda', 'con-ron'}
           and len(kernels['nanoda']) == 1 and kernels['nanoda'][0].endswith('/bin/nanoda_bin')
           and kernels['con-ron'][0].endswith('/bin/con-ron') and kernels['con-ron'][1:] == ['--jobs=2'],
           'Unexpected Comparator configuration')
    targets = load(K + 'export-targets.json')
    demand(targets[:4] == ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] and targets[4:7] == NAMES
           and sorted(targets[7:10]) == AXIOMS, 'Unexpected export targets')
    judge = read(K + 'judge.log')
    demand(all(m in judge for m in ACCEPTS + [OKAY]) and re.search(r'con-ron: accepted \d+ declarations', judge)
           and not any(m in judge for m in REJECTS), 'Judge log lacks the three acceptances')
    controls = load(K + 'control-results.json')['cases']
    demand([(c['name'], c['exit_code'], c['log']) for c in controls]
           == [('matching', 0, 'controls/matching.log'), ('mismatched', 1, 'controls/mismatched.log'),
               ('ill-typed', 1, 'controls/ill-typed.log')], 'Unexpected preflight controls')
    matching, mismatched, ill = (read(K + c['log']) for c in controls)
    demand(all(m in matching for m in ACCEPTS + [OKAY]), 'Matching control was not accepted by all kernels')
    demand(MISMATCH in mismatched and OKAY not in mismatched, 'Mismatched control was not rejected')
    demand(all(m in ill for m in REJECTS) and OKAY not in ill, 'Ill-typed control was not rejected by all kernels')
    audit = load(K + 'challenge-source-audit.json')
    demand(audit['challenge_sha256'] == report['challenge_sha256'] and audit['template_sha256'] == TEMPLATE_SHA256
           and audit['challenge_LEAN_PATH_has_no_WeightedQRH_or_fork'] is True, 'Challenge source audit differs')
    pinned = {f['path']: f for f in audit['protected_definition_files']}
    demand(set(pinned) == set(DEFINITIONS), 'Unexpected protected definition files')
    for path, (source, digest) in DEFINITIONS.items():
        item = pinned[path]
        demand(item['source'] == source and item['sha256'] == digest and item['matches_pinned_blob'] is True
               and item['git_blob'] == item['git_blob_at_checkout_head']
               and item['checkout_head'] == source.split()[1], f'Definition file not pinned upstream: {path}')
    pins = load(K + 'tool-pins.json')
    demand(report['tool_sha256'] == TOOLS, 'Kernel report binaries differ from the pinned darwin_aarch64 tools')
    demand(pins['judge_toolchain']['release_sha256'] == RELEASE_SHA256
           and pins['judge_toolchain']['binaries_sha256'] == TOOLS
           and pins['driver']['path'] == DRIVER and pins['driver']['sha256'] == manifest[DRIVER],
           'Tool pins differ from the recorded run')

    # 5. Axiom reports of the Lake build and the isolated rebuild; default-kernel Comparator logs.
    for log in ('evidence/lake/lake-build.log', 'evidence/isolated-rebuild/WeightedQRH.FinalAxioms.log'):
        sets = axiom_sets(read(log))
        demand(all(name in sets for name in ENDPOINTS) and all(s <= set(AXIOMS) for s in sets.values()),
               f'Axiom report incomplete or non-standard: {log}')
    for name in ('Zeta', 'Dirichlet', 'Hecke'):
        for log in (f'evidence/lake/comparator-lake-WeightedQRH{name}.log',
                    f'evidence/comparator/comparator-WeightedQRH{name}.log'):
            text = read(log)
            demand('Lean default kernel accepts the solution' in text and OKAY in text, f'Comparator rejected: {log}')
    negative = read('evidence/comparator/comparator-NegControl.log')
    demand(MISMATCH in negative and OKAY not in negative, 'Negative Comparator control was accepted')
    zeta = read(ZETA + '.lean')
    demand(zeta.count('(10499 / 12000 : ℝ)') == 1
           and read(NEGATIVE + '.lean') == zeta.replace('(10499 / 12000 : ℝ)', '(1 / 2 : ℝ)')
           and read(NEGATIVE + '.json') == read(ZETA + '.json').replace('WeightedQRHZeta', 'WeightedQRHNegControl')
           and 'ComparatorChallenges.WeightedQRHNegControl' in negative,
           'Negative control is not the zeta challenge at 1/2')

    # 6. Catalogue record binding.
    records = json.loads(catalogue_path.read_text())['records']
    matches = [r for r in records if r['id'] == ID]
    demand(len(matches) == 1, 'Catalogue record missing')
    record = matches[0]
    demand(f"{record['theta']['numerator']}/{record['theta']['denominator']}" == THETA,
           'Catalogue boundary differs from the kernel report')
    module = 'formalization/' + ENTRYPOINT['module'].replace('.', '/') + '.lean'
    demand(record['entrypoint'] == ENTRYPOINT and module in manifest
           and 'theorem LFunction_ne_zero_of_10499_12000_lt_re' in read(module)
           and f"exact {ENTRYPOINT['declaration']} χ hs hpole" in solution,
           'Catalogue entrypoint is not the all-Dirichlet theorem restated by the checked Solution')
    for ref in record['references']:
        url = ref['url']
        if not url.startswith('https://'):
            demand((url.startswith(f'proofs/{ID}/') and url[len(f'proofs/{ID}/'):] in inventory)
                   or (url.startswith(REPLAY_PREFIX) and url[len(REPLAY_PREFIX):] in REPLAY_REFERENCES),
                   f'Reference outside this package: {url}')
    if record['status'] == 'framework-verified':
        # Historical author logs cannot grant the site's independently verified status.
        # The protected maintainer receipt binds every source file and the actual run.
        subprocess.run(['node', str(Path(__file__).resolve().parent / 'check-akashlevy-kernels.mjs'),
                        str(root), str(catalogue_path)], check=True)
    else:
        demand(record['status'] == 'verification-pending' and record['first_verified_at'] == '',
               'Pending record cannot carry a verification date')
    return len(names), len(inventory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--catalogue', type=Path)
    parser.add_argument('--regenerate', action='store_true')
    parser.add_argument('--status', choices=STATUSES)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.regenerate:
        regenerate(root, args.status)
        return
    snapshot, downloads = check(root, args.catalogue or root / 'catalogue/results.json')
    print(f'{ID}: {snapshot} snapshot files and {downloads} historical downloads checked; catalogue verification status validated separately.')


if __name__ == '__main__':
    main()
