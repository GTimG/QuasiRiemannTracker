"""Check the contributor dossier without executing submitted proof code.

These checks bind published bytes and reported outcomes. They do not replace an
independent maintainer replay or authorize a verification-status upgrade.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
from publication_policy import approved_files, check_archive

ROOT = Path(__file__).resolve().parents[1]
NAME = 'cycle25-quartic-20261010'
THETA = '683505193/781250000'
ROOTS = ['Cycle25Verification.' + n for n in (
    'allDirichlet', 'zeta', 'allHecke', 'exactAllDirichlet', 'exactZeta',
    'exactAllHecke', 'plainMoment')]
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError('Cycle25: ' + message)


def check(root=ROOT):
    proof = root / 'proofs' / NAME
    public = root / 'public/proofs' / NAME
    names = approved_files(proof)
    manifest = load(root / 'proofs' / (NAME + '.sha256.json'))
    require(set(names) == set(manifest), 'source manifest differs from allowlist')
    for path, expected in manifest.items():
        require(digest(proof / path) == expected, 'source checksum mismatch: ' + path)
    require(load(public / 'source-sha256.json') == manifest, 'downloaded source manifest differs')
    check_archive(public / 'source-public.tar.gz', proof, manifest)
    checksum, archive = (public / 'SHA256SUMS.txt').read_text().strip().split('  ')
    require(archive == 'source-public.tar.gz' and checksum == digest(public / archive), 'archive checksum differs')
    collection = load(public / 'collection.json')
    require(collection['id'] == NAME and collection['status'] == 'verification-pending', 'collection must remain pending')
    require(set(collection['files']) == {p.name for p in public.iterdir() if p.name != 'collection.json'}, 'public collection incomplete')
    for path, expected in collection['files'].items():
        require(PurePosixPath(path).name == path and digest(public / path) == expected, 'public checksum mismatch')
    for target, source in collection['snapshot_exports'].items():
        require(target in collection['files'] and PurePosixPath(target).name == target
                and source in manifest and (public / target).read_bytes() == (proof / source).read_bytes(), 'public export differs')
    paper = load(proof / 'manuscript/paper-files.json')
    require(set(paper['files']) == {'paper.md', 'paper.tex', 'paper.pdf'}, 'unexpected manuscript files')
    for filename, expected in paper['files'].items():
        path = public / filename if filename == 'paper.pdf' else proof / 'manuscript' / filename
        require(digest(path) == expected, 'manuscript checksum differs')
    require((public / 'paper.pdf').read_bytes().startswith(b'%PDF-') and (public / 'paper.pdf').stat().st_size == paper['pdf_bytes'], 'PDF missing or invalid')
    require(collection['paper_sha256'] == digest(public / 'paper.pdf'), 'PDF collection checksum differs')
    inventory = load(proof / 'reproduce/frozen-source-inventory.json')['sources']
    expected = {'formalization/' + item['path']: item['sha256'] for item in inventory}
    actual = {p.relative_to(proof).as_posix() for namespace in ('Cycle25', 'OAI', 'ZetaZeroFree')
              for p in (proof / 'formalization' / namespace).rglob('*.lean')}
    require(len(expected) == 3224 and actual == set(expected), 'finished Lean closure differs')
    require(all(manifest[p] == h for p, h in expected.items()), 'frozen mathematical source differs')
    record, = [r for r in load(root / 'catalogue/results.json')['records'] if r['id'] == NAME]
    require(record['status'] == 'verification-pending' and record['first_verified_at'] == '', 'contributor evidence cannot mint maintainer verification')
    require('/'.join(record['theta'][k] for k in ('numerator', 'denominator')) == THETA, 'catalogue boundary differs')
    require(record['entrypoint'] == {'module': 'Cycle25.Assembly.Final.Endpoint', 'declaration': 'Cycle25.dirichlet_nonzero_catalogue'}, 'catalogue entrypoint differs')
    evidence = proof / 'evidence/multi-kernel'
    report = load(evidence / 'result.json')
    config = load(evidence / 'comparator.json')
    require(report['status'] == 'PASS' and report['theta_rational'] == THETA, 'kernel report boundary differs')
    require(report['declarations'] == ROOTS == config['theorem_names'], 'seven checked roots differ')
    require(report['kernels'] == ['Lean default', 'nanoda', 'con-ron'], 'three-kernel evidence incomplete')
    require(set(report['allowed_axioms']) == AXIOMS == set(config['permitted_axioms']), 'unexpected axiom boundary')
    require(report['preflight_passed'] and report['statement_definitions_compared'], 'statement/control gates absent')
    require(report['source_compiler'] == '4.34.1' and report['judge_toolchain'] == '4.35.0-rc2', 'compiler/checker pins differ')
    controls = load(evidence / 'control-results.json')
    require(controls['passed'] and controls['checks'] == ['matching proof accepted', 'mismatched statement rejected', 'ill-typed proof rejected'], 'controls incomplete')
    require(load(evidence / 'judge.outcome.json')['returncode'] == 0, 'judge exited unsuccessfully')
    log = (evidence / 'judge.log').read_text()
    require(all(line in log for line in ['con-ron kernel accepts the solution', 'nanoda kernel accepts the solution', 'Lean default kernel accepts the solution', 'Your solution is okay!']), 'acceptance transcript incomplete')
    build = load(proof / 'evidence/clean-build/result.json')
    require(build['passed'] and build['compiled_modules'] == 301 and build['reused_upstream_modules'] == 2923, 'clean-build scope differs')
    require(load(proof / 'reproduce/portability-validation.json')['passed'], 'portable dependency checks failed')
    return len(names)


if __name__ == '__main__':
    print(f'Cycle25 contributor publication checks passed: {check()} source files; maintainer review remains pending.')
