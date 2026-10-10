#!/usr/bin/env python3
"""Maintainer-run, offline-sandboxed replay of the pinned Akash Levy contribution.

Use this file and its pins from a reviewed, protected checkout. A PR must never
supply this driver, the profile, tool binaries, or the canonical library. The
profile only locates an already approved dependency build and checker bundle.
Every process that can load candidate data runs inside real Palomar confinement.
"""
from pathlib import Path, PurePosixPath
import argparse
import concurrent.futures
import datetime
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import stat
import zipfile
import time
import traceback
import urllib.request

HERE = Path(__file__).resolve().parent
PALOMAR_COMMIT = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
PALOMAR_SCRIPT = 'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def artifact_inventory(work, paths):
    """Never follow candidate-written log links or hash unbounded diagnostics."""
    result, total = {}, 0
    for path in paths:
        relative = path.relative_to(work)
        safe_relative(relative.as_posix())
        current = work
        for part in relative.parts:
            current = current / part
            require(not current.is_symlink(), 'Artifact symlink rejected')
        info = path.stat()
        require(stat.S_ISREG(info.st_mode), 'Artifact must be a regular file')
        # Proof streams are large but are created by the trusted exporter outside
        # candidate mounts and remain private. All public diagnostics are bounded.
        if relative.parts[0] != 'exports':
            total += info.st_size
            require(info.st_size <= 12*1024**2 and total <= 128*1024**2,
                    'Diagnostic artifact resource limit')
        name = relative.as_posix()
        require(name not in result and len(result) < 4096, 'Artifact inventory limit or duplicate')
        result[name] = digest(path)
    return result


def safe_relative(name):
    path = PurePosixPath(name)
    require(isinstance(name, str) and name and not path.is_absolute()
            and '..' not in path.parts and '\\' not in name
            and name == path.as_posix() and not any(ord(c) < 32 for c in name),
            'Unsafe relative path')
    return path


def imports(text):
    """Read the pinned import header without evaluating Lean or Python."""
    output, index, depth = [], 0, 0
    while index < len(text):
        if text[index:index+2] == '/-': depth += 1; index += 2; continue
        if depth and text[index:index+2] == '-/': depth -= 1; index += 2; continue
        if depth: output.append('\n' if text[index] == '\n' else ' '); index += 1; continue
        if text[index:index+2] == '--':
            end = text.find('\n', index); index = len(text) if end < 0 else end; continue
        output.append(text[index]); index += 1
    result = []
    for line in ''.join(output).splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if match:
            for part in match[1].split():
                if part == 'all': continue
                require(bool(re.fullmatch(r'[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*', part)), 'Unsafe module name')
                result.append(part)
        elif line.strip() and line.strip() not in ('module', 'prelude'): break
    return result


def checked_zip(data, *, count_limit, byte_limit, member_limit):
    archive = zipfile.ZipFile(io.BytesIO(data))
    seen, total = set(), 0
    for member in archive.infolist():
        name = member.filename.rstrip('/')
        safe_relative(name)
        require(name not in seen, 'Duplicate archive path')
        seen.add(name)
        total += member.file_size
        kind = stat.S_IFMT(member.external_attr >> 16)
        require(kind in (0, stat.S_IFREG, stat.S_IFDIR), 'Archive link or special file')
        require(not (member.flag_bits & 1), 'Encrypted archive member')
        require(len(seen) <= count_limit and total <= byte_limit and member.file_size <= member_limit,
                'Source archive resource limit')
    return archive


def unpack_source(payload, inputs, destination):
    """Authenticate the full prepared source bundle without executing author code."""
    bundle = inputs['source_bundle']
    require(len(payload) == bundle['bytes'] and hashlib.sha256(payload).hexdigest() == bundle['sha256'],
            'Source bundle hash or size mismatch')
    with checked_zip(payload, count_limit=4000, byte_limit=80*1024**2, member_limit=2*1024**2) as archive:
        require(set(archive.namelist()) == {r['path'] for r in inputs['source_manifest']}, 'Source inventory differs')
        expected = {}
        for row in inputs['source_manifest']:
            name = str(safe_relative(row['path']))
            require(name == row['module'].replace('.', '/') + '.lean' and name not in expected, 'Invalid source destination')
            data = archive.read(name)
            require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'], 'Source hash or size mismatch')
            target = destination / name
            require(not target.exists() and not target.is_symlink(), 'Refusing source overwrite')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            expected[name] = row['sha256']
    return expected


def canonical_sources():
    """Fixed rational contract; no candidate-controlled predicates or hypotheses."""
    statement = '''namespace QRHBoundsPR6
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  DIRICHLET_PROOF

theorem zeta {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  ZETA_PROOF

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  HECKE_PROOF
end QRHBoundsPR6
'''
    challenge = 'import Mathlib.NumberTheory.LSeries.DirichletContinuation\nimport OAI.NumberTheory.DirichletL.Hecke.IdealBridge\n\n' + statement
    solution = 'import WeightedQRH.Statements\n\n' + statement
    for placeholder, proof in {
        'DIRICHLET_PROOF': 'exact OAI.DirichletCharacter.LFunction_ne_zero_of_10499_12000_lt_re χ hs hpole',
        'ZETA_PROOF': 'exact OAI.riemannZeta_ne_zero_of_10499_12000_lt_re hs',
        'HECKE_PROOF': 'exact WeightedQRH.hecke_nonzero χ s hs hpole',
    }.items():
        challenge = challenge.replace(placeholder, 'sorry')
        solution = solution.replace(placeholder, proof)
    return challenge, solution


# This reviewed scheduler executes *inside* the sandbox. Logs and exit statuses
# from it are diagnostics only; only the external Comparator can accept a proof.
BUILDER = '''from pathlib import Path
import concurrent.futures,json,subprocess,time
root=Path(__file__).resolve().parent.parent
graph=json.loads((root/'controller/graph.json').read_text())
done=set(); pending=set(graph); active={}; failed=[]; started=time.time()
def compile_one(module):
 rel=module.replace('.','/')
 out=root/'candidate-lib'/(rel+'.olean'); out.parent.mkdir(parents=True,exist_ok=True)
 with (root/'candidate-logs'/(module+'.log')).open('w') as log:
  return subprocess.run(['lean','-j1','-DautoImplicit=false','-DwarningAsError=false','-R',str(root/'source'),'-o',str(out),rel+'.lean'],cwd=root/'source',stdout=log,stderr=subprocess.STDOUT,timeout=1800).returncode
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
 while pending or active:
  for module in sorted(pending):
   if len(active)>=8 or failed: break
   if any(dep in graph and dep not in done for dep in graph[module]): continue
   pending.remove(module); active[pool.submit(compile_one,module)]=module
  if not active: break
  ready,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in ready:
   module=active.pop(future)
   try: code=future.result()
   except Exception as error: code=1; print(type(error).__name__,str(error),flush=True)
   if code: failed.append(module)
   else: done.add(module)
  print(json.dumps({'compiled':len(done),'total':len(graph),'failed':failed,'pending':len(pending),'seconds':round(time.time()-started,1)}),flush=True)
if failed or pending: raise SystemExit(1)
'''


def run(profile, work):
    require(sys.platform == 'linux' and os.getuid() != 0, 'An unprivileged Linux worker is required')
    require(not sys.flags.optimize, 'Do not run the verifier with Python optimization')
    profile = json.loads(profile.read_text())
    baseline = Path(profile['baseline']).resolve()
    checkers = Path(profile['checkers']).resolve()
    evidence = Path(profile['evidence']).resolve()
    old = baseline / 'toolchains/lean-4.34.1-linux'
    judge = checkers / 'tools/lean-4.35.0-rc2-linux'
    ref = checkers / 'tools/palomar'
    inputs = json.loads((HERE / 'pins.json').read_text())
    work.mkdir(mode=0o700, parents=False, exist_ok=False)
    started = time.monotonic()
    def status(phase, **extra):
        value = {'phase': phase, 'updated_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 'elapsed_seconds': round(time.monotonic()-started, 2), **extra}
        write_json(work / 'status.json', value)
        print(json.dumps(value), flush=True)
    try:
        require(subprocess.check_output(['git', '-C', str(ref), 'rev-parse', 'HEAD'], text=True).strip() == PALOMAR_COMMIT, 'Palomar revision mismatch')
        require(not subprocess.check_output(['git', '-C', str(ref), 'status', '--porcelain', '--untracked-files=no'], text=True).strip(), 'Palomar checkout changed')
        require(digest(ref / 'scripts/verify_submission.py') == PALOMAR_SCRIPT, 'Palomar driver hash mismatch')
        os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:8])
        sys.path.insert(0, str(ref))
        from scripts import verify_submission as v
        v._BWRAP = Path('/usr/bin/bwrap')
        v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, 'memory_high_percent': 3, 'memory_max_percent': 4,
                                 'tasks_max': 256, 'open_files_max': 65536, 'file_size_max_bytes': 32 * 1024**3}
        v.install_execution_deadline(budget_seconds=10800)
        bundled = {name: judge / 'bin' / name for name in v.TOOLCHAIN_TOOLS}
        exporter = checkers / 'tools/lean4export/.lake/build/bin/lean4export'
        python, touch = Path('/usr/bin/python3').resolve(), Path('/usr/bin/touch').resolve()
        leantar = old / 'bin/leantar'
        tools = v.tool_snapshot([*bundled.values(), v._BWRAP, old / 'bin/lean', exporter, python, touch, leantar])
        expected_tools = {Path(p.replace('BASELINE', str(baseline)).replace('CHECKERS', str(checkers))): sha for p, sha in inputs['tool_pins'].items()}
        require(tools == expected_tools, 'Tool binary pins differ from the approved environment')
        write_json(work / 'tool-pins.json', {str(p): sha for p, sha in tools.items()})
        for name in ['source', 'trusted-lib', 'candidate-deps', 'candidate-lib', 'challenge-src', 'challenge-lib', 'solution-src',
                     'solution-lib', 'exports', 'controller', 'candidate-home', 'candidate-tmp', 'candidate-logs',
                     'trusted-home', 'trusted-tmp', 'logs', 'downloads', 'cache-extraction', 'preflight', 'controls']:
            (work / name).mkdir()
        common = {'PATH': str(old / 'bin') + ':/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LEAN_NUM_THREADS': '1', 'LEAN_ABORT_ON_PANIC': '1'}
        trusted_env = {**common, 'HOME': str(work / 'trusted-home'), 'TMPDIR': str(work / 'trusted-tmp'),
                       'LEAN_PATH': str(work / 'challenge-lib') + ':' + str(work / 'trusted-lib')}
        status('genuine-sandbox-and-checker-preflight', status='running')
        probe = work / 'controller/trusted.txt'; probe.write_text('positive read control\n')
        v.verify_sandbox_confinement(work / 'controller/denied-write', work / 'denied-read', positive_read=probe,
            python=python, touch=touch, cwd=work / 'controller', environment=trusted_env,
            writable_directories=[work / 'trusted-home', work / 'trusted-tmp'],
            protected_write_directories=[work / 'controller'], readable_paths=[work / 'controller', *v.system_readable_paths()],
            executable_paths=[old, Path('/usr')], tools=tools)
        control_cases = []
        original_judge = v.judge_exports
        def record_control(**kwargs):
            proc = original_judge(**kwargs)
            name = kwargs['solution_export'].stem
            require(name in ['PalomarPreflightSolution', 'PalomarPreflightWrong', 'PalomarPreflightIllTyped'], 'Unexpected control')
            log = name + '.log'
            (work / 'controls' / log).write_text(proc.stdout + '\n' + proc.stderr)
            control_cases.append({'name': name, 'exit_code': proc.returncode, 'log': log})
            return proc
        v.judge_exports = record_control
        try:
            v.comparator_preflight(work / 'preflight', lean=bundled['lean'], leanexport=bundled['leanexport'],
                lake=bundled['lake'], lean_prefix=judge, bwrap=v._BWRAP, kernels=v.protected_kernels(bundled),
                primitives=v.primitive_targets(judge), environment={**trusted_env, 'PATH': str(judge / 'bin') + ':/usr/bin:/bin'},
                executable_paths=[judge, v._BWRAP, Path('/usr')],
                tools=tools, timeout=300)
        finally:
            v.judge_exports = original_judge
        require([c['exit_code'] for c in control_cases] == [0, 1, 1], 'Checker controls incomplete')
        write_json(work / 'checker-controls.json', {'status': 'PASS', 'cases': control_cases,
            'executed_before_candidate': True, 'finished_at': datetime.datetime.now(datetime.timezone.utc).isoformat()})
        write_json(work / 'preflight-result.json', {'status': 'PASS', 'sandbox': 'real bubblewrap, cgroups, seccomp, empty-root allowlist',
            'controls': ['filesystem', 'network', 'process namespaces', 'environment', 'positive acceptance', 'statement mismatch', 'ill-typed export']})
        status('freeze-approved-canonical-library', status='running')
        graph_path = baseline / 'audit/final-source-graph.json'
        require(digest(graph_path) == inputs['trusted_graph_sha256'], 'Approved source graph changed')
        trusted_graph = json.loads(graph_path.read_text())
        library_manifest = {}
        for module, source_hash in inputs['trusted_module_sources'].items():
            info = trusted_graph[module]
            require(info['sha256'] == source_hash and digest(baseline / info['source']) == source_hash, 'Approved source changed: ' + module)
            rel = module.replace('.', '/')
            require((baseline / 'build/source' / (rel + '.olean')).is_file(), 'Missing approved dependency: ' + module)
            for suffix in ['.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig', '.ilean']:
                src = baseline / 'build/source' / (rel + suffix)
                if not src.is_file(): continue
                target = work / 'trusted-lib' / (rel + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, target)
                library_manifest[rel + suffix] = digest(target)
        require(digest(HERE / 'approved-library-manifest.json') == inputs['approved_library_manifest_sha256'], 'Approved manifest changed')
        require(library_manifest == json.loads((HERE / 'approved-library-manifest.json').read_text()), 'Approved compiled library changed')
        write_json(work / 'trusted-library-manifest.json', library_manifest)
        write_json(work / 'dependency-pins.json', {'lake_manifest': inputs['dependency_lock'], 'openai_commit': inputs['openai_source_commit'],
            'source_graph_sha256': inputs['trusted_graph_sha256'], 'library_sha256': digest(work / 'trusted-library-manifest.json')})
        challenge, solution = canonical_sources()
        (work / 'challenge-src/Challenge.lean').write_text(challenge)
        (work / 'solution-src/Solution.lean').write_text(solution)
        config = {'challenge_module': 'Challenge', 'solution_module': 'Solution',
                  'theorem_names': ['QRHBoundsPR6.allDirichlet', 'QRHBoundsPR6.zeta', 'QRHBoundsPR6.allHecke'],
                  'definition_names': [], 'permitted_axioms': sorted(AXIOMS), 'external_kernels': v.protected_kernels(bundled)}
        write_json(work / 'comparator.json', config)
        targets = v.comparator_export_targets(config, v.primitive_targets(judge))
        status('export-trusted-challenge-before-any-candidate', status='running')
        result = v.sandboxed_run([str(old / 'bin/lean'), '-j1', '-o', str(work / 'challenge-lib/Challenge.olean'), 'Challenge.lean'],
            cwd=work / 'challenge-src', environment=trusted_env,
            writable_directories=[work / 'challenge-lib', work / 'trusted-home', work / 'trusted-tmp'],
            readable_paths=[work / 'trusted-lib', *v.system_readable_paths()], executable_paths=[old, Path('/usr')], tools=tools, timeout=600)
        (work / 'logs/challenge-compile.log').write_text(result.stdout + '\n' + result.stderr)
        result = v.export_module('Challenge', targets, output=work / 'exports/Challenge.export', leanexport=exporter,
            cwd=work / 'challenge-src', environment=trusted_env,
            readable_paths=[work / 'challenge-lib', work / 'trusted-lib', *v.system_readable_paths()],
            executable_paths=[old, exporter, Path('/usr')], tools=tools, timeout=1800)
        (work / 'logs/challenge-export.log').write_text(result.stdout + '\n' + result.stderr)
        require(result.returncode == 0, 'Challenge export failed')
        v.verify_export(work / 'exports/Challenge.export')
        challenge_hash = digest(work / 'exports/Challenge.export')
        write_json(work / 'challenge-frozen.json', {'export_sha256': challenge_hash,
            'source_sha256': digest(work / 'challenge-src/Challenge.lean'), 'exported_before_candidate_execution': True})
        status('fetch-source-as-data-only', status='running')
        bundle_path = Path(profile['source_bundle']).resolve()
        require(bundle_path.is_file() and bundle_path.stat().st_size == inputs['source_bundle']['bytes'], 'Missing prepared source bundle')
        expected = unpack_source(bundle_path.read_bytes(), inputs, work / 'source')
        write_json(work / 'submission-manifest.json', inputs['submission_files'])
        compiled = set(inputs['compiled_modules'])
        require(set(expected) == {m.replace('.', '/') + '.lean' for m in compiled}, 'Compiled source inventory differs')
        write_json(work / 'source-manifest.json', expected)
        for name, sha in inputs['evidence_files'].items():
            require(digest(evidence / name) == sha, 'Pinned dependency provenance changed')
        downloads = json.loads((evidence / 'official-mathlib-cache-downloads.json').read_text())['modules']
        key_audit = json.loads((evidence / 'mathlib-cache-key-source-audit.json').read_text())['module_sources']
        selected_cache = {m:r for m,r in downloads.items() if m not in inputs['trusted_module_sources']}
        status('fetch-pinned-official-dependency-cache', status='running', archives=len(selected_cache))
        def fetch_cache(item):
            module, row = item
            source = key_audit[module]
            require(source['cache_key'] == row['url'].rsplit('/', 1)[1], 'Cache key mismatch')
            require(re.fullmatch(r'https://cache\.mathlib\.org/mathlib4-master/f/[0-9a-f]{16}\.ltar', row['url']) is not None, 'Unapproved cache URL')
            relative = source['path'].removeprefix('WORKSPACE/compressed/')
            require(digest(baseline / safe_relative(relative)) == source['sha256'], 'Cache source mismatch: ' + module)
            for attempt in range(3):
                try:
                    # Optional operator cache is read as data, authenticated, then copied.
                    # It is never mounted in a candidate environment or made writable.
                    cached = Path(profile['official_cache']) / source['cache_key'] if profile.get('official_cache') else None
                    if cached is not None and cached.is_file():
                        require(not cached.is_symlink() and cached.stat().st_size == row['bytes'], 'Cached archive size or type mismatch')
                        data = cached.read_bytes()
                    else:
                        with urllib.request.urlopen(urllib.request.Request(row['url'], headers={'User-Agent': 'QRHBounds-MaintainerReplay/1.0'}), timeout=60) as response:
                            data = response.read(20 * 1024**2 + 1)
                    require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'], 'Official cache archive hash mismatch')
                    target = work / 'downloads' / source['cache_key']; target.write_bytes(data)
                    return {'file': str(target), 'base': str(work / 'cache-extraction')}
                except OSError:
                    if attempt == 2: raise
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
            extraction = list(pool.map(fetch_cache, sorted(selected_cache.items())))
        write_json(work / 'cache-downloads.json', {m:{k:r[k] for k in ['url','sha256','bytes']} for m,r in selected_cache.items()})
        write_json(work / 'controller/extraction.json', extraction)
        extract_code = 'import subprocess,json\nfrom pathlib import Path\np=Path(__file__).parent/"extraction.json"\nsubprocess.run(["leantar","-x","-f","--jobs","3","-j","-"],input=p.read_text(),text=True,check=True)\n'
        (work / 'controller/extract.py').write_text(extract_code)
        status('extract-cache-inside-offline-sandbox', status='running')
        result = v.sandboxed_run([str(python), str(work / 'controller/extract.py')], cwd=work / 'controller', environment=trusted_env,
            writable_directories=[work / 'cache-extraction', work / 'trusted-home', work / 'trusted-tmp'],
            readable_paths=[work / 'downloads', *v.system_readable_paths()], executable_paths=[old, Path('/usr')], tools=tools, timeout=900)
        (work / 'logs/cache-extraction.log').write_text(result.stdout + '\n' + result.stderr)
        sidecars = json.loads((evidence / 'dependency-sidecar-audit.json').read_text())
        cached_hashes = {p.split('/lib/lean/')[-1]:h for section in ['main_oleans', 'sidecars'] for p,h in sidecars[section].items()}
        # Candidate cache never enters canonical compilation; all its proof content
        # must pass independent kernel replay and definition identity checks.
        extra_manifest = {}
        for file in (work / 'cache-extraction').rglob('*'):
            if not file.is_file() or '/lib/lean/' not in str(file): continue
            require(not file.is_symlink(), 'Cache extraction contained a symlink')
            rel = str(file).split('/lib/lean/')[-1]
            if not rel.endswith(('.olean', '.olean.private', '.olean.server')): continue
            module = rel.partition('.olean')[0].replace('/', '.')
            if module not in selected_cache: continue
            require(rel in cached_hashes and digest(file) == cached_hashes[rel], 'Cache object mismatch: ' + rel)
            target = work / 'candidate-deps' / safe_relative(rel); target.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(file, target)
            extra_manifest[rel] = digest(target)
        for module in selected_cache:
            require(module.replace('.', '/') + '.olean' in extra_manifest, 'Missing extracted module: ' + module)
        # Complete each namespace without giving the candidate writable shared caches.
        for rel in library_manifest:
            target = work / 'candidate-deps' / rel; target.parent.mkdir(parents=True, exist_ok=True); target.symlink_to(work / 'trusted-lib' / rel)
        write_json(work / 'additional-library-manifest.json', extra_manifest)
        graph = {m:imports((work / 'source' / (m.replace('.', '/')+'.lean')).read_text()) for m in compiled}
        for module, dependencies in graph.items():
            require(re.fullmatch(r'[A-Za-z0-9_.]+', module) is not None, 'Invalid module')
            for dep in dependencies:
                require(dep in graph or dep in inputs['trusted_module_sources'] or dep in selected_cache or
                        (old / 'lib/lean' / (dep.replace('.', '/')+'.olean')).is_file(), 'Missing dependency: ' + dep)
        write_json(work / 'controller/graph.json', graph)
        (work / 'controller/build.py').write_text(BUILDER)
        for rel in library_manifest:
            if not rel.startswith('OAI/'): continue
            module = rel.split('.olean')[0].split('.ir')[0].split('.ilean')[0].replace('/', '.')
            if module in graph: continue
            target = work / 'candidate-lib' / rel; target.parent.mkdir(parents=True, exist_ok=True); target.symlink_to(work / 'trusted-lib' / rel)
        candidate_env = {**common, 'HOME': str(work / 'candidate-home'), 'TMPDIR': str(work / 'candidate-tmp'),
                         'LEAN_PATH': str(work / 'candidate-lib') + ':' + str(work / 'candidate-deps')}
        writable = [work / n for n in ['candidate-lib', 'candidate-home', 'candidate-tmp', 'candidate-logs']]
        readable = [work / 'source', work / 'trusted-lib', work / 'candidate-deps', work / 'controller', *v.system_readable_paths()]
        status('test-actual-candidate-mount-isolation', status='running')
        v.verify_sandbox_confinement(work / 'source/denied-write', work / 'denied-read', positive_read=work / 'source/WeightedQRH/Statements.lean',
            python=python, touch=touch, cwd=work / 'source', environment=candidate_env, writable_directories=writable,
            protected_write_directories=[work / 'source', work / 'trusted-lib', work / 'candidate-deps', work / 'controller'],
            readable_paths=readable, executable_paths=[old, Path('/usr')], tools=tools)
        status('compile-candidate-in-offline-sandbox', status='running', candidate_modules=len(graph))
        result = v.sandboxed_run([str(python), str(work / 'controller/build.py')], cwd=work / 'source', environment=candidate_env,
            writable_directories=writable, readable_paths=readable, executable_paths=[old, Path('/usr')],
            tools=tools, timeout=7200, check=False, stdout_path=work / 'logs/candidate-build.log')
        if result.returncode:
            status('candidate-build-failed', status='build-failed', returncode=result.returncode)
            raise RuntimeError('Candidate build failed; inspect per-module logs')
        solution_env = {**trusted_env, 'LEAN_PATH': str(work / 'solution-lib') + ':' + str(work / 'candidate-lib') + ':' + str(work / 'candidate-deps')}
        status('compile-and-export-solution', status='running')
        result = v.sandboxed_run([str(old / 'bin/lean'), '-j1', '-o', str(work / 'solution-lib/Solution.olean'), 'Solution.lean'],
            cwd=work / 'solution-src', environment=solution_env,
            writable_directories=[work / 'solution-lib', work / 'trusted-home', work / 'trusted-tmp'],
            readable_paths=[work / 'candidate-lib', work / 'candidate-deps', work / 'trusted-lib', *v.system_readable_paths()],
            executable_paths=[old, Path('/usr')], tools=tools, timeout=600)
        (work / 'logs/solution-compile.log').write_text(result.stdout + '\n' + result.stderr)
        result = v.export_module('Solution', targets, output=work / 'exports/Solution.export', leanexport=exporter,
            cwd=work / 'solution-src', environment=solution_env,
            readable_paths=[work / 'solution-lib', work / 'candidate-lib', work / 'candidate-deps', work / 'trusted-lib', *v.system_readable_paths()],
            executable_paths=[old, exporter, Path('/usr')], tools=tools, timeout=1800)
        (work / 'logs/solution-export.log').write_text(result.stdout + '\n' + result.stderr)
        require(result.returncode == 0, 'Solution export failed')
        v.verify_export(work / 'exports/Solution.export')
        require(digest(work / 'exports/Challenge.export') == challenge_hash, 'Frozen challenge changed')
        require(all(digest(work / 'source' / name) == sha for name,sha in expected.items()), 'Candidate source changed')
        status('comparator-and-three-independent-kernels', status='running')
        result = v.judge_exports(lake=bundled['lake'], config=work / 'comparator.json', challenge_export=work / 'exports/Challenge.export',
            solution_export=work / 'exports/Solution.export', scratch=work / 'judge', bwrap=v._BWRAP, lean_prefix=judge,
            environment=trusted_env, tools=tools, timeout=7200)
        transcript = result.stdout + '\n' + result.stderr
        (work / 'logs/judge.log').write_text(transcript)
        verdict = v.comparator_verdict(result.returncode, transcript)
        if verdict: raise verdict
        require('Your solution is okay!' in transcript and all(name+' kernel accepts the solution' in transcript for name in ['Lean default','nanoda','con-ron']), 'Incomplete kernel acceptance')
        v.verify_tool_snapshot(tools)
        require(digest(work / 'exports/Challenge.export') == challenge_hash, 'Frozen challenge changed')
        require(all(digest(work / 'trusted-lib' / name) == sha for name,sha in library_manifest.items()), 'Approved library changed')
        require(all(digest(work / 'candidate-deps' / name) == sha for name,sha in extra_manifest.items()), 'Extra cache changed')
        artifact_paths = [*sorted(work.glob('*.json')), work / 'challenge-src/Challenge.lean', work / 'solution-src/Solution.lean',
                          work / 'exports/Challenge.export', work / 'exports/Solution.export', *sorted((work / 'logs').glob('*.log')),
                          *sorted((work / 'candidate-logs').glob('*.log')), *sorted((work / 'controls').glob('*.log'))]
        artifacts = artifact_inventory(work, [p for p in artifact_paths if p.name != 'status.json'])
        write_json(work / 'result.json', {'status':'PASS', 'kind':'independent maintainer mechanical replay; not signed registry admission',
            'verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'source_commit':inputs['source_commit'],
            'reviewed_pr_head':inputs['pr_head_commit'], 'trusted_base_commit':inputs['trusted_base_commit'],
            'source_repository':inputs['source_repository'], 'source_content_sha256':inputs['source_content_sha256'],
            'driver_sha256':digest(Path(__file__)), 'pins_sha256':digest(HERE / 'pins.json'),
            'source_bundle':inputs['source_bundle'], 'dependency_fork':inputs['dependency_fork'],
            'submission_manifest_sha256':inputs['submission_manifest_sha256'], 'theta_exact':inputs['theta_exact'], 'targets':config['theorem_names'], 'allowed_axioms':config['permitted_axioms'],
            'kernels':['Lean default','nanoda','con-ron'], 'judge_exit_code':result.returncode,
            'sandbox_preflight':'PASS', 'candidate_mount_preflight':'PASS', 'receipt_outside_candidate':True,
            'challenge_exported_before_candidate_execution':True, 'candidate_modules_rebuilt':len(graph),
            'approved_dependency_modules':len(inputs['trusted_module_sources']), 'extra_official_cache_modules':len(selected_cache),
            'source_compiler':'4.34.1', 'judge_toolchain':'4.35.0-rc2', 'verifier_commit':PALOMAR_COMMIT,
            'artifacts':artifacts, 'limitations':['Reuses a separately approved source-built canonical library; not a cache-free bootstrap.',
              'Extra candidate dependencies fetched from pinned official cache and kernel-replayed; they never supply canonical definitions.',
              'This is a local maintainer replay, not a production submission service or signed publication receipt.']})
        write_json(work / 'controls/control-results.json', {'status': 'PASS', 'main_receipt_sha256': digest(work / 'result.json'),
            'executed_before_candidate': True, 'cases': control_cases})
        status('complete', status='PASS', receipt_sha256=digest(work / 'result.json'))
    except BaseException as error:
        previous = json.loads((work / 'status.json').read_text()) if (work / 'status.json').exists() else {}
        category = 'build-failed' if previous.get('status') == 'build-failed' else 'infrastructure-blocked'
        if getattr(error, 'owner', None) == 'submitter': category = 'checking-failed'
        if isinstance(error, (TimeoutError, subprocess.TimeoutExpired)): category = 'timed-out'
        status('stopped', status=category, error_type=type(error).__name__, error=str(error), code=getattr(error, 'code', None), detail=getattr(error, 'detail', None))
        traceback.print_exc()
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', type=Path, required=True, help='Trusted operator paths; never from a submission')
    parser.add_argument('--work', type=Path, required=True, help='New private directory on a disposable unprivileged Linux worker')
    args = parser.parse_args()
    run(args.profile.resolve(), args.work.resolve())


if __name__ == '__main__':
    main()
