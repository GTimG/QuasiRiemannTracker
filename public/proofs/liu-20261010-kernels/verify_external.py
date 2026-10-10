#!/usr/bin/env python3
"""Check an external QRH proof against separately built canonical definitions.

Apache-2.0. Local mechanical verification, not signed registry admission.
Input paths are supplied by the operator; public packages retain relative
inventories and a documented mapping to an independently reconstructed build.
"""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import traceback

PALOMAR = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
EXPORTER = '076e8e57707e813375e8f9da8bf989799ace9680'
VERIFIER = 'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2'
SOURCE_LEAN = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
BWRAP = 'bb807d18eaee5dad15afd5cf48c8de1c3206ff97e852af693d679d62394eb5a2'
PINS = '18094edb243320a431d10a84e0ed7c7d6b1b00f1a7b14f81b2f8ad1a7747b20a'
GRAPH = '7364b78eb62004edfe9d7c3ebacd0b4f8cbc65f53e07dd6200816a92338cca7e'
RECORDS = '530332d9c117d87456183de122ac4fc685661f0d7aa671253d91d31bd9018b00'
DECLARATIONS = ['QRHPalomar.allDirichlet', 'QRHPalomar.zeta', 'QRHPalomar.allHecke']
AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
KERNELS = ['Lean default', 'nanoda', 'con-ron']


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def commit(path):
    return subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()


def safe(path):
    return bool(path) and not Path(path).is_absolute() and '..' not in Path(path).parts


def audit_inputs(cfg, work, jobs):
    inventory = json.loads(Path(cfg['input_inventory']).read_text())
    source_root = Path(cfg['source_root']).resolve()
    files = inventory['source_files']
    assert files and all(safe(p) for p in files)
    manifest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    assert manifest == cfg['source_manifest_sha256']
    artifacts = inventory['artifact_files']
    assert artifacts and inventory['native_build_success'] is True
    assert inventory['candidate_imports_no_QRH'] is True
    assert commit(Path(cfg['source_checkout'])) == cfg['source_commit']

    base = Path(cfg['canonical_root']).resolve()
    audit_root = Path(cfg['canonical_audit_root']).resolve()
    gp, rp = audit_root/'local-selected-source-graph.json', audit_root/'local-build-records.json'
    assert sha(gp) == GRAPH and sha(rp) == RECORDS
    graph, records = json.loads(gp.read_text()), json.loads(rp.read_text())
    roots = ['Mathlib.NumberTheory.LSeries.DirichletContinuation',
             'OAI.NumberTheory.DirichletL.Hecke.IdealBridge']
    closure = set()

    def visit(name):
        if name not in closure:
            closure.add(name)
            for dependency in graph[name]['imports']:
                visit(dependency)

    for name in roots:
        visit(name)
    assert len(closure) == 4386
    assert not any(n == 'QRH' or n.startswith('QRH.') for n in closure)
    checks = [(source_root/p, h) for p, h in files.items()]
    checks += [(Path(p), h) for p, h in artifacts.items()]
    checks += [(base/graph[n]['source'], graph[n]['sha256']) for n in closure]
    checks += [(base/records[n]['olean'], records[n]['olean_sha256']) for n in closure]

    def check(item):
        path, digest = item
        if sha(path) != digest:
            raise ValueError('Source/artifact integrity mismatch: ' + str(path))

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(check, checks))
    write(work/'source-inputs.json', {'manifest_sha256': manifest, 'files': files})
    write(work/'native-build-inputs.json', {
        'status': 'PASS', 'source_manifest_sha256': manifest,
        'sources_and_oleans_rehashed': True, 'challenge_imports_no_candidate': True,
        'candidate_imports_no_QRH': True, 'candidate_source_count': len(files),
        'candidate_artifact_count': len(artifacts), 'canonical_dependency_count': len(closure),
        'canonical_source_graph_sha256': GRAPH, 'canonical_build_records_sha256': RECORDS,
        'canonical_imports': roots, 'native_inventory_sha256': sha(cfg['input_inventory']),
        'native_build_report_sha256': sha(cfg['native_build_report']),
        'trust_note': 'Canonical source/artifacts match the accepted independent-check baseline. '
                      'Pinned dependency caches and fresh candidate builds are distinguished in the native inventory. '
                      'The exported proof closure is subsequently replayed in three kernels.'})
    return inventory


def main():
    if sys.flags.optimize:
        raise SystemExit('Integrity checks require Python without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', required=True, type=Path)
    parser.add_argument('--work', required=True, type=Path)
    parser.add_argument('--checkers', required=True, type=Path)
    parser.add_argument('--bwrap', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--timeout', type=int, default=19800)
    args = parser.parse_args()
    assert 1 <= args.jobs <= len(os.sched_getaffinity(0))
    cfg = json.loads(args.config.read_text())
    work, checker = args.work.resolve(), args.checkers.resolve()
    work.mkdir(parents=True, exist_ok=False)
    report = {
        'status': 'RUNNING', 'kind': 'local-mechanical-kernel-evidence',
        'started_utc': utc(), 'source_commit': cfg['source_commit'],
        'repository': cfg['repository'], 'source_manifest_sha256': cfg['source_manifest_sha256'],
        'source_compiler': '4.34.1', 'judge_toolchain': '4.35.0-rc2',
        'palomar_commit': PALOMAR, 'exporter_commit': EXPORTER,
        'declarations': DECLARATIONS, 'allowed_axioms': AXIOMS, 'kernels': KERNELS,
        'statement_definitions_compared': False, 'phases': [], 'jobs': args.jobs,
        'source_inputs': 'source-inputs.json', 'native_build_report': 'native-build-inputs.json',
        'judge_log': 'judge.log', 'tool_pins': 'tool-pins.json',
        'preflight_results': 'preflight-results.json', 'comparator_config': 'comparator.json',
        'runner': 'verify_external.py', 'source_provenance': 'source-provenance.json',
        'reproduction_script': cfg['reproduction_script'],
        'host_policy_note': 'Temporary per-binary user-namespace profile; global restriction unchanged.',
        'registration_note': 'No signed receipt or editorial admission is claimed.'}
    if cfg.get('theta_exact'):
        report['theta_exact'] = cfg['theta_exact']
    else:
        report['theta'] = cfg['theta']

    def save():
        write(work/'result.json', report)

    def phase(name):
        report['current_phase'] = name
        report['phases'].append({'name': name, 'started_utc': utc()})
        save()
        print(f'[{utc()}] {name}', flush=True)

    try:
        phase('tool-and-input-integrity')
        palomar = checker/'tools/palomar'
        exporter = checker/'tools/lean4export/.lake/build/bin/lean4export'
        judge = checker/'tools/lean-4.35.0-rc2-linux'
        source = Path(cfg['source_toolchain']).resolve()
        bwrap = args.bwrap.resolve()
        assert commit(palomar) == PALOMAR and commit(checker/'tools/lean4export') == EXPORTER
        assert sha(palomar/'scripts/verify_submission.py') == VERIFIER
        assert sha(checker/'tool-pins.json') == PINS
        pins = json.loads((checker/'tool-pins.json').read_text())
        assert sha(source/'bin/lean') == SOURCE_LEAN and sha(bwrap) == BWRAP
        assert sha(exporter) == pins['exporter']['sha256']
        sys.path.insert(0, str(palomar))
        from scripts import verify_submission as v
        v.configure_bwrap(bwrap)
        v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, 'memory_high_percent': 35,
                                 'memory_max_percent': 43, 'tasks_max': 4096}
        v.install_execution_deadline(budget_seconds=args.timeout)
        bundled = v.toolchain_tools(judge)
        for name, path in bundled.items():
            assert sha(path) == pins[name]['sha256']
        tools = v.tool_snapshot([*bundled.values(), source/'bin/lean', exporter, bwrap])
        write(work/'tool-pins.json', {'palomar_commit': PALOMAR, 'exporter_commit': EXPORTER,
            'judge_tools': v.tool_digests(bundled, bwrap), 'source_lean_sha256': SOURCE_LEAN,
            'source_exporter_sha256': sha(exporter), 'driver_sha256': sha(__file__),
            'verifier_script_sha256': VERIFIER})
        audit_inputs(cfg, work, args.jobs)
        (work/'verify_external.py').write_bytes(Path(__file__).read_bytes())
        (work/'source-provenance.json').write_bytes(Path(cfg['source_provenance']).read_bytes())
        wrappers = Path(cfg['wrapper_sources']).resolve()
        challenge_text = (wrappers/'Challenge.lean').read_text()
        solution_text = (wrappers/'Solution.lean').read_text()
        assert sha(wrappers/'Challenge.lean') == cfg['challenge_sha256']
        assert not re.search(r'\b(sorry|admit)\b', solution_text)
        raw = {'challenge_module': 'Challenge', 'solution_module': 'Solution',
               'theorem_names': DECLARATIONS, 'definition_names': [], 'permitted_axioms': AXIOMS}
        write(work/'requested-comparator.json', raw)
        kernels = v.protected_kernels(bundled)
        config = v.protected_comparator_config(work/'requested-comparator.json', work/'comparator.json', kernels=kernels)
        protected = v.validate_protected_comparator_config(config, kernels=kernels)
        src, lib, exports = (work/n for n in ['src', 'lib', 'exports'])
        for path in [src, lib, exports, work/'home', work/'tmp']:
            path.mkdir(parents=True)
        cmod = protected['challenge_module']
        csrc = src/(cmod.replace('.', '/') + '.lean')
        csrc.parent.mkdir(parents=True)
        csrc.write_text(challenge_text)
        (src/'Solution.lean').write_text(solution_text)
        report['challenge_source'] = str(csrc.relative_to(work))
        report['solution_source'] = 'src/Solution.lean'
        environment = {'PATH': str(source/'bin')+':/usr/bin:/bin', 'LANG': 'C.UTF-8',
            'HOME': str(work/'home'), 'TMPDIR': str(work/'tmp'), 'LEAN_ABORT_ON_PANIC': '1'}
        phase('positive-and-negative-checker-controls')
        original_judge = v.judge_exports
        controls = []

        def observe(**kwargs):
            proc = original_judge(**kwargs)
            label = kwargs['solution_export'].stem
            log = 'preflight-' + label + '.log'
            (work/log).write_text(proc.stdout + '\n' + proc.stderr)
            controls.append({'name': label, 'exit_code': proc.returncode, 'log': log})
            write(work/'preflight-results.json', {'cases': controls})
            return proc

        v.judge_exports = observe
        try:
            v.comparator_preflight(work, lean=bundled['lean'], leanexport=bundled['leanexport'],
                lake=bundled['lake'], lean_prefix=judge, bwrap=bwrap, kernels=kernels,
                primitives=v.primitive_targets(judge),
                environment={**environment, 'PATH': str(judge/'bin')+':/usr/bin:/bin'},
                executable_paths=[judge, bwrap, Path('/usr')], tools=tools, timeout=180)
        finally:
            v.judge_exports = original_judge
        report['palomar_preflight'] = 'passed'
        canonical_paths = [Path(p) for p in Path(cfg['canonical_lean_path']).read_text().strip().split(os.pathsep)]
        dependency_view = work/'canonical-dependencies'
        dependency_view.mkdir()
        for path in canonical_paths[0].iterdir():
            if path.name != 'QRH' and not path.name.startswith('QRH.'):
                (dependency_view/path.name).symlink_to(path, target_is_directory=path.is_dir())
        candidate_paths = [Path(p) for p in Path(cfg['candidate_lean_path']).read_text().strip().split(os.pathsep)]
        cenv = {**environment, 'LEAN_PATH': os.pathsep.join(map(str, [lib, dependency_view, *canonical_paths[1:]]))}
        senv = {**environment, 'LEAN_PATH': os.pathsep.join(map(str, [lib, *candidate_paths]))}
        readable = [work, Path(cfg['workspace']).resolve(), *v.system_readable_paths()]
        executable = [source, exporter, bwrap, Path('/usr')]
        targets = v.comparator_export_targets(protected, v.primitive_targets(judge))
        write(work/'export-targets.json', targets)
        for label, module, path, env in [('Challenge', cmod, csrc, cenv),
                                       ('Solution', 'Solution', src/'Solution.lean', senv)]:
            phase(label.lower()+'-compile')
            target = lib/(module.replace('.', '/')+'.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            proc = v.sandboxed_run([str(source/'bin/lean'), f'-j{args.jobs}', '-R', str(src),
                '-o', str(target), str(path)], cwd=src, environment=env,
                writable_directories=[lib, work/'home', work/'tmp'], readable_paths=readable,
                executable_paths=executable, tools=tools, timeout=600, check=False)
            (work/(label+'-compile.log')).write_text(proc.stdout+'\n'+proc.stderr)
            if proc.returncode:
                raise RuntimeError(label+' compilation failed')
            phase(label.lower()+'-export')
            destination = exports/(label.lower()+'.export')
            proc = v.export_module(module, targets, output=destination, leanexport=exporter,
                cwd=src, environment=env, readable_paths=readable, executable_paths=executable,
                tools=tools, timeout=args.timeout)
            (work/(label+'-export.log')).write_text(proc.stderr)
            if proc.returncode:
                raise RuntimeError(label+' export failed')
            v.verify_export(destination)
            tools[destination.resolve()] = sha(destination)
            report.setdefault('exports', {})[label.lower()] = {'sha256': sha(destination), 'bytes': destination.stat().st_size}
            save()
        phase('comparator-and-three-kernels')
        proc = v.judge_exports(lake=bundled['lake'], config=config,
            challenge_export=exports/'challenge.export', solution_export=exports/'solution.export',
            scratch=work/'judge', bwrap=bwrap, lean_prefix=judge,
            environment=environment, tools=tools, timeout=args.timeout)
        log = (proc.stdout+'\n'+proc.stderr).strip()+'\n'
        (work/'judge.log').write_text(log)
        report['judge_exit_code'] = report['comparator_exit_code'] = proc.returncode
        verdict = v.comparator_verdict(proc.returncode, log)
        if verdict is not None:
            raise verdict
        markers = [name+' kernel accepts the solution' for name in KERNELS]+['Your solution is okay!']
        assert all(marker in log for marker in markers)
        v.verify_tool_snapshot(tools)
        phase('final-source-and-artifact-recheck')
        audit_inputs(cfg, work, args.jobs)
        report.update(status='PASS', statement_definitions_compared=True,
            acceptance_markers=markers, finished_utc=utc(), verified_at_utc=utc())
        report['export_sizes'] = {'exports/'+label+'.export': values['bytes'] for label, values in report['exports'].items()}
        report['artifacts'] = {p.relative_to(work).as_posix(): sha(p) for p in sorted(work.rglob('*'))
            if p.is_file() and not p.is_symlink() and p != work/'result.json'
            and not any(part in {'canonical-dependencies', 'home', 'tmp', 'judge', 'lib', 'comparator-preflight'}
                        for part in p.relative_to(work).parts)}
        save()
        print(json.dumps({k: report[k] for k in ['status', 'repository', 'declarations', 'verified_at_utc']}, indent=2), flush=True)
        return 0
    except Exception as exc:
        report.update(status='FAILED', error_type=type(exc).__name__, error=str(exc),
                      detail=getattr(exc, 'detail', None), finished_utc=utc())
        (work/'exception.log').write_text(traceback.format_exc())
        save()
        print(json.dumps({'status': 'FAILED', 'error': str(exc)}, indent=2), flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
