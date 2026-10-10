#!/usr/bin/env python3
"""Audit the actual Lean namespace-first resolution used by a frozen judge run.

This does not execute candidate code or modify the running driver. It verifies
compiled-module resolution against the exact recorded native/canonical inputs.
Run before and after the exported proof check; publish both audits and this file.
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


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def read_paths(path):
    values = Path(path).read_text().strip().split(os.pathsep)
    demand(values and all(values), 'Empty LEAN_PATH component')
    paths = [Path(value).resolve() for value in values]
    demand(all(path.is_dir() for path in paths), 'Missing LEAN_PATH directory')
    return paths


def resolve_module(module, search):
    # Lean/Util/Path.lean, SearchPath.findWithExt in the pinned source compiler.
    parts = module.split('.')
    demand(all(parts), 'Invalid module name')
    for index, root in enumerate(search):
        if (root/parts[0]).is_dir() or (root/(parts[0]+'.olean')).exists():
            file = root.joinpath(*parts).with_suffix('.olean')
            demand(file.is_file(), 'Claimed namespace lacks module: '+module)
            return file.resolve(), index
    raise ValueError('Module not found: '+module)


def checker_audit(checker):
    expected = 'd4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'
    repo = checker/'tools/palomar'
    revision = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    demand(revision == expected, 'Unexpected Palomar revision')
    names = subprocess.check_output(['git', '-C', str(repo), 'ls-files', '-z', 'scripts'], text=True).split('\0')
    hashes = {}
    for name in names:
        if not name:
            continue
        original = subprocess.check_output(['git', '-C', str(repo), 'show', expected+':'+name])
        digest = hashlib.sha256(original).hexdigest()
        demand(sha(repo/name) == digest, 'Checker helper differs from pinned blob: '+name)
        hashes[name] = digest
    return {'commit': revision, 'tracked_script_count': len(hashes), 'files': hashes,
            'scope': 'Tracked helper/source bytes match pinned git blobs; this is not a host-process attestation.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--checkers', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--module-manifest', type=Path,
                        help='Detailed native source/build manifest when inventory has no modules list')
    args = parser.parse_args()
    demand(1 <= args.jobs <= 4, 'This audit uses at most four workers')
    cfg = json.loads(args.config.read_text())
    work = args.work.resolve()
    inventory = json.loads(Path(cfg['input_inventory']).read_text())
    base = Path(cfg['canonical_root']).resolve()
    audit_root = Path(cfg['canonical_audit_root']).resolve()
    graph_path, records_path = audit_root/'local-selected-source-graph.json', audit_root/'local-build-records.json'
    demand(sha(graph_path) == '7364b78eb62004edfe9d7c3ebacd0b4f8cbc65f53e07dd6200816a92338cca7e', 'Canonical graph pin differs')
    demand(sha(records_path) == '530332d9c117d87456183de122ac4fc685661f0d7aa671253d91d31bd9018b00', 'Canonical artifact pin differs')
    graph, records = json.loads(graph_path.read_text()), json.loads(records_path.read_text())
    canonical_modules = set()

    def visit(module):
        if module not in canonical_modules:
            canonical_modules.add(module)
            for imported in graph[module]['imports']:
                visit(imported)

    for root in ['Mathlib.NumberTheory.LSeries.DirichletContinuation', 'OAI.NumberTheory.DirichletL.Hecke.IdealBridge']:
        visit(root)
    demand(len(canonical_modules) == 4386, 'Canonical closure size differs')
    demand(not any(module == 'QRH' or module.startswith('QRH.') for module in canonical_modules), 'Candidate QRH in challenge closure')
    canonical_path = read_paths(cfg['canonical_lean_path'])
    candidate_path = read_paths(cfg['candidate_lean_path'])
    core = Path(cfg['source_toolchain']).resolve()/'lib/lean'
    canonical_search = [work/'lib', work/'canonical-dependencies', *canonical_path[1:], core]
    candidate_search = [work/'lib', *candidate_path, core]
    demand((work/'canonical-dependencies').is_dir(), 'Run has not created its actual canonical dependency view')
    path_source = Path(cfg['source_toolchain'])/'src/lean/Lean/Util/Path.lean'
    source_text = path_source.read_text()
    demand('(p / pkg).isDir <||> ((p / pkg).addExtension ext).pathExists' in source_text and
           'return root?.map (modToFilePath · mod ext)' in source_text,
           'Pinned Lean resolution implementation needs re-review')
    artifacts = {str(Path(path).resolve()): digest for path, digest in inventory['artifact_files'].items()}
    demand(len(artifacts) == len(inventory['artifact_files']), 'Duplicate real paths in native artifact inventory')
    detailed = json.loads(args.module_manifest.read_text()) if args.module_manifest else None
    candidate_modules = inventory.get('modules') or list(detailed['modules'])
    demand(len(candidate_modules) == len(set(candidate_modules)), 'Duplicate native module inventory')
    if detailed:
        demand(detailed['module_count'] == len(candidate_modules), 'Detailed module count differs')
    native_oleans = {path: digest for path, digest in artifacts.items() if path.endswith('.olean')}
    auxiliary = {path: digest for path, digest in artifacts.items() if not path.endswith('.olean')}

    wrappers = Path(cfg['wrapper_sources'])
    wrapper_bindings = {}
    for name in ['Challenge.lean', 'Solution.lean']:
        path = wrappers/name
        text = path.read_text()
        imports = []
        for line in text.splitlines():
            if line.startswith('import '):
                imports.extend(line[7:].split())
        demand(imports and all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name) for name in imports),
               'Wrapper import header requires explicit review')
        if name == 'Challenge.lean':
            demand(sha(path) == cfg['challenge_sha256'], 'Canonical wrapper pin differs')
            demand(imports == ['Mathlib.NumberTheory.LSeries.DirichletContinuation',
                               'OAI.NumberTheory.DirichletL.Hecke.IdealBridge'], 'Canonical import roots differ')
        else:
            demand(set(imports) <= set(candidate_modules), 'Native inventory omits a solution import root')
        wrapper_bindings[name] = {'path': str(path.resolve()), 'sha256': sha(path), 'import_roots': imports}

    def audit_one(item):
        family, module = item
        search = canonical_search if family == 'canonical' else candidate_search
        actual, index = resolve_module(module, search)
        if family == 'canonical':
            expected = records[module]['olean_sha256']
            canonical_file = (base/records[module]['olean']).resolve()
            demand(actual.is_relative_to(base), 'Canonical module resolved outside independent tree: '+module)
            demand(sha(canonical_file) == expected, 'Pinned canonical artifact changed: '+module)
        else:
            demand(str(actual) in native_oleans, 'Resolved candidate module absent from native inventory: '+module)
            expected = native_oleans[str(actual)]
            if detailed:
                module_artifacts = {str(Path(path).resolve()): digest
                                    for path, digest in detailed['modules'][module]['artifacts'].items()}
                demand(module_artifacts.get(str(actual)) == expected, 'Module-specific artifact mapping differs: '+module)
        actual_hash = sha(actual)
        demand(actual_hash == expected, 'Resolved module hash differs: '+module)
        sidecars = {}
        for suffix in ['.private', '.server']:
            sidecar = Path(str(actual)+suffix)
            if sidecar.is_file():
                sidecar = sidecar.resolve()
                value = sha(sidecar)
                recorded = artifacts.get(str(sidecar))
                if recorded:
                    demand(value == recorded, 'Sidecar differs from native artifact inventory: '+str(sidecar))
                sidecars[suffix] = {'path': str(sidecar), 'sha256': value,
                                    'native_inventory_hash_matches': recorded is not None,
                                    'immutable_canonical_main_olean_pin_covers_this_file': False}
        return family, module, {'resolved_path': str(actual), 'sha256': actual_hash, 'search_root_index': index,
                                'sidecars': sidecars}

    items = [('canonical', module) for module in sorted(canonical_modules)]
    items += [('candidate', module) for module in sorted(candidate_modules)]
    resolved = {'canonical': {}, 'candidate': {}}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for family, module, value in pool.map(audit_one, items):
            resolved[family][module] = value
    used_candidate_paths = {item['resolved_path'] for item in resolved['candidate'].values()}
    demand(used_candidate_paths == set(native_oleans), 'Native main-olean inventory contains unresolved or missing modules')
    def check_aux(item):
        path, expected = item
        demand(sha(path) == expected, 'Supplementary native artifact differs: '+path)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(check_aux, auxiliary.items()))
    bindings = {
        'config': args.config, 'canonical_lean_path': Path(cfg['canonical_lean_path']),
        'candidate_lean_path': Path(cfg['candidate_lean_path']), 'input_inventory': Path(cfg['input_inventory']),
        'run_driver': work/'verify_external.py', 'this_audit': Path(__file__),
        'lean_resolution_source': path_source, 'source_lean_binary': Path(cfg['source_toolchain'])/'bin/lean',
        'canonical_graph': graph_path, 'canonical_build_records': records_path,
    }
    if args.module_manifest:
        bindings['native_module_manifest'] = args.module_manifest
    result = {'status': 'PASS', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'scope': 'Actual namespace-first module resolution and byte-hash equality; independent supplement to the frozen judge run.',
              'canonical_count': len(canonical_modules), 'candidate_count': len(candidate_modules),
              'supplementary_native_artifact_count': len(auxiliary),
              'supplementary_native_artifacts_all_rehashed': True,
              'wrapper_bindings': wrapper_bindings,
              'sidecar_scope': 'All present private/server sidecars are inventoried; those in the native artifact manifest are rehashed against it. The old canonical metadata pins main .olean files only. Any separate official-cache provenance audit must be retained, and is not inferred from this main-olean check.',
              'bindings': {name: {'path': str(path.resolve()), 'sha256': sha(path)} for name, path in bindings.items()},
              'canonical_lean_path_contents': Path(cfg['canonical_lean_path']).read_text(),
              'candidate_lean_path_contents': Path(cfg['candidate_lean_path']).read_text(),
              'actual_search_paths': {'canonical': list(map(str, canonical_search)), 'candidate': list(map(str, candidate_search))},
              'checker_sources': checker_audit(args.checkers.resolve()),
              'resolved_modules': resolved}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'canonical_count': result['canonical_count'],
                      'candidate_count': result['candidate_count'], 'checker_script_count': result['checker_sources']['tracked_script_count'],
                      'report_sha256': sha(args.output)}))


if __name__ == '__main__':
    main()
