#!/usr/bin/env python3
"""Verify local source build records and exact targets with cached dependencies.

This reports the cache trust boundary explicitly. It does not claim the official
mathlib dependencies have been compiled locally from source.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess

R = Path(__file__).resolve().parents[1]
CONFIG = 'lean-4.34.1-local-cache-build-v1'


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


for line in (R / 'audit/frozen-targets.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    assert sha(R / name) == expected, name
gate = R / 'audit/FinalTargetsRequired.lean'
assert sha(gate) == '9b6cac802217299b1ebeb62f0b8f19ed11b796447085b04509903db98bbb10d4', gate
inputs = R / 'inputs/qrh-formalization-handoff-20261009'
input_count = 0
for line in (inputs / 'SHA256SUMS.txt').read_text().splitlines():
    expected, name = line.split(maxsplit=1)
    assert sha(inputs / name.lstrip('*')) == expected, name
    input_count += 1
assert sha(inputs / 'accepted-answer.tex') == 'c8b9994d6a55521b53fe4664ba190e46dc0a02f7d85221e25d39efa4dcd34de9'

status = json.loads((R / 'audit/local-build-status.json').read_text())
graph = json.loads((R / 'audit/local-selected-source-graph.json').read_text())
records = json.loads((R / 'audit/local-build-records.json').read_text())
assert status['success'] and not status['failed'] and not status['blocked']
assert status['configuration'] == CONFIG
assert {'QRH', 'QRH.Analytic'} <= set(status['roots'])
assert status['checked'] == status['closure'] == len(graph) == len(records)
local_modules = {'.'.join(p.relative_to(R / 'formalization').with_suffix('').parts)
                 for p in (R / 'formalization/QRH').rglob('*.lean')} | {'QRH'}
assert local_modules <= graph.keys(), sorted(local_modules - graph.keys())
keys = {}


def check(module):
    if module in keys:
        return keys[module]
    item = graph[module]
    assert sha(R / item['source']) == item['sha256'], module
    key = hashlib.sha256((item['sha256'] + ''.join(check(d) for d in item['imports'])
                          + CONFIG).encode()).hexdigest()
    record = records[module]
    assert record['key'] == key, module
    target = R / record['olean']
    assert sha(target) == record['olean_sha256'], module
    if record['mode'] == 'local-source':
        assert target.with_suffix('.source-key').read_text() == key, module
        with (R / 'logs/local-source' / (module + '.log')).open() as f:
            header = json.loads(f.readline())
        assert header['key'] == key and header['source_sha256'] == item['sha256'], module
        assert any(f'-j{n}' in header['command'] for n in range(1, 17)), module
    else:
        assert record['mode'] == 'official-mathlib-cache', module
        assert record['olean'] == item['cache'], module
        assert not module.startswith(('OAI.', 'QRH.', 'RellichKondrachov.',
                                      'MathlibExtensions.', 'PrimeNumberTheoremAnd.')), module
    keys[module] = key
    return key


for module in graph:
    check(module)

# Verify repository pins and mathematical definition provenance independently
# of the local proof changes, which have their own source hashes above.
repositories = json.loads((R / 'audit/dependency-licenses.json').read_text())
checked_pins = []
for repository in repositories:
    path = R / repository['path']
    if repository['path'] == 'upstream/argonaut' and not path.exists():
        continue
    revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                       text=True).strip()
    assert revision == repository['revision'], repository['path']
    for notice in repository['notices']:
        assert sha(R / notice['path']) == notice['sha256'], notice['path']
    checked_pins.append({'path': repository['path'], 'revision': revision})
for item in json.loads((R / 'audit/actual-definition-provenance.json').read_text()):
    repository = R / item['repository']
    current = repository / item['path']
    pinned = subprocess.check_output(['git', '-C', str(repository), 'show',
                                      'HEAD:' + item['path']])
    assert current.read_bytes() == pinned and sha(current) == item['sha256'], item['path']

lean = R / 'toolchains/lean-4.34.1-linux/bin/lean'
version = subprocess.check_output([str(lean), '--version'], text=True).strip()
assert 'version 4.34.1,' in version
assert 'commit 5045d0056413266e57c625dcd7c365b10e377c52' in version
env = os.environ.copy()
env['LEAN_PATH'] = (R / 'audit/local-lean-path.txt').read_text().strip()
env['GLIBC_TUNABLES'] = 'glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1'
log = R / 'logs/local-final-targets-required.log'
gate_threads = min(16, len(os.sched_getaffinity(0))) if hasattr(os, 'sched_getaffinity') else min(16, os.cpu_count() or 1)
with log.open('w') as f:
    result = subprocess.run([str(lean), f'-j{gate_threads}', str(gate)],
                            env=env, stdout=f, stderr=subprocess.STDOUT)
assert result.returncode == 0, log
output = log.read_text()
groups = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
groups += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
names = {'QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re',
         'QRH.riemannZeta_ne_zero_of_theta_lt_re', 'QRH.Hecke.LFunction_ne_zero_of_theta_lt_re'}
assert {name for name, _ in groups} == names, output
axioms = {name: sorted(a.strip() for a in values.split(',') if a.strip())
          for name, values in groups}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(values) <= allowed for values in axioms.values()), axioms
report = {'status': 'PASS', 'exact_three_targets_proved': True,
          'threshold': '874957019421/1000000000000', 'declarations': axioms,
          'compiler': version, 'build': status, 'module_artifacts_rechecked': len(keys),
          'all_local_qrh_modules_checked': len(local_modules),
          'source_graph_sha256': sha(R / 'audit/local-selected-source-graph.json'),
          'specification_hash_manifest_sha256': sha(R / 'audit/frozen-targets.sha256'),
          'gate': 'audit/FinalTargetsRequired.lean', 'gate_exit_code': result.returncode,
          'gate_thread_budget': gate_threads,
          'gate_sha256': sha(gate),
          'immutable_inputs_checked': input_count,
          'pinned_repositories': checked_pins,
          'trust_note': status['trust_note']}
(R / 'audit/local-verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
