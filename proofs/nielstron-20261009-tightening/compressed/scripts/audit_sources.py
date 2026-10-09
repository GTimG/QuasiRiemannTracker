#!/usr/bin/env python3
"""Recheck pinned sources and immutable inputs; this is not a proof checker."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(manifest, directory):
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split(maxsplit=1)
        name = name.lstrip('*')
        assert sha(directory / name) == expected, name
        count += 1
    return count


inputs = ROOT / 'inputs/qrh-formalization-handoff-20261009'
input_count = check_manifest(inputs / 'SHA256SUMS.txt', inputs)
assert sha(inputs / 'accepted-answer.tex') == (
    'c8b9994d6a55521b53fe4664ba190e46dc0a02f7d85221e25d39efa4dcd34de9')
target_count = check_manifest(ROOT / 'audit/frozen-targets.sha256', ROOT)
repositories = json.loads((ROOT / 'audit/dependency-licenses.json').read_text())
unselected_absent = []
for repo in repositories:
    if repo['path'] == 'upstream/argonaut' and not (ROOT / repo['path']).exists():
        # The inspected alternative is not required by bootstrap or the proof slice.
        unselected_absent.append(repo['path'])
        continue
    revision = subprocess.check_output(
        ['git', '-C', str(ROOT / repo['path']), 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == repo['revision'], repo['path']
    for notice in repo['notices']:
        assert sha(ROOT / notice['path']) == notice['sha256'], notice['path']

graph = json.loads((ROOT / 'audit/selected-source-graph.json').read_text())
counts = Counter()
header_flags = []
for module, item in graph.items():
    source = ROOT / item['source']
    assert sha(source) == item['sha256'], module
    owners = [r for r in repositories if source.is_relative_to(ROOT / r['path'])]
    if owners:
        owner = max(owners, key=lambda r: len(r['path']))
        assert any(n['license'] == 'Apache-2.0' for n in owner['notices']), module
        counts[owner['path']] += 1
    else:
        assert source.is_relative_to(ROOT / 'formalization/QRH') or source == ROOT / 'formalization/QRH.lean'
        counts['local QRH (Apache-2.0)'] += 1
    # A header scan supplements the recorded license review; it cannot replace it.
    header = '\n'.join(source.read_text().splitlines()[:40]).lower()
    if any(marker in header for marker in ('mit license', 'gnu general public license', 'bsd license')) or (
            'all rights reserved' in header and 'apache' not in header):
        header_flags.append(item['source'])
assert not header_flags, (len(header_flags), header_flags[:10])

definitions = json.loads((ROOT / 'audit/actual-definition-provenance.json').read_text())
for item in definitions:
    repository = ROOT / item['repository']
    current = (repository / item['path']).read_bytes()
    pinned = subprocess.check_output(['git', '-C', str(repository), 'show', 'HEAD:' + item['path']])
    assert current == pinned and hashlib.sha256(current).hexdigest() == item['sha256'], item['path']

result = {'immutable_inputs_checked': input_count, 'frozen_targets_checked': target_count,
          'pinned_repositories_checked': len(repositories) - len(unselected_absent),
          'unselected_candidate_absent': unselected_absent, 'source_modules_checked': len(graph),
          'source_counts': dict(sorted(counts.items())), 'header_license_flags': header_flags,
          'actual_definition_files_checked': len(definitions), 'task_completion_claim': False}
(ROOT / 'audit/source-reverification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
