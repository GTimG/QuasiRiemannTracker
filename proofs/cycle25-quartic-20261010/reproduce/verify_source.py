#!/usr/bin/env python3
"""Check the frozen finished proof source; optionally rebuild its entrypoint."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
INVENTORY = json.loads((HERE / 'frozen-source-inventory.json').read_text())
PINS = json.loads((HERE.parent / 'dependencies/dependency-pins.json').read_text())


def check(project):
    expected = {item['path']: item for item in INVENTORY['sources']}
    actual = {str(p.relative_to(project)) for name in ['Cycle25', 'OAI', 'ZetaZeroFree']
              for p in (project / name).rglob('*.lean')}
    if actual != set(expected):
        raise ValueError('Finished-source set differs: missing=' + repr(sorted(set(expected) - actual))
                         + ', extra=' + repr(sorted(actual - set(expected))))
    for path, item in expected.items():
        source = project / path
        if source.is_symlink() or hashlib.sha256(source.read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('Frozen source mismatch: ' + path)
    print('Frozen source checks passed (' + str(len(expected)) + ' modules).')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--build', action='store_true', help='Rebuild all local source dependencies of the endpoint')
    args = parser.parse_args()
    project = args.project.resolve()
    check(project)
    if args.build:
        subprocess.run(['python3', str(HERE / 'bootstrap_dependencies.py'), '--project', str(project), '--check'], check=True)
        version = subprocess.check_output(['elan', 'run', PINS['toolchain']['toolchain'], 'lean', '--version'], text=True)
        if PINS['toolchain']['commit'] not in version:
            raise ValueError('Unexpected compiler commit')
        # This invokes only finished endpoint roots, never an unrelated dependency default target.
        for module in INVENTORY['entrypoints']:
            subprocess.run(['elan', 'run', PINS['toolchain']['toolchain'], 'lake', 'build', module], cwd=project, check=True)
        check(project)
        print('Finished endpoint and its full local source dependencies built successfully.')


if __name__ == '__main__':
    main()
