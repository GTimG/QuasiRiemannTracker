#!/usr/bin/env python3
"""Prepare pinned dependencies; never update the lockfile or reuse local symlinks."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PINS = json.loads((ROOT / 'dependency-pins.json').read_text())

def run(args, cwd=ROOT, capture=False):
    return subprocess.run(args, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE if capture else None,
                          stderr=subprocess.PIPE if capture else None)

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def check_bundle():
    closure = json.loads((ROOT.parent / 'evidence/import-closure.json').read_text())
    for item in closure['modules'].values():
        path = ROOT / item['path']
        if path.is_symlink() or digest(path) != item['sha256']:
            raise ValueError('Source hash mismatch: ' + item['path'])
    report = json.loads((ROOT.parent / 'evidence/analytic-verification-report.json').read_text())
    for item in report['sources']:
        if digest(ROOT / item['path']) != item['sha256']:
            raise ValueError('Verified source changed: ' + item['path'])
    for patch in PINS['patches']:
        if digest(ROOT / patch['path']) != patch['sha256']:
            raise ValueError('Compatibility patch changed: ' + patch['path'])
    print(f"Bundle source and patch hashes passed ({len(closure['modules'])} Lean modules).")

def prepare():
    prefix = ['elan', 'run', PINS['toolchain']['toolchain']]
    version = run(prefix + ['lean', '--version'], capture=True).stdout
    if PINS['toolchain']['commit'] not in version:
        raise ValueError('Lean version/commit does not match the verified source compiler')
    lake = ROOT / '.lake'
    packages = lake / 'packages'
    if lake.is_symlink() or packages.is_symlink():
        raise ValueError('Refusing an external .lake or packages symlink')
    packages.mkdir(parents=True, exist_ok=True)
    for package in PINS['packages']:
        name = package['name'].removeprefix('«').removesuffix('»')
        if '/' in name or name in {'.', '..'}:
            raise ValueError('Unsafe package name')
        path = packages / name
        if path.is_symlink():
            raise ValueError('Refusing a dependency symlink: ' + name)
        if not path.exists():
            path.mkdir()
            run(['git', 'init', '--quiet'], path)
            run(['git', 'remote', 'add', 'origin', package['url']], path)
        if not (path / '.git').exists():
            raise ValueError('Existing dependency is not a Git checkout: ' + name)
        remote = run(['git', 'remote', 'get-url', 'origin'], path, True).stdout.strip()
        if remote.removesuffix('.git') != package['url'].removesuffix('.git'):
            raise ValueError('Existing dependency origin differs: ' + name)
        head = subprocess.run(['git', 'rev-parse', '--verify', 'HEAD'], cwd=path,
                              text=True, capture_output=True)
        if head.returncode:
            # An interrupted fetch can safely resume in the empty checkout.
            if run(['git', 'status', '--porcelain'], path, True).stdout:
                raise ValueError('Uncommitted files in incomplete dependency: ' + name)
            run(['git', 'fetch', '--depth=1', 'origin', package['rev']], path)
            run(['git', 'checkout', '--detach', package['rev']], path)
        elif head.stdout.strip() != package['rev']:
            raise ValueError('Existing dependency commit differs; preserve it and use a fresh directory: ' + name)
    for patch in PINS['patches']:
        path = packages / patch['package']
        file = str(ROOT / patch['path'])
        reverse = subprocess.run(['git', 'apply', '--reverse', '--check', file], cwd=path,
                                 text=True, capture_output=True)
        if reverse.returncode:
            run(['git', 'apply', '--check', file], path)
            run(['git', 'apply', file], path)
        run(['git', 'apply', '--reverse', '--check', file], path)
    print('Pinned dependencies and compatibility patches are ready.')
    print('Optional Mathlib cache: elan run leanprover/lean4:v4.34.1 lake exe cache get')
    print('Full proof check: python3 verify_analytic.py')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check-bundle', action='store_true', help='Offline source/patch integrity check')
    mode.add_argument('--prepare', action='store_true', help='Fetch missing pinned Git dependencies and apply included patches')
    args = parser.parse_args()
    check_bundle()
    if args.prepare:
        prepare()

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
