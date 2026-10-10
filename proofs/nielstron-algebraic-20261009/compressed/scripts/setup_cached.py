#!/usr/bin/env python3
"""Bootstrap pinned dependencies, then fetch the matching official mathlib cache."""
from pathlib import Path
import json, os, subprocess, sys

root = Path(__file__).resolve().parents[1]
subprocess.run([sys.executable, str(root / 'scripts/bootstrap.py')], check=True)
mathlib = root / 'formalization/.lake/packages/mathlib'
packages = mathlib / '.lake/packages'
packages.mkdir(parents=True, exist_ok=True)
manifest = json.loads((mathlib / 'lake-manifest.json').read_text())
for item in manifest['packages']:
    link = packages / item['name']
    target = mathlib.parent / item['name']
    assert target.is_dir(), target
    if link.exists() or link.is_symlink():
        assert link.resolve() == target.resolve(), link
    else:
        # Relative links keep the complete workspace relocatable.
        link.symlink_to(Path('../../..') / item['name'], target_is_directory=True)
env = os.environ.copy()
toolchain = root / 'toolchains/lean-4.34.1-linux/bin'
env['PATH'] = str(toolchain) + os.pathsep + env.get('PATH', '')
subprocess.run([str(toolchain / 'lake'), 'exe', 'cache', 'get'], cwd=mathlib,
               env=env, check=True)
print('Pinned source dependencies and official mathlib cache ready.')
