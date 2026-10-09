#!/usr/bin/env python3
"""Inventory the OpenAI import closure; no fetched code is executed."""
from pathlib import Path
import re, json, hashlib
root = Path(__file__).resolve().parents[1]
source = root / 'upstream/openai-math/lean'
todo = ['OAI.NumberTheory.DirichletL.Nonvanishing']
seen, external = {}, set()
while todo:
    module = todo.pop()
    if module in seen:
        continue
    path = source.joinpath(*module.split('.')).with_suffix('.lean')
    if not path.exists():
        external.add(module)
        continue
    deps = re.findall(r'^(?:public\s+)?import\s+([\w.]+)', path.read_text(), re.M)
    seen[module] = deps
    todo += deps
(root / 'audit/openai-import-closure.json').write_text(json.dumps(
    {'modules': seen, 'external': sorted(external)}, indent=2) + '\n')
(root / 'audit/openai-source.sha256').write_text(''.join(
    hashlib.sha256(source.joinpath(*m.split('.')).with_suffix('.lean').read_bytes()).hexdigest()
    + '  ' + m.replace('.', '/') + '.lean\n' for m in sorted(seen)))
print(f'{len(seen)} OpenAI modules; {len(external)} external imports')
