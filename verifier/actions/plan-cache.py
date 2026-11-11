"""Plan the shared build: compile only shards whose modules changed.

Runs after setup.py and before any submitted code executes. It authenticates the
published index, records the full set of module keys for publish-cache.py, and
narrows the prepared contract to the changed shards plus the modules they
import, restoring those imports from their signed shards.
"""
from pathlib import Path
import json, os, sys, tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache_release import KEY, fetch_index, fetch_shards
from library_contract import write_readonly
from standard.build_cache import build_inputs, compatibility_error, digest, shard_of

OUT = Path('verification').resolve()


def plan(keys, index, rebuild_all=False):
    """Return the changed and removed shards and the modules to build."""
    shards = {}
    for module, key in keys['modules'].items():
        shards.setdefault(shard_of(module), {})[module] = key
    previous = {} if index is None or compatibility_error(index, keys) else index['shards']
    changed = sorted(name for name, modules in shards.items()
                     if rebuild_all or previous.get(name, {}).get('modules') != modules)
    removed = sorted(set(previous) - set(shards))
    return shards, previous, changed, removed


def closure(modules, dependencies):
    needed, stack = set(), list(modules)
    while stack:
        module = stack.pop()
        if module not in needed:
            needed.add(module)
            stack.extend(dependencies[module])
    return needed


def main():
    prepared = OUT/'prepared'
    contract = json.loads((prepared/'contract.json').read_text())
    profile = json.loads((OUT/'profile.json').read_text())
    profile.pop('candidate_cache', None)
    keys = build_inputs(contract, profile, json.loads((prepared/'libraries.json').read_text()),
                        json.loads((OUT/'tool-pins.json').read_text()))
    with tempfile.TemporaryDirectory(dir=OUT, prefix='build-index-') as tmp:
        index = fetch_index(Path(tmp))
    rebuild_all = os.environ.get('QRH_CACHE_REBUILD_ALL', 'false')
    if rebuild_all not in ('true', 'false'):
        raise ValueError('QRH_CACHE_REBUILD_ALL must be true or false')
    shards, previous, changed, removed = plan(keys, index, rebuild_all == 'true')
    needed = closure([m for name in changed for m in shards[name]], contract['module_dependencies'])
    # Every changed shard is rebuilt whole; unchanged imports come from their shards.
    reuse = {shard_of(m) for m in needed} - set(changed)
    order = [m for m in contract['build_order'] if m in needed]
    paths = {'src/'+m.replace('.', '/')+'.lean' for m in order}
    for path in set(contract['source_files']) - paths:
        (prepared/'submission'/path).unlink()
    contract.update(build_order=order,
                    module_dependencies={m: contract['module_dependencies'][m] for m in order},
                    source_files={p: h for p, h in contract['source_files'].items() if p in paths})
    write_readonly(prepared/'contract.json', (json.dumps(contract, indent=2)+'\n').encode())
    if reuse:
        directory = OUT/'build-cache'
        directory.mkdir(exist_ok=True)
        profile['candidate_cache'] = {'shards': fetch_shards(index, reuse, directory), 'signer': digest(KEY)}
    (OUT/'profile.json').write_text(json.dumps(profile, indent=2)+'\n')
    # Recorded before any submitted code runs, outside sandbox-writable paths.
    (OUT/'cache-plan.json').write_text(json.dumps({
        'head_sha': contract['head_sha'], 'keys': keys, 'previous': previous,
        'changed': changed, 'removed': removed}, sort_keys=True)+'\n')
    print(f'{len(changed)} of {len(shards)} shards changed ({len(order)} modules to build, '
          f'{len(reuse)} shards reused); {len(removed)} shards removed', flush=True)
    with open(os.environ.get('GITHUB_OUTPUT', os.devnull), 'a') as output:
        output.write(f'build={"true" if changed else "false"}\n')
        output.write(f'publish={"true" if changed or removed else "false"}\n')


if __name__ == '__main__':
    main()
