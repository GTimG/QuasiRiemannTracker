#!/usr/bin/env python3
"""Compile this project, reusing the exact pinned mathlib official cache.

Unlike build_source.py, this route explicitly trusts downloaded mathlib/package
oleans. OAI, QRH, and both patched packages are always compiled locally. Cache
artifacts, sources, compiler commands, and dependency keys are recorded in a
separate local audit, leaving the upstream source-only audit claims untouched.
"""
from pathlib import Path
from functools import lru_cache
import argparse, concurrent.futures, hashlib, json, os, re, subprocess, time

R = Path(__file__).resolve().parents[1]
P = R / 'formalization'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('modules', nargs='+')
parser.add_argument('--jobs', type=int, default=min(16, len(os.sched_getaffinity(0)))
                    if hasattr(os, 'sched_getaffinity') else min(16, os.cpu_count() or 1))
parser.add_argument('--inventory-only', action='store_true')
args = parser.parse_args()
assert 1 <= args.jobs <= 16
packages = sorted((P / '.lake/packages').iterdir())
roots = [R / 'upstream/openai-math/lean', P] + packages
lean = R / 'toolchains/lean-4.34.1-linux/bin/lean'
base = lean.parent.parent / 'lib/lean'
out = R / 'build/local'
logs = R / 'logs/local-source'
out.mkdir(parents=True, exist_ok=True)
logs.mkdir(parents=True, exist_ok=True)
cache_roots = [p / '.lake/build/lib/lean' for p in packages
               if p.name not in ('rellich-kondrachov', 'PrimeNumberTheoremAnd')]
cache_roots = [p for p in cache_roots if p.is_dir()]
CONFIG = 'lean-4.34.1-local-cache-build-v1'


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def clean(text):
    result = []
    i = depth = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            result.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            result.append(text[i])
            i += 1
    return ''.join(result)


@lru_cache(None)
def find(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    for root in roots:
        path = root / relative
        if path.is_file():
            return root, path
    if base.joinpath(*module.split('.')).with_suffix('.olean').is_file():
        return None
    raise RuntimeError('Missing source ' + module)


graph_file = R / 'audit/local-selected-source-graph.json'
previous_graph = json.loads(graph_file.read_text()) if graph_file.exists() else {}
graph = {}
todo = list(args.modules)
while todo:
    module = todo.pop()
    if module in graph:
        continue
    found = find(module)
    if found is None:
        continue
    root, path = found
    digest = sha(path)
    previous = previous_graph.get(module, {})
    if previous.get('sha256') == digest and previous.get('source') == str(path.relative_to(R)):
        imports = previous['imports']
    else:
        imports = []
        for line in clean(path.read_text()).splitlines():
            match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
            if match:
                imports.extend(d for d in match.group(1).split() if d != 'all')
            elif line.strip() and line.strip() not in ('module', 'prelude'):
                break
        imports = [d for d in imports if find(d) is not None]
    relative = Path(*module.split('.')).with_suffix('.olean')
    cached = None
    if root in packages and root.name not in ('rellich-kondrachov', 'PrimeNumberTheoremAnd'):
        candidate = root / '.lake/build/lib/lean' / relative
        if candidate.is_file():
            cached = candidate
    graph[module] = {'source': str(path.relative_to(R)), 'imports': imports,
                     'sha256': digest,
                     'cache': str(cached.relative_to(R)) if cached else None}
    todo.extend(imports)

graph_file.write_text(json.dumps(graph, indent=2) + '\n')
cache_count = sum(item['cache'] is not None for item in graph.values())
print(f'Source closure: {len(graph)}; official cache: {cache_count}; '
      f'local source: {len(graph)-cache_count}; workers={args.jobs}', flush=True)
if args.inventory_only:
    raise SystemExit(0)

env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(str(p) for p in [out] + cache_roots)
env['LEAN_NUM_THREADS'] = '1'
env['GLIBC_TUNABLES'] = 'glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1'
(R / 'audit/local-lean-path.txt').write_text(env['LEAN_PATH'] + '\n')
done, records, active = {}, {}, {}
pending, failed = set(graph), []
start = time.time()
last_report = 0


def compile_one(module, key, threads):
    item = graph[module]
    root, path = find(module)
    target = out.joinpath(*module.split('.')).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    command = [str(lean), f'-j{threads}']
    if module.startswith(('OAI.', 'QRH.', 'Mathlib.', 'RellichKondrachov.',
                          'MathlibExtensions.', 'PrimeNumberTheoremAnd.')):
        command.append('-DautoImplicit=false')
    if module.startswith('Mathlib.'):
        command.append('-DmaxSynthPendingDepth=3')
    command += ['-o', str(target), str(path.relative_to(root))]
    with (logs / (module + '.log')).open('w') as f:
        f.write(json.dumps({'command': command, 'cwd': str(root),
                            'source_sha256': item['sha256'], 'key': key}) + '\n')
        f.flush()
        module_env = env.copy()
        module_env['LEAN_NUM_THREADS'] = str(threads)
        result = subprocess.run(command, cwd=root, env=module_env, stdout=f,
                                stderr=subprocess.STDOUT)
    if result.returncode == 0:
        target.with_suffix('.source-key').write_text(key)
    return result.returncode


with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or active:
        progressed = False
        ready_sources = sum(not graph[m]['cache'] and all(d in done for d in graph[m]['imports'])
                            for m in pending)
        for module in sorted(pending):
            item = graph[module]
            if not all(d in done for d in item['imports']):
                continue
            free_threads = args.jobs - sum(entry[2] for entry in active.values())
            if free_threads <= 0 and not item['cache']:
                continue
            key = hashlib.sha256((item['sha256'] + ''.join(done[d] for d in item['imports'])
                                  + CONFIG).encode()).hexdigest()
            pending.remove(module)
            progressed = True
            if item['cache']:
                target = R / item['cache']
                done[module] = key
                records[module] = {'mode': 'official-mathlib-cache', 'key': key,
                                   'olean': item['cache'], 'olean_sha256': sha(target)}
                continue
            target = out.joinpath(*module.split('.')).with_suffix('.olean')
            stamp = target.with_suffix('.source-key')
            if target.is_file() and stamp.is_file() and stamp.read_text() == key:
                done[module] = key
                records[module] = {'mode': 'local-source', 'key': key,
                                   'olean': str(target.relative_to(R)), 'olean_sha256': sha(target)}
                continue
            threads = max(1, free_threads // max(1, ready_sources))
            ready_sources -= 1
            active[pool.submit(compile_one, module, key, threads)] = (module, key, threads)
        if active:
            ready, _ = concurrent.futures.wait(active, timeout=10,
                       return_when=concurrent.futures.FIRST_COMPLETED)
            for future in ready:
                module, key, threads = active.pop(future)
                if future.result():
                    failed.append(module)
                    print(f'FAIL {module}: logs/local-source/{module}.log', flush=True)
                else:
                    target = out.joinpath(*module.split('.')).with_suffix('.olean')
                    done[module] = key
                    records[module] = {'mode': 'local-source', 'key': key,
                                       'olean': str(target.relative_to(R)), 'olean_sha256': sha(target)}
        elif not progressed:
            break
        now = time.time()
        if now - last_report > 30 or failed:
            print(f'{len(done)}/{len(graph)} checked; {len(active)} running; '
                  f'{len(failed)} failed; {round(now-start)}s', flush=True)
            last_report = now

summary = {'roots': args.modules, 'closure': len(graph), 'checked': len(done),
           'official_cache_modules': cache_count,
           'local_source_modules': len(graph)-cache_count,
           'failed': failed, 'blocked': sorted(pending), 'seconds': time.time()-start,
           'jobs': args.jobs, 'success': not failed and not pending,
           'thread_policy': 'Distribute the full jobs-thread budget across ready Lean modules',
           'trust_note': 'Official mathlib cache reused; OAI and QRH compiled from source.',
           'configuration': CONFIG}
(R / 'audit/local-build-records.json').write_text(json.dumps(records, indent=2)+'\n')
(R / 'audit/local-build-status.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'blocked'}), flush=True)
raise SystemExit(0 if summary['success'] else 1)
