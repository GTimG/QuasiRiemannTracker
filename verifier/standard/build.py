"""Compile prepared shared submission modules for the build cache; no proof check.

This mirrors replay.py's sandbox, library authentication and per-module
compilation, without the challenge, Comparator or kernels. Its output is a
cache of compiled modules: admission still exports every proof and re-checks it
with Comparator and all three kernels, so a cached module cannot make a proof pass.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, sys, tarfile, time
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from worker_resources import replay_budget_seconds, worker_capacity
from standard.compile import compile_modules, publish_module
from standard.build_cache import build_inputs, restore_shards

if sys.flags.optimize or os.getuid() == 0:
    raise SystemExit('Use unoptimized Python as an unprivileged worker user')

sha = lambda p: hashlib.file_digest(open(p, 'rb'), 'sha256').hexdigest()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--profile', type=Path, required=True)
parser.add_argument('--prepared', type=Path, required=True)
parser.add_argument('--work', type=Path, required=True)
parser.add_argument('--tool-pins', type=Path, required=True)
args = parser.parse_args()
profile = json.loads(args.profile.read_text())
prepared = args.prepared.resolve()
contract = json.loads((prepared/'contract.json').read_text())
assert contract.get('purpose') == 'shared-build-cache'
assert re.fullmatch(r'[a-f0-9]{40}', contract['head_sha'])
ref = Path(profile['palomar']).resolve()
sys.path.insert(0, str(ref))
from scripts import verify_submission as v
assert sha(ref/'scripts/verify_submission.py') == 'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2'
work = args.work.resolve()
work.mkdir(mode=0o700)
for name in ['candidate-lib', 'logs', 'home', 'tmp', 'control']:
    (work/name).mkdir()
old = Path(profile['source_toolchain']).resolve()
source = work/'source'
shutil.copytree(Path(profile['submission']).resolve(), source)
libs = [Path(p).resolve() for p in profile['libraries']]
inputs = {str(p.relative_to(source)): sha(p) for p in source.rglob('*') if p.is_file()}
assert inputs == contract['source_files']
library_inventory = json.loads((prepared/'libraries.json').read_text())
assert sha(prepared/'libraries.json') == contract['library_inventory_sha256']
def check_libraries():
    for filename, expected in library_inventory.items():
        path = Path(filename)
        assert any(path.is_relative_to(lib) for lib in libs)
        assert not path.is_symlink() and sha(path) == expected, filename
print('Authenticate pinned library snapshot', flush=True)
check_libraries()
v._BWRAP = Path(profile.get('bwrap', '/usr/bin/bwrap'))
v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS, 'memory_high_percent': 75, 'memory_max_percent': 85, 'tasks_max': 256}
v.install_execution_deadline(budget_seconds=replay_budget_seconds())
approved_tools = json.loads(args.tool_pins.read_text())
assert sha(old/'bin/lean') == approved_tools['source_lean'], 'Source compiler pin differs'
python, touch = Path('/usr/bin/python3').resolve(), Path('/usr/bin/touch')
tools = v.tool_snapshot([v._BWRAP, old/'bin/lean', python, touch])
capacity = worker_capacity()
jobs = capacity['threads']
env = {'PATH': str(old/'bin')+':/usr/bin:/bin', 'HOME': str(work/'home'), 'TMPDIR': str(work/'tmp'),
       'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1'}
system = v.system_readable_paths()
candidate_env = {**env, 'LEAN_PATH': ':'.join(map(str, [work/'candidate-lib', *libs]))}
print('Sandbox controls', flush=True)
v.verify_sandbox_confinement(source/'denied-write', work/'denied-read', positive_read=next(source.rglob('*.lean')),
    python=python, touch=touch, cwd=source, environment=candidate_env,
    writable_directories=[work/'candidate-lib', work/'home', work/'tmp'],
    protected_write_directories=[source, *libs], readable_paths=[source, *libs, *system],
    executable_paths=[old, Path('/usr')], tools=tools)
keys = build_inputs(contract, profile, library_inventory, approved_tools)
# Written before any submitted code runs, outside every sandbox-writable path.
(work/'build-inputs.json').write_text(json.dumps(keys, sort_keys=True)+'\n')
cached_modules = set()
cache = profile.get('candidate_cache')
if cache:
    try:
        cached_modules = restore_shards(cache, work/'candidate-lib', keys)
        print(f'Reused {len(cached_modules)} authenticated compiled modules', flush=True)
    except (ValueError, KeyError, TypeError, OSError, tarfile.TarError) as error:
        print(f'Build cache miss: {error}; compiling source', flush=True)
        shutil.rmtree(work/'candidate-lib')
        (work/'candidate-lib').mkdir()
order = contract['build_order']
dependencies = contract['module_dependencies']
print(f'Compiling {len(order) - len(cached_modules)} of {len(order)} shared modules, up to {jobs} at once', flush=True)
module_started = {}
def compile_one(module, module_threads):
    if module in cached_modules:
        return
    started = time.monotonic()
    retry = module in module_started
    module_started.setdefault(module, started)
    lean_threads = 1 if retry else module_threads
    assert re.fullmatch(r'Submissions(?:\.[A-Za-z_][A-Za-z0-9_]*)+', module)
    relative = module.replace('.', '/')
    scratch = work/'compilers'/module
    if scratch.exists():
        shutil.rmtree(scratch)
    for part in ['out', 'home', 'tmp']:
        (scratch/part).mkdir(parents=True, exist_ok=True)
    output = scratch/'out'/'module.olean'
    environment = {**candidate_env, 'HOME': str(scratch/'home'), 'TMPDIR': str(scratch/'tmp')}
    memory_limit = max(1024**3, capacity['memory_bytes'] * 3 // 4 * module_threads // jobs)
    result = v.sandboxed_run([str(old/'bin/lean'), f'-j{lean_threads}', '-o', str(output), relative+'.lean'],
        cwd=source/'src', environment=environment,
        writable_directories=[scratch/'out', scratch/'home', scratch/'tmp'],
        readable_paths=[work/'candidate-lib', *libs, *system], executable_paths=[old, Path('/usr')],
        tools=tools, timeout=max(0, 1800 - (time.monotonic() - module_started[module])),
        resource_properties=(f'MemoryMax={memory_limit}',))
    (work/'logs'/('compile-'+module+'.log')).write_text(result.stdout+'\n'+result.stderr)
    if result.returncode:
        raise RuntimeError(f'compile-{module} failed: '+result.stderr[-2000:])
    publish_module(output, work/'candidate-lib'/(relative+'.olean'))
    shutil.rmtree(scratch)
    print(f'Compiled {module} in {time.monotonic()-started:.1f}s', flush=True)
compile_modules(order, dependencies, compile_one, jobs=jobs,
    is_memory_error=lambda error: isinstance(error, v.ResourceExhausted) and 'result oom-kill)' in str(error))
v.verify_tool_snapshot(tools)
assert inputs == {str(p.relative_to(source)): sha(p) for p in source.rglob('*') if p.is_file()}
check_libraries()
(work/'build-result.json').write_text(json.dumps({
    'status': 'BUILT', 'built_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'head_sha': contract['head_sha'], 'modules': len(order), 'reused': len(cached_modules),
    'build_inputs_sha256': sha(work/'build-inputs.json')}, indent=2)+'\n')
print(f'Built {len(order)} shared modules at {contract["head_sha"]}', flush=True)
