"""Build the pinned checker environment before any submitted code executes."""
from pathlib import Path
import hashlib, json, os, shlex, shutil, subprocess, sys, time
warm_cache = sys.argv[1:] == ['--warm-cache']
if sys.argv[1:] and not warm_cache:
    raise SystemExit('Usage: setup.py [--warm-cache]')
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'verifier'))
from worker_resources import worker_threads
threads = worker_threads()
print(f'Worker setup: using {threads} Lean threads', flush=True)
OUT = ROOT / 'verification'
ENV_ROOT = Path(os.environ.get('QRH_WORKER_ROOT', str(OUT / 'environment'))).resolve()
ENV_ROOT.mkdir(parents=True, exist_ok=True)
PINS = json.loads((ROOT/'verifier/pins.json').read_text())
sha = lambda p: hashlib.file_digest(open(p, 'rb'), 'sha256').hexdigest()
def run(*args, cwd=None, env=None):
    command = list(map(str,args))
    suffix = f' ... ({len(command)-8} more arguments)' if len(command) > 8 else ''
    print('Worker setup: '+shlex.join(command[:8])+suffix, flush=True)
    started = time.monotonic()
    subprocess.run(command, cwd=cwd, env=env, check=True)
    print(f'Worker setup command completed in {time.monotonic()-started:.1f}s', flush=True)
def clone(url, rev, dest):
    if not dest.exists():
        run('git','init',dest)
        run('git','-C',dest,'fetch','--depth=1',url,rev)
        run('git','-C',dest,'checkout','--detach','FETCH_HEAD')
    if subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip() != rev:
        raise RuntimeError('Dependency revision differs: '+str(dest))
def toolchain(version, digest):
    dest = ENV_ROOT / ('lean-'+version+'-linux')
    if not dest.exists():
        archive = ENV_ROOT / (version+'.tar.zst')
        run('curl','--fail','--location','--retry','3','--proto','=https','--tlsv1.2',
            'https://github.com/leanprover/lean4/releases/download/v'+version+'/lean-'+version+'-linux.tar.zst','-o',archive)
        if sha(archive) != digest: raise RuntimeError('Toolchain archive checksum mismatch')
        run('tar','--zstd','-xf',archive,'-C',ENV_ROOT)
        archive.unlink()
    return dest
source = toolchain('4.34.1','47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4')
judge = toolchain('4.35.0-rc2','b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049')
env = {**os.environ, 'PATH':str(source/'bin')+':'+os.environ['PATH'], 'LEAN_NUM_THREADS':str(threads)}
palomar = ENV_ROOT/'palomar'
clone('https://github.com/PalomarRegistry/PalomarSubmission.git','d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44',palomar)
bwrap = ENV_ROOT/'bwrap-bin/bwrap'
# Run installation on every VM so its path receives the required AppArmor profile.
run('bash',palomar/'scripts/install_bwrap.sh',bwrap.parent)
export = ENV_ROOT/'lean4export'
clone(PINS['lean4export']['url'],PINS['lean4export']['commit'],export)
(export/'lean-toolchain').write_text(PINS['lean']+'\n')
run(source/'bin/lake','build',cwd=export,env=env)
exporter = export/'.lake/build/bin/lean4export'
base_tools = json.loads((ROOT/'verifier/standard/tool-pins.json').read_text())
actual = {'source_lean':sha(source/'bin/lean'), 'exporter':sha(exporter),
          **{'judge_'+name:sha(judge/'bin'/name) for name in ['lake','lean','leanexport','leanchecker','nanoda_bin','con-ron']}}
if any(actual[k] != digest for k,digest in base_tools.items() if k != 'exporter'):
    raise RuntimeError('Downloaded checker tools differ from pinned binaries')
# The exporter is freshly built from its protected source revision. Its binary
# depends on the build platform; snapshot it before candidate execution.
(OUT/'tool-pins.json').write_text(json.dumps(actual,indent=2)+'\n')
project = ENV_ROOT/'project'
project.mkdir(exist_ok=True)
shutil.copyfile(ROOT/'verifier/standard/lake-manifest.json',project/'lake-manifest.json')
lakefile = (ROOT/'verifier/standard/lakefile.lean').read_text()
(project/'lakefile.lean').write_text(lakefile)
(project/'lean-toolchain').write_text(PINS['lean']+'\n')
packages = project/'.lake/packages'; packages.mkdir(parents=True,exist_ok=True)
for p in json.loads((project/'lake-manifest.json').read_text())['packages']:
    name = p['name'].strip('«»'); dest = packages/name
    clone(p['url'],p['rev'],dest)
    if name in ['rellich-kondrachov','PrimeNumberTheoremAnd']:
        patch = ROOT/'verifier/actions/patches'/(name+'-lean4341.patch')
        if subprocess.run(['git','-C',str(dest),'apply','--reverse','--check',str(patch)],capture_output=True).returncode:
            run('git','-C',dest,'apply',patch)
# The official Mathlib cache is fetched from the pinned dependency sources.
run(source/'bin/lake','exe','cache','get',cwd=project,env=env)
# These package sources are fixed by the protected manifest and compatibility
# patches. A submitted import can select a module within these fixed trees.
package_roots = {'PrimeNumberTheoremAnd': packages/'PrimeNumberTheoremAnd',
                 'RellichKondrachov': packages/'rellich-kondrachov'}
modules = (['PrimeNumberTheoremAnd.Wiener',
            'RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich']
           if warm_cache else json.loads((OUT/'imports.json').read_text()))
for module in modules:
    parts = module.split('.')
    if parts[0] not in package_roots or any(not part.isascii() or not part.isidentifier() for part in parts):
        raise RuntimeError('Invalid pinned package import')
    path = package_roots[parts[0]]/Path(*parts).with_suffix('.lean')
    if not path.is_file(): raise RuntimeError('Missing pinned package source: '+module)
if modules: run(source/'bin/lake', 'build', *sorted(set(modules)), cwd=project, env=env)
# Import Mathlib exactly as the canonical challenge does, before checking source.
(project/'Challenge.lean').write_text('import Mathlib\n')
run(source/'bin/lake','build','Challenge',cwd=project,env=env)
(project/'Challenge.lean').unlink()
for p in (project/'.lake/build').rglob('Challenge.*'): p.unlink()
if warm_cache:
    print('Shared checking environment ready',flush=True)
    sys.exit(0)
libraries = sorted(p.resolve() for p in packages.glob('*/.lake/build/lib/lean') if p.is_dir())
inventory = {}
for lib in libraries:
    for p in sorted(lib.rglob('*')):
        if p.is_symlink(): raise RuntimeError('Symlink in checker library: '+str(p))
        if p.is_file(): inventory[str(p)] = sha(p)
from library_contract import bind_libraries
prepared = OUT/'prepared'
bind_libraries(prepared, inventory)
profile = dict(palomar=str(palomar),source_toolchain=str(source),judge_toolchain=str(judge),
               exporter=str(exporter),submission=str(prepared/'submission'),libraries=list(map(str,libraries)), bwrap=str(bwrap))
(OUT/'profile.json').write_text(json.dumps(profile,indent=2)+'\n')
print('Checker environment ready',flush=True)
