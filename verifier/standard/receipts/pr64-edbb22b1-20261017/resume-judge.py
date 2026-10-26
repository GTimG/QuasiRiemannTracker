"""Replay prepared standard submission with Palomar's unmodified sandbox and kernels."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, sys, tarfile, time
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from worker_resources import worker_capacity
from standard.judge import judge_exports
from standard.compile import compile_modules, publish_module
from standard.build_cache import build_inputs, restore_cache

if sys.flags.optimize or os.getuid() == 0:
    raise SystemExit('Use unoptimized Python as an unprivileged worker user')

sha = lambda p: hashlib.file_digest(open(p, 'rb'), 'sha256').hexdigest()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--profile', type=Path, required=True)
parser.add_argument('--prepared', type=Path, required=True)
parser.add_argument('--work', type=Path, required=True)
parser.add_argument('--tool-pins', type=Path, default=Path(__file__).parent/'tool-pins.json')
args = parser.parse_args()
profile = json.loads(args.profile.read_text())
prepared = args.prepared.resolve()
contract = json.loads((prepared/'contract.json').read_text())
ref = Path(profile['palomar']).resolve()
sys.path.insert(0, str(ref))
from scripts import verify_submission as v
assert sha(ref/'scripts/verify_submission.py') == 'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2'
work = args.work.resolve()
assert work.is_dir()
for name in ['challenge-src','challenge-lib','candidate-lib','solution-src','solution-lib','exports','logs','home','tmp','control','preflight']:
    assert (work/name).is_dir()
old = Path(profile['source_toolchain']).resolve()
judge = Path(profile['judge_toolchain']).resolve()
exporter = Path(profile['exporter']).resolve()
source = work/'source'
assert source.is_dir()
libs = [Path(p).resolve() for p in profile['libraries']]
manifest = contract['manifest']
assert re.fullmatch(r'[a-f0-9]{40}',contract['head_sha'])
inputs = {str(p.relative_to(source)):sha(p) for p in source.rglob('*') if p.is_file()}
assert inputs == contract['source_files']
for name in ['Challenge','Solution']:
    src = prepared/(name+'.lean')
    assert sha(src) == contract['generated_files'][name+'.lean']
    assert sha(src) == sha(work/('challenge-src' if name=='Challenge' else 'solution-src')/(name+'.lean'))
assert sha(prepared/'contract.json') == sha(work/'contract.json')
library_inventory = json.loads((prepared/'libraries.json').read_text())
assert sha(prepared/'libraries.json') == contract['library_inventory_sha256']
def check_libraries():
    for filename, expected in library_inventory.items():
        path = Path(filename)
        assert any(path.is_relative_to(lib) for lib in libs)
        assert not path.is_symlink() and sha(path) == expected, filename
print('Authenticate pinned library snapshot',flush=True)
check_libraries()
v._BWRAP = Path(profile.get('bwrap', '/usr/bin/bwrap'))
v.VERIFICATION_LIMITS = {**v.VERIFICATION_LIMITS,'memory_high_percent':75,'memory_max_percent':85,'tasks_max':256}
# Compilation, export and all three kernel checks share this deadline.
# Keep the Actions check step longer so timeout evidence can still be retained.
v.install_execution_deadline(budget_seconds=21600)
bundled = {name:judge/'bin'/name for name in v.TOOLCHAIN_TOOLS}
approved_tools=json.loads(args.tool_pins.read_text())
selected_tools={'source_lean':old/'bin/lean','exporter':exporter,**{'judge_'+name:path for name,path in bundled.items()}}
assert {name:sha(path) for name,path in selected_tools.items()} == approved_tools, 'Checker tool pins differ'
python, touch = Path('/usr/bin/python3').resolve(), Path('/usr/bin/touch')
tools = v.tool_snapshot([*bundled.values(),v._BWRAP,old/'bin/lean',exporter,python,touch])
(work/'tools.json').write_text(json.dumps({str(k):val for k,val in tools.items()},indent=2)+'\n')
capacity = worker_capacity()
threads = capacity['threads']
print(f'Proof compilation: using {threads} Lean threads', flush=True)
env = {'PATH':str(old/'bin')+':/usr/bin:/bin','HOME':str(work/'home'),'TMPDIR':str(work/'tmp'),'LANG':'C.UTF-8','LEAN_ABORT_ON_PANIC':'1'}
system = v.system_readable_paths()
phases=json.loads((work/'phases.json').read_text())
def stage(name):
    phases.append({'phase':name,'at':datetime.datetime.now(datetime.timezone.utc).isoformat()})
    (work/'phases.json').write_text(json.dumps(phases,indent=2)+'\n')
    print(name,flush=True)
def log(name,result):
    (work/'logs'/(name+'.log')).write_text(result.stdout+'\n'+result.stderr)
    if result.returncode: raise RuntimeError(name+' failed: '+result.stderr[-2000:])

# Resume only the immutable, completed source/export checkpoint after a recorded OOM.
checkpoint = json.loads((work/'source-export-checkpoint.json').read_text())
assert checkpoint['original_driver_sha256'] == sha(Path(__file__).with_name('replay.py'))
assert checkpoint['head_sha'] == contract['head_sha']
for name, expected in checkpoint['files'].items():
    assert sha(work/name) == expected, name
assert checkpoint['freshly_compiled'] == 913
assert checkpoint['authenticated_cached_modules'] == 2923
assert phases[-1]['phase'] == 'Comparator and Lean, NanoDa, con-ron'
original_config=json.loads((work/'comparator.json').read_text())
config={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['QRH.canonical_bound'],'definition_names':[],'permitted_axioms':sorted(v.STANDARD_AXIOMS),'external_kernels':v.protected_kernels(bundled)}
assert original_config == config
assert config['external_kernels']['con-ron'][-1] == '--jobs=2'
config['external_kernels']['con-ron'][-1] = '--jobs=1'
(work/'retry-comparator.json').write_text(json.dumps(config,indent=2)+'\n')
# The resource retry changes only the con-ron job count. Repeat sandbox and checker controls.
stage('retry sandbox and kernel controls')
v.verify_sandbox_confinement(work/'control/retry-denied-write',work/'retry-denied-read',positive_read=work/'control/read.txt',python=python,touch=touch,cwd=work/'control',environment=env,writable_directories=[work/'home',work/'tmp'],protected_write_directories=[work/'control'],readable_paths=[work/'control',*system],executable_paths=[old,Path('/usr')],tools=tools)
v.comparator_preflight(work/'retry-preflight',lean=bundled['lean'],leanexport=bundled['leanexport'],lake=bundled['lake'],lean_prefix=judge,bwrap=v._BWRAP,kernels=config['external_kernels'],primitives=v.primitive_targets(judge),environment={**env,'PATH':str(judge/'bin')+':/usr/bin:/bin'},executable_paths=[judge,v._BWRAP,Path('/usr')],tools=tools,timeout=300)
v.verify_export(work/'exports/Challenge.export')
v.verify_export(work/'exports/Solution.export')
challenge_hash=checkpoint['files']['exports/Challenge.export']
solution_hash=checkpoint['files']['exports/Solution.export']
cache=profile['candidate_cache']
cached_modules=set(range(checkpoint['authenticated_cached_modules']))
stage('Comparator and Lean, NanoDa, con-ron')
print(f"Kernel verification: {capacity['kernel_jobs']} simultaneous checks",flush=True)
result=judge_exports(v,config=work/'retry-comparator.json',challenge_export=work/'exports/Challenge.export',solution_export=work/'exports/Solution.export',scratch=work/'retry-judge',bundled=bundled,lean_prefix=judge,environment=env,tools=tools,capacity=capacity,timeout=7200)
log('judge',result)
transcript=result.stdout+'\n'+result.stderr
assert 'Your solution is okay!' in transcript and all(k+' kernel accepts the solution' in transcript for k in ['Lean default','nanoda','con-ron'])
v.verify_tool_snapshot(tools)
assert sha(work/'exports/Challenge.export') == challenge_hash
assert sha(work/'exports/Solution.export') == solution_hash
assert inputs == {str(p.relative_to(source)):sha(p) for p in source.rglob('*') if p.is_file()}
check_libraries()
stage('accepted')
report={'status':'PASS','verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewed_pr_head':contract['head_sha'],'source_commit':contract['source_commit'],'source_repository':contract['repository'],'result_id':manifest['id'],'theta_exact':manifest.get('exact_bound',manifest['theta']['numerator']+'/'+manifest['theta']['denominator']),**({'bound_interval':manifest['bound_interval']} if 'bound_interval' in manifest else {}),'targets':config['theorem_names'],'allowed_axioms':config['permitted_axioms'],'kernels':['Lean default','nanoda','con-ron'],'judge_exit_code':result.returncode,'sandbox_preflight':'PASS','candidate_mount_preflight':'PASS','challenge_exported_before_candidate_execution':True,'receipt_outside_candidate':True,'source_files':inputs,'submission_trees':contract.get('submission_trees', {}),'library_inventory_sha256':contract['library_inventory_sha256'],'driver_sha256':sha(Path(__file__)),'palomar_sha256':sha(ref/'scripts/verify_submission.py'),'tool_pins':approved_tools,'artifacts':{str(p.relative_to(work)):sha(p) for p in work.rglob('*') if p.is_file() and p.suffix in ['.log','.json','.lean','.export']}}
if cached_modules:
    report['build_cache'] = {**{k:cache[k] for k in ['url','sha256','signer']}, 'modules_reused':len(cached_modules)}
report['resume_provenance'] = {'checkpoint_sha256':sha(work/'source-export-checkpoint.json'), 'original_driver_sha256':checkpoint['original_driver_sha256'], 'reason':'Original final checker exhausted memory; repeat the entire Comparator/three-kernel stage with con-ron --jobs=1 on hash-frozen exports after reauthenticating source, tools, libraries and completed-build evidence.'}
(work/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print('Accepted '+manifest['id']+' at '+contract['head_sha'],flush=True)
