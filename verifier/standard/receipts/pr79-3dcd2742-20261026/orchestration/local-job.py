#!/usr/bin/env python3
"""Trusted one-off local replay controller; never supplied by a proof candidate."""
from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys, time, traceback

ROOT=Path('/home/runner/repository')
INPUT=Path('/opt/qrh-inputs')
OUT=ROOT/'verification'
EVIDENCE=ROOT/'local-evidence'
JOB=sys.argv[1]
assert JOB in ['pr79','pr72'] and os.getuid()==10001
os.chdir(ROOT)
EVIDENCE.mkdir()
OUT.mkdir()
(ROOT/'verification-context').mkdir()
os.environ.update(QRH_WORKER_THREADS='12',QRH_KERNEL_JOBS='1',PYTHONUNBUFFERED='1')
ALLOWED=['PATH','HOME','LANG','XDG_RUNTIME_DIR','DBUS_SESSION_BUS_ADDRESS','QRH_WORKER_THREADS','QRH_KERNEL_JOBS']
REPLAY_ENV={key:os.environ[key] for key in ALLOWED if key in os.environ}
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
records=[]
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()


def write_json(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2)+'\n')


def run(name,args,*,env=None,timeout=129900,required=True):
    print(f'LOCAL_STAGE {name}',flush=True)
    begun=time.monotonic()
    with (EVIDENCE/(name+'.log')).open('wb') as log:
        process=subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        # The guest systemd service and outer VM watchdog bound the whole run.
        # Stream the transcript while retaining the original bytes for review.
        import threading
        def terminate():
            import signal
            try: os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError: pass
        timer=threading.Timer(timeout,terminate)
        timer.start()
        try:
            for block in iter(lambda:process.stdout.read1(65536),b''):
                log.write(block);log.flush()
                sys.stdout.buffer.write(block);sys.stdout.buffer.flush()
            code=process.wait()
        finally:
            timer.cancel()
    records.append({'stage':name,'exit_code':code,'seconds':time.monotonic()-begun})
    write_json(EVIDENCE/'stages.json',records)
    if required and code: raise RuntimeError(f'{name} exited {code}')
    return code


def preserve(run_dir,destination):
    destination.mkdir(parents=True,exist_ok=True)
    names=['result.json','contract.json','controls.json','phases.json','comparator.json','tools.json',
           'challenge-src/Challenge.lean','solution-src/Solution.lean']
    files=[run_dir/name for name in names]
    files += list((run_dir/'logs').rglob('*.log')) if (run_dir/'logs').exists() else []
    files += list((run_dir/'judge').rglob('*.log')) if (run_dir/'judge').exists() else []
    for src in files:
        if src.is_symlink(): raise ValueError('Symlink in outside-sandbox evidence')
        if src.is_file():
            dst=destination/src.relative_to(run_dir)
            dst.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(src,dst)


def replay_fixture(name,*,negative=None):
    fixture=INPUT/('control' if negative else 'baseline')
    prepared=ROOT/('prepared-'+name)
    shutil.copytree(fixture/'prepared',prepared)
    from library_contract import bind_libraries
    bind_libraries(prepared,inventory)
    if negative:
        # Deliberately invalid fixture; unrelated to either submitted source.
        path=prepared/'submission/src/Candidate/Main.lean'
        signature='''{q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1 / 1 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0'''
        if negative=='sorryAx': body='import Mathlib\nnamespace Candidate\ntheorem bound '+signature+' := by\n  sorry\nend Candidate\n'
        else: body='import Mathlib\nnamespace Candidate\naxiom hidden_assumption '+signature+'\ntheorem bound '+signature+' := hidden_assumption χ hs hpole\nend Candidate\n'
        path.chmod(0o644);path.write_text(body);path.chmod(0o444)
        contract=json.loads((prepared/'contract.json').read_text())
        contract['source_files']['src/Candidate/Main.lean']=sha(path)
        contract_path=prepared/'contract.json'
        contract_path.chmod(0o644);write_json(contract_path,contract);contract_path.chmod(0o444)
    profile={**candidate_profile,'submission':str(prepared/'submission')}
    profile_path=ROOT/('profile-'+name+'.json')
    write_json(profile_path,profile)
    target=ROOT/('run-'+name)
    try:
        code=run(name,['python3','verifier/standard/replay.py','--profile',str(profile_path),
                      '--prepared',str(prepared),'--work',str(target),'--tool-pins',str(OUT/'tool-pins.json')],
                 env=REPLAY_ENV,required=not negative)
    finally:
        preserve(target,EVIDENCE/name)
    if negative:
        logs=(EVIDENCE/(name+'.log')).read_text(errors='replace')+'\n'+'\n'.join(p.read_text(errors='replace') for p in (target/'logs').glob('*.log'))
        phases=json.loads((target/'phases.json').read_text())
        assert code and negative in logs and phases[-1]['phase']=='Comparator and Lean, NanoDa, con-ron',f'{name} did not reject the intended forbidden axiom'
        assert not (target/'result.json').exists(), 'Invalid control produced a success receipt'
    else:
        report=json.loads((target/'result.json').read_text())
        assert report['status']=='PASS' and report['theta_exact']=='7/8'
    return target


status='FAILED'
try:
    for name in ['runtime-manifest.json','protected-runtime-manifest.json','protected-sha.txt','budget-only.patch','local-job.py','local-job.sh','guesthook.sh','vm.py']:
        shutil.copyfile(INPUT/name,EVIDENCE/name)
    manifest=json.loads((INPUT/'runtime-manifest.json').read_text())
    assert all(sha(ROOT/name)==expected for name,expected in manifest['files'].items()),'Runtime differs from immutable host input'
    write_json(EVIDENCE/'context.json',json.loads((INPUT/'jobs'/JOB/'context.json').read_text()))
    shutil.copyfile(INPUT/'jobs'/JOB/'context.json',ROOT/'verification-context/context.json')
    shutil.copytree(INPUT/'jobs'/JOB/'prepared',OUT/'prepared')
    imports=set(json.loads((INPUT/'jobs'/JOB/'imports.json').read_text()))
    imports.update(json.loads((INPUT/'baseline/imports.json').read_text()))
    write_json(OUT/'imports.json',sorted(imports))
    run('setup',['python3','verifier/actions/setup.py'],timeout=7200)
    # Use Tim's reviewed upstream capacity fix before baseline or proof code.
    # setup.py first authenticates every original tool; only NanoDa is replaced.
    bundle=INPUT/'nanoda-upstream'
    provenance=json.loads((bundle/'provenance.json').read_text())
    assert provenance['commit']=='998e0a84e4c1572ca279ff05007af6ec6639405a'
    assert provenance['tests_passed'] is True and sha(bundle/'nanoda_bin')==provenance['binary_sha256']
    profile=json.loads((OUT/'profile.json').read_text())
    pins_path=OUT/'tool-pins.json'
    original_pins=json.loads(pins_path.read_text())
    binary=Path(profile['judge_toolchain'])/'bin/nanoda_bin'
    assert sha(binary)==original_pins['judge_nanoda_bin']
    write_json(EVIDENCE/'original-tool-pins.json',original_pins)
    binary.unlink()
    shutil.copyfile(bundle/'nanoda_bin',binary)
    binary.chmod(0o555)
    assert sha(binary)==provenance['binary_sha256']
    actual_pins={**original_pins,'judge_nanoda_bin':provenance['binary_sha256']}
    write_json(pins_path,actual_pins)
    shutil.copytree(bundle,EVIDENCE/'nanoda-upstream',ignore=shutil.ignore_patterns('nanoda_bin'))
    write_json(EVIDENCE/'runtime-deviation.json',{
        'reason':'Pristine upstream NanoDa 0.4.26, matching Tim PR69/76 capacity remediation',
        'commit':provenance['commit'],'before_sha256':original_pins['judge_nanoda_bin'],
        'after_sha256':provenance['binary_sha256'],
        'baseline_and_controls':'run freshly below before the candidate',
        'other_checker_tools_changed':False})
    print('Authenticated upstream NanoDa replacement installed before controls',flush=True)
    run('restore-build',['python3','verifier/actions/restore-build.py'],timeout=1800)
    candidate_profile=json.loads((OUT/'profile.json').read_text())
    inventory=json.loads((OUT/'prepared/libraries.json').read_text())
    sys.path.insert(0,str(ROOT/'verifier/actions'))
    baseline=replay_fixture('baseline')
    replay_fixture('control-sorry',negative='sorryAx')
    replay_fixture('control-hidden',negative='hidden_assumption')
    # If the signed public archive was unavailable, reuse only this VM's fully
    # accepted baseline build, authenticated against the protected cache recipe.
    if 'candidate_cache' not in candidate_profile:
        sys.path.insert(0,str(ROOT/'verifier'))
        from standard.build_cache import build_inputs,pack_cache
        baseline_report=json.loads((baseline/'result.json').read_text())
        baseline_profile=json.loads((ROOT/'profile-baseline.json').read_text())
        baseline_contract=json.loads((baseline/'contract.json').read_text())
        inputs=build_inputs(baseline_contract,baseline_profile,inventory,baseline_report['tool_pins'])
        archive=OUT/'accepted-baseline-build.tar.gz'
        try:
            pack_cache(baseline/'candidate-lib',archive,inputs)
            candidate_profile['candidate_cache']={'path':str(archive),'sha256':sha(archive),'url':'local-authenticated-baseline','signer':'same-isolated-worker'}
            write_json(OUT/'profile.json',candidate_profile)
        except ValueError as error:
            write_json(EVIDENCE/'baseline-cache.json',{'status':'not-reused','reason':str(error)})
    code=run('candidate',['python3','verifier/actions/run.py'],env=REPLAY_ENV,required=False)
    attempt=json.loads((OUT/'attempt.json').read_text())
    if code or attempt['status']!='accepted': raise RuntimeError(f'Candidate failed: {attempt.get("status")}: {attempt.get("reason")}')
    assert all(sha(ROOT/name)==expected for name,expected in manifest['files'].items()),'Runtime changed during checking'
    status='PASS'
except BaseException as error:
    traceback.print_exc()
    write_json(EVIDENCE/'failure.json',{'type':type(error).__name__,'reason':str(error)})
finally:
    preserve(OUT/'run',EVIDENCE/'candidate')
    for name in ['baseline','control-sorry','control-hidden']:
        preserve(ROOT/('run-'+name),EVIDENCE/name)
    for name in ['attempt.json','profile.json','tool-pins.json','build-cache-status.json','build-cache-inputs.json','prepared/libraries.json']:
        src=OUT/name
        if src.is_file():
            dst=EVIDENCE/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
    shutil.copyfile(ROOT/'verifier/standard/lake-manifest.json',EVIDENCE/'dependency-pins.json')
    shutil.copyfile(ROOT/'verifier/standard/replay.py',EVIDENCE/'replay-driver.txt')
    write_json(EVIDENCE/'local-summary.json',{'job':JOB,'status':status,'started_at':started,'completed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'stages':records,'threads':12,'kernel_jobs':1})
    print(f'LOCAL_COMPLETE {JOB} {status}',flush=True)
sys.exit(0 if status=='PASS' else 1)
