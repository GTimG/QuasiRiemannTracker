"""Run both original Argonaut audits and check all reported axiom sets."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, re, subprocess, time

BASE=Path(__file__).resolve().parent
REPO=BASE.parents[1]
PROJECT=BASE/'project'
EVIDENCE=BASE/'evidence'
LEAN=REPO/'compressed/toolchains/lean-4.34.1-linux/bin/lean'
ALLOWED={'propext','Classical.choice','Quot.sound'}
TARGETS=[
 'OAI.DirichletCharacter.LFunction_ne_zero_of_perturbed_boundary_lt_re',
 'OAI.riemannZeta_ne_zero_of_perturbed_boundary_lt_re',
 'OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_perturbed_boundary_lt_re']
FILES=['PerturbedBoundaryMainCurrentFullAuditV2.lean','HUBBLE-PrincipalV2-TerminalAudit.lean']

def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

build_path=BASE/'native/build-result.json'
build=json.loads(build_path.read_text())
assert build['status']=='PASS' and not build['stronger_local_result_used']
env=dict(os.environ)
env['LEAN_PATH']=(BASE/'native/lean-path.txt').read_text().strip()

def audit(name):
    source=PROJECT/'audits'/name
    log=EVIDENCE/(name+'.log')
    cmd=[str(LEAN),'-j4','-DautoImplicit=false','-R',str(PROJECT),str(source)]
    started=time.time()
    with log.open('w') as output:
        run=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=output,stderr=subprocess.STDOUT)
    text=log.read_text()
    printed={name:sorted(set(x.strip() for x in axioms.split(',') if x.strip()))
             for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
    success=(run.returncode==0 and all(t in printed for t in TARGETS)
             and all(set(ax)<=ALLOWED for ax in printed.values())
             and 'sorryAx' not in text)
    return {'status':'PASS' if success else 'FAIL','returncode':run.returncode,
            'source':str(source),'source_sha256':sha(source),'command':cmd,
            'log':str(log),'log_sha256':sha(log),'seconds':round(time.time()-started,3),
            'printed_axioms':printed}

with ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(audit,FILES))
result={'status':'PASS' if all(r['status']=='PASS' for r in results) else 'FAIL',
        'verified_utc':datetime.now(timezone.utc).isoformat(),'candidate':'Argonaut Math v0.1.8',
        'entry_module':'PerturbedBoundaryMain','targets':TARGETS,
        'threshold':'3499999/4000000','compiler':str(LEAN),'compiler_sha256':sha(LEAN),
        'compiler_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
        'native_build_report':str(build_path),'native_build_report_sha256':sha(build_path),
        'inventory':str(EVIDENCE/'operator-inventory.json'),'inventory_sha256':sha(EVIDENCE/'operator-inventory.json'),
        'lean_path':env['LEAN_PATH'],'standard_axioms':sorted(ALLOWED),'audits':results,
        'build_scope':build['native_build_scope'],'stronger_local_result_used':False,
        'independent_kernel_replay':'Performed separately by the shared verification driver; not claimed by this native-only report.'}
(EVIDENCE/'native-build.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'audits':len(results),'target_theorems':len(TARGETS),
                  'report_sha256':sha(EVIDENCE/'native-build.json')}))
raise SystemExit(result['status']!='PASS')
