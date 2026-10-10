"""Compile Argonaut's unchanged additions against individually audited caches.

Cached OpenAI sources are equal modulo CRLF/LF; both original and canonical
byte hashes are retained. No stronger local theorem is imported.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib, json, os, subprocess, time

BASE=Path(__file__).resolve().parent
REPO=BASE.parents[1]
PROJECT=BASE/'project'
CANONICAL=REPO/'compressed'
OUT=BASE/'native'
BUILD=OUT/'lib'
LOGS=OUT/'logs'
TOOLCHAIN=CANONICAL/'toolchains/lean-4.34.1-linux'
LEAN=TOOLCHAIN/'bin/lean'
GRAPH=json.loads((BASE/'evidence/source-build-manifest.json').read_text())['modules']
CG=json.loads((CANONICAL/'audit/local-selected-source-graph.json').read_text())
CR=json.loads((CANONICAL/'audit/local-build-records.json').read_text())
ROOTS=[Path(p) for p in (CANONICAL/'audit/local-lean-path.txt').read_text().strip().split(':')]
ROOTS += [TOOLCHAIN/'lib/lean']

def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

OUT.mkdir(exist_ok=True);BUILD.mkdir(exist_ok=True);LOGS.mkdir(exist_ok=True)
sources={};reused={};source_files={};artifact_files={}
for m,e in GRAPH.items():
    p=Path(e['source'])
    assert sha(p)==e['source_sha256'],p
    source_files[str(p.relative_to(REPO))]=e['source_sha256']
    rel=Path(*m.split('.')).with_suffix('.olean')
    cache=next((r/rel for r in ROOTS if (r/rel).is_file()),None)
    if cache is None:
        assert p.is_relative_to(PROJECT),p
        sources[m]=p
        continue
    # The toolchain pins its own sources/artifacts. All other reused artifacts
    # have an explicit canonical source matched to the original archive.
    if m in CG:
        canonical=CANONICAL/CG[m]['source']
        assert sha(canonical)==CG[m]['sha256']
    elif p.is_relative_to(TOOLCHAIN):
        canonical=p
    elif p.is_relative_to(PROJECT/'.lake/packages'):
        canonical=CANONICAL/'formalization/.lake/packages'/p.relative_to(PROJECT/'.lake/packages')
    elif p.is_relative_to(PROJECT/'OAI'):
        canonical=CANONICAL/'upstream/openai-math/lean'/p.relative_to(PROJECT)
    else:raise RuntimeError('No audited source mapping for '+m)
    assert canonical.is_file(),(m,canonical)
    a=p.read_bytes();b=canonical.read_bytes()
    assert a.replace(b'\r\n',b'\n')==b.replace(b'\r\n',b'\n'),m
    source_files[str(canonical.relative_to(REPO))]=sha(canonical)
    artifacts={}
    for suffix in ['', '.private', '.server']:
        f=Path(str(cache)+suffix)
        if f.is_file():artifacts[str(f)]=sha(f)
    if m in CR:
        assert artifacts[str(cache)]==CR[m]['olean_sha256'],m
    reused[m]={'original_source':str(p),'original_source_sha256':e['source_sha256'],
               'compiled_source':str(canonical),'compiled_source_sha256':sha(canonical),
               'newline_normalization_only':a!=b,'artifacts':artifacts}
    artifact_files.update(artifacts)
    # Lean chooses the first namespace directory in LEAN_PATH, so OAI gets a
    # complete read-only overlay containing the cached and new modules.
    if m.startswith('OAI.') or m=='OAI':
        for f in artifacts:
            target=BUILD/Path(*m.split('.')).with_suffix('.olean')
            target=Path(str(target)+f[len(str(cache)):])
            target.parent.mkdir(parents=True,exist_ok=True)
            if not target.exists():target.symlink_to(f)
env=dict(os.environ)
env['LEAN_PATH']=':'.join(map(str,[BUILD,*ROOTS[:-1]]))
(OUT/'lean-path.txt').write_text(env['LEAN_PATH']+'\n')
assert not any(m=='QRH' or m.startswith('QRH.') for m in GRAPH)
print(f'Audited closure: {len(GRAPH)} modules; {len(sources)} fresh; {len(reused)} source-matched caches',flush=True)
save(OUT/'reused-foundation.json',reused)
pending=set(sources);done=set(reused);running={};records={};failed=[]

def compile_one(m):
    source=sources[m];base=source
    for _ in m.split('.'):base=base.parent
    assert base.joinpath(*m.split('.')).with_suffix('.lean')==source
    artifact=BUILD/Path(*m.split('.')).with_suffix('.olean')
    artifact.parent.mkdir(parents=True,exist_ok=True)
    log=LOGS/(m+'.log')
    cmd=[str(LEAN),'-j1','-DautoImplicit=false','-R',str(base),'-o',str(artifact),str(source)]
    start=time.time()
    with log.open('w') as f:
        r=subprocess.run(cmd,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
    record={'returncode':r.returncode,'seconds':round(time.time()-start,3),'source':str(source),
            'source_sha256':sha(source),'log':str(log),'command':cmd,'artifacts':{}}
    if r.returncode==0:
        for suffix in ['', '.private', '.server']:
            p=Path(str(artifact)+suffix)
            if p.is_file():record['artifacts'][str(p)]=sha(p)
    return record

with ThreadPoolExecutor(max_workers=8) as pool:
    while pending or running:
        for m in sorted(pending):
            if len(running)>=8 or failed:break
            if set(GRAPH[m]['imports'])<=done:
                pending.remove(m);running[pool.submit(compile_one,m)]=m
        if not running:
            if pending and not failed:raise RuntimeError('Unresolved dependency: '+str(sorted(pending)))
            break
        completed,_=wait(running,return_when=FIRST_COMPLETED)
        for f in completed:
            m=running.pop(f);r=f.result();records[m]=r
            if r['returncode']:
                failed.append(m);print('FAIL '+m+'; '+r['log'],flush=True)
            else:
                done.add(m);artifact_files.update(r['artifacts'])
                print(f'PASS {len(records)}/{len(sources)} {m} ({r["seconds"]}s)',flush=True)
    status='FAIL' if failed or pending else 'PASS'
result={'status':status,'entry':'PerturbedBoundaryMain','compiler':str(LEAN),'compiler_sha256':sha(LEAN),
        'lean_path':env['LEAN_PATH'],'workers':8,'cpu_affinity':sorted(os.sched_getaffinity(0)),
        'compiled':records,'reused_manifest':'reused-foundation.json','reused_manifest_sha256':sha(OUT/'reused-foundation.json'),
        'reused_count':len(reused),'failed':failed,'pending':sorted(pending),
        'native_build_scope':'All candidate additions and missing foundation modules compiled unchanged. Canonical caches matched original sources, allowing only CRLF/LF normalization.',
        'full_lake_attempt':'../evidence/full-lake-attempt.json','stronger_local_result_used':False}
save(OUT/'build-result.json',result)
for p in [PROJECT/'lakefile.task18-reviewed-overlay-v1.lean',PROJECT/'lake-manifest.json',PROJECT/'lean-toolchain']:
    source_files[str(p.relative_to(REPO))]=sha(p)
inventory={'source_files':source_files,'artifact_files':artifact_files,'source_root':str(REPO),
           'source_manifest_sha256':hashlib.sha256(json.dumps(source_files,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
           'native_build_success':status=='PASS','candidate_imports_no_QRH':True,
           'compiler':result['compiler'],'compiler_sha256':result['compiler_sha256'],
           'native_build_report':str(OUT/'build-result.json'),'reused_manifest_sha256':result['reused_manifest_sha256']}
save(BASE/'evidence/operator-inventory.json',inventory)
raise SystemExit(status!='PASS')
