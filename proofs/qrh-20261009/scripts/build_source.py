#!/usr/bin/env python3
"""Bounded, resumable Lean source compiler. No downloaded oleans are used.
Every successful module records source and direct-dependency digests. The Lean
release standard library is the compiler baseline; all other imports are rebuilt.
"""
from pathlib import Path
import argparse, concurrent.futures, hashlib, json, os, re, subprocess, time
from functools import lru_cache
R=Path(__file__).resolve().parents[1]; P=R/'formalization'
parser=argparse.ArgumentParser();parser.add_argument('modules',nargs='+');parser.add_argument('--jobs',type=int,default=6)
parser.add_argument('--inventory-only',action='store_true')
a=parser.parse_args();assert 1<=a.jobs<=8
roots=[R/'upstream/openai-math/lean',P]+sorted((P/'.lake/packages').iterdir())
lean=R/'toolchains/lean-4.34.1-linux/bin/lean'; base=lean.parent.parent/'lib/lean'
out=R/'build/source';out.mkdir(parents=True,exist_ok=True)
logs=R/'logs/source';logs.mkdir(parents=True,exist_ok=True)
def clean(s):
    # Preserve newlines while removing nested comments and line comments.
    result=[];i=0;depth=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2;continue
        if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
        if depth:result.append('\n' if s[i]=='\n' else ' ');i+=1;continue
        if s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j;continue
        result.append(s[i]);i+=1
    return ''.join(result)
@lru_cache(None)
def find(m):
    rel=Path(*m.split('.')).with_suffix('.lean')
    for p in roots:
        if (p/rel).is_file():return p,p/rel
    if base.joinpath(*m.split('.')).with_suffix('.olean').is_file():return None
    raise RuntimeError('Missing source '+m)
graph={};todo=list(a.modules)
while todo:
    m=todo.pop()
    if m in graph:continue
    loc=find(m)
    if loc is None:continue
    root,p=loc;s=p.read_text();deps=[]
    for line in clean(s).splitlines():
        match=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
        if match:deps+=[d for d in match.group(1).split() if d != 'all']
        elif line.strip() and line.strip() not in ('module', 'prelude'):break
    deps=[d for d in deps if find(d) is not None]
    graph[m]=(root,p,deps,hashlib.sha256(p.read_bytes()).hexdigest());todo+=deps
(R/'audit/selected-source-graph.json').write_text(json.dumps({m:{'source':str(p.relative_to(R)),'imports':d,'sha256':h} for m,(r,p,d,h) in graph.items()},indent=2)+'\n')
print(f'Source closure: {len(graph)} modules; workers={a.jobs}',flush=True)
if a.inventory_only:raise SystemExit(0)
env=os.environ.copy();env['LEAN_PATH']=str(out);env['LEAN_NUM_THREADS']='1'
done={};pending=set(graph);active={};failed=[];start=time.time()
def compile_one(m,key):
    root,p,deps,h=graph[m];ofile=out.joinpath(*m.split('.')).with_suffix('.olean');ofile.parent.mkdir(parents=True,exist_ok=True)
    log=logs/(m+'.log')
    cmd=[str(lean),'-j1'] + (['-DautoImplicit=false'] if m.startswith(('OAI.', 'QRH.', 'Mathlib.', 'RellichKondrachov.', 'MathlibExtensions.', 'PrimeNumberTheoremAnd.')) else []) + (['-DmaxSynthPendingDepth=3'] if m.startswith('Mathlib.') else []) + ['-o',str(ofile),str(p.relative_to(root))]
    with log.open('w') as f:
        f.write(json.dumps({'command':cmd,'cwd':str(root),'source_sha256':h,'key':key})+'\n');f.flush()
        proc=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    if proc.returncode==0:ofile.with_suffix('.source-key').write_text(key)
    return proc.returncode
with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
    while pending or active:
        progressed=False
        for m in sorted(pending):
            if len(active)>=a.jobs:break
            root,p,deps,h=graph[m]
            if not all(d in done for d in deps):continue
            key=hashlib.sha256((h+''.join(done[d] for d in deps)+'lean-4.34.1-package-options-v2-j1'+('mathlib-maxSynthPendingDepth=3' if m.startswith('Mathlib.') else '')+('autoImplicit=false' if m.startswith(('RellichKondrachov.', 'MathlibExtensions.', 'PrimeNumberTheoremAnd.')) else '')).encode()).hexdigest()
            ofile=out.joinpath(*m.split('.')).with_suffix('.olean');stamp=ofile.with_suffix('.source-key')
            pending.remove(m);progressed=True
            if ofile.is_file() and stamp.is_file() and stamp.read_text()==key:done[m]=key;continue
            active[pool.submit(compile_one,m,key)]=(m,key)
        if active:
            ready,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in ready:
                m,key=active.pop(f);rc=f.result()
                if rc:failed.append(m);print(f'FAIL {m}: see logs/source/{m}.log',flush=True)
                else:done[m]=key
            if len(done)%50<a.jobs or failed:print(f'{len(done)}/{len(graph)} checked; {len(active)} running; {round(time.time()-start)}s',flush=True)
        elif not progressed:
            if pending:print(f'{len(pending)} blocked modules',flush=True)
            break
summary={'roots':a.modules,'closure':len(graph),'checked':len(done),'failed':failed,'blocked':sorted(pending),'seconds':time.time()-start,'jobs':a.jobs,'success':not failed and not pending}
(R/'audit/source-build-status.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='blocked'}),flush=True)
raise SystemExit(0 if summary['success'] else 1)
