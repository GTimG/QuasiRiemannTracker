#!/usr/bin/env python3
"""Build Liu's exact selected import closure with a bounded native scheduler.

Cached dependencies are logged with hashes; final independent proof replay is
a separate required step. This does not substitute a different theorem.
"""
import argparse
import concurrent.futures as cf
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--lean',type=Path,required=True)
    ap.add_argument('--lean-path-file',type=Path,required=True)
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--entry',default='RHZeroFreeExtension.CombinedPaperVerification')
    args=ap.parse_args()
    root=args.package.resolve(); lean=args.lean.resolve()
    out=root.parent/'native';build=out/'lib';logs=out/'logs'
    build.mkdir(parents=True,exist_ok=True);logs.mkdir(exist_ok=True)
    bases=[Path(x) for x in args.lean_path_file.read_text().strip().split(':')]
    env=dict(os.environ);env['LEAN_PATH']=':'.join(map(str,[build,*bases]))
    (out/'lean-path.txt').write_text(env['LEAN_PATH']+'\n')
    sources={};deps={};reused={};missing=[]
    def src(m):
        rel=Path(*m.split('.')).with_suffix('.lean')
        for base in (root,root/'vendor'):
            if (base/rel).exists():return base/rel,base
        return None
    def visit(m):
        if m in deps or m in reused:return
        source=src(m)
        cached=next((b/Path(*m.split('.')).with_suffix('.olean') for b in bases
                     if (b/Path(*m.split('.')).with_suffix('.olean')).exists()),None)
        if cached is not None and not (source and source[1]==root):
            reused[m]={'path':str(cached),'sha256':sha(cached)}
            if source:reused[m]['source_sha256']=sha(source[0])
            return
        if not source:
            # Core Lean modules can be supplied by the toolchain itself.
            core=lean.parent.parent/'lib/lean'/Path(*m.split('.')).with_suffix('.olean')
            if core.exists():reused[m]={'path':str(core),'sha256':sha(core)};return
            missing.append(m);return
        sources[m]=source
        imports=[]
        for line in source[0].read_text().splitlines():
            if re.match(r'^\s*(?:public\s+)?import\s+',line):
                line=re.sub(r'^\s*(?:public\s+)?import\s+','',line).split('--')[0]
                imports.extend(line.split())
        deps[m]=set(imports)
        for child in imports:visit(child)
    visit(args.entry)
    if missing:
        (out/'missing.json').write_text(json.dumps(sorted(set(missing)),indent=2)+'\n')
        raise SystemExit('Missing imports: '+', '.join(sorted(set(missing))))
    # Lean resolves a namespace at its first search-path root. The new OAI
    # modules therefore need a complete read-only artifact overlay, rather
    # than relying on a second OAI directory later in LEAN_PATH.
    overlay_prefixes={m.split('.')[0] for m in sources}
    for base in bases:
        for cached in base.rglob('*'):
            if not cached.is_file():
                continue
            rel=cached.relative_to(base)
            if rel.parts[0] not in overlay_prefixes:
                continue
            module='.'.join(str(rel).split('.olean',1)[0].split('/'))
            if module in sources:
                continue
            dest=build/rel
            if not dest.exists():
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.symlink_to(cached)
    print(f'Closure: {len(sources)} modules to compile; {len(reused)} cached boundaries',flush=True)
    pending=set(sources);done=set(reused);running={};records={};failed=[]
    def compile_one(m):
        source,base=sources[m]
        artifact=build/Path(*m.split('.')).with_suffix('.olean')
        artifact.parent.mkdir(parents=True,exist_ok=True)
        log=logs/(m+'.log')
        cmd=[str(lean),'-j1','-DautoImplicit=false','-DwarningAsError='+str(base==root).lower(),
             '-R',str(base),'-o',str(artifact),str(source)]
        start=time.time()
        with log.open('w') as f:
            r=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
        record={'returncode':r.returncode,'seconds':round(time.time()-start,3),
                'source':str(source),'source_sha256':sha(source),'log':str(log),'command':cmd}
        if r.returncode==0:record.update(artifact=str(artifact),artifact_sha256=sha(artifact))
        return record
    with cf.ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or running:
            for m in sorted(pending):
                if len(running)>=args.workers or failed:break
                if deps[m]<=done:
                    pending.remove(m);running[pool.submit(compile_one,m)]=m
            if not running:
                if pending and not failed:raise RuntimeError('Dependency cycle or unresolved imports: '+str(sorted(pending)))
                break
            completed,_=cf.wait(running,return_when=cf.FIRST_COMPLETED)
            for f in completed:
                m=running.pop(f);rec=f.result();records[m]=rec
                if rec['returncode']:
                    failed.append(m);print('FAIL '+m+'; '+rec['log'],flush=True)
                else:
                    done.add(m);print(f'PASS {len(records)}/{len(sources)} {m} ({rec["seconds"]}s)',flush=True)
    result={'status':'FAIL' if failed or pending else 'PASS','entry':args.entry,
            'lean':str(lean),'lean_sha256':sha(lean),'lean_path':env['LEAN_PATH'],
            'workers':args.workers,'compiled':records,'reused':reused,
            'failed':failed,'pending':sorted(pending)}
    (out/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
    raise SystemExit(1 if failed or pending else 0)

if __name__=='__main__':main()
