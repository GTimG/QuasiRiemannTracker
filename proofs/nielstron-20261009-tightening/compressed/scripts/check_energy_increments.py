#!/usr/bin/env python3
"""One Lean worker: check explicit drafts once their source-built imports exist.
Only compiled, allowed-axiom-audited files are promoted into formalization/QRH.
This never edits upstream sources or frozen targets and is not a model runner.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,sys

R=Path(__file__).resolve().parents[1]
items=json.loads((R/(sys.argv[1] if len(sys.argv)>1 else 'audit/energy-extension-drafts.json')).read_text())
lean=R/'toolchains/lean-4.34.1-linux/bin/lean'
env=os.environ.copy();env['LEAN_PATH']=str(R/'build/source')
checked=[];allowed={'propext','Classical.choice','Quot.sound'}
def known():
    path=R/'audit/checked-energy-increments.jsonl'
    records={}
    if path.exists():
        for line in path.read_text().splitlines():
            try:record=json.loads(line)
            except json.JSONDecodeError:continue # another one-worker queue may be appending
            src=R/record['source']
            assert src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==record['sha256'],src
            records[record['module']]=record
    return records
for item in items:
    source=R/item['source'];module=item['module']
    dest=R/'formalization'/Path(*module.split('.')).with_suffix('.lean')
    if module in known():
        checked.append(module);print('REUSE CHECKED',module,flush=True);continue
    imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
    while True:
        missing=[]
        already=known()
        for imp in imports:
            out=R/'build/source'/Path(*imp.split('.')).with_suffix('.olean')
            if not out.exists() or not (out.with_suffix('.source-key').exists() or imp in checked or imp in already):
                missing.append(imp)
        if not missing:break
        print('WAIT',module,':',', '.join(missing),flush=True)
        time.sleep(20)
    out=R/'build/source'/Path(*module.split('.')).with_suffix('.olean')
    out.parent.mkdir(parents=True,exist_ok=True)
    log=R/'logs'/('increment-'+module+'.log')
    cmd=[str(lean),'-j1','-DautoImplicit=false','-R',str(R/'research/drafts'),'-o',str(out),str(source)]
    with log.open('w') as f:
        f.write(json.dumps({'command':cmd,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()})+'\n');f.flush()
        rc=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
    if rc:raise SystemExit('FAIL '+module+'; '+str(log))
    declarations=['OAI.'+item['namespace']+'.'+n for n in item['theorems']]
    audit=R/'audit'/('Increment'+module.rsplit('.',1)[1]+'Axioms.lean')
    audit.write_text('import '+module+'\n'+''.join('#print axioms '+n+'\n' for n in declarations))
    axlog=R/'logs'/('increment-'+module+'-axioms.log')
    with axlog.open('w') as f:
        rc=subprocess.run([str(lean),'-j1',str(audit)],env=env,stdout=f,stderr=subprocess.STDOUT).returncode
    s=axlog.read_text()
    groups=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)
    groups += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",s)]
    assert rc==0 and {n for n,_ in groups}==set(declarations),(module,rc,s)
    assert all({a.strip() for a in ax.split(',') if a.strip()}<=allowed for _,ax in groups),s
    assert not dest.exists(),dest
    dest.parent.mkdir(parents=True,exist_ok=True);source.rename(dest)
    checked.append(module)
    record={'module':module,'source':str(dest.relative_to(R)),'sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'declarations':declarations,'axioms_allowed_only':True}
    with (R/'audit/checked-energy-increments.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
    with (R/'PROGRESS.txt').open('a') as f:
        f.write('\nChecked analytic integration increment: '+module+'; '+str(len(declarations))+' extended declarations compile and have allowed-only transitive axioms. Source '+str(dest.relative_to(R))+'. Original imported objects unchanged; complete manuscript packaging and final targets still pending.\n')
    print('CHECKED',module,flush=True)
print('All requested increments checked; this does not complete the analytic theorem.',flush=True)
