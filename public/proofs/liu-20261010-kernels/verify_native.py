#!/usr/bin/env python3
"""Strictly replay Liu's published 22-target correspondence entry."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import runpy
import subprocess

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--workers',type=int,default=8)
    args=ap.parse_args();work=args.work.resolve();package=work/'package';native=work/'native'
    build=json.loads((native/'build-result.json').read_text())
    if build['status']!='PASS':raise SystemExit('Native build must pass before replay')
    if sha(Path(build['lean']))!=build['lean_sha256']:
        raise SystemExit('Native compiler binary changed')
    for rec in build['compiled'].values():
        if sha(Path(rec['artifact']))!=rec['artifact_sha256']:
            raise SystemExit('Compiled artifact changed: '+rec['artifact'])
    for rec in build['reused'].values():
        if sha(Path(rec['path']))!=rec['sha256']:
            raise SystemExit('Cached boundary changed: '+rec['path'])
    manifest=json.loads((work/'source-manifest.json').read_text())
    for x in manifest['files']:
        if sha(package/x['path'])!=x['sha256']:raise SystemExit('Source changed: '+x['path'])
    # Only read the original verifier's declared target inventory.
    expected=runpy.run_path(str(package/'verify.py'))['EXPECTED']
    env=dict(os.environ);env['LEAN_PATH']=build['lean_path']
    cmd=[build['lean'],'--trust=0','-j'+str(args.workers),'-DautoImplicit=false',
         '-DwarningAsError=true','RHZeroFreeExtension/CombinedPaperVerification.lean']
    log=native/'kernel.log'
    with log.open('w') as f:
        result=subprocess.run(cmd,cwd=package,env=env,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text()
    if result.returncode or re.search(r'error:|sorryAx|declaration uses .sorry.',text):
        raise SystemExit('Strict native replay failed; inspect '+str(log))
    allowed={'propext','Classical.choice','Quot.sound'}
    axioms={}
    for name,items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S):
        names={x.strip() for x in items.split(',') if x.strip()}
        if not names<=allowed:raise SystemExit('Nonstandard axioms in '+name)
        axioms[name]=sorted(names)
    for name in expected:
        if 'CombinedPaper.'+name not in axioms:raise SystemExit('Missing axiom report: '+name)
    for x in manifest['files']:
        if sha(package/x['path'])!=x['sha256']:raise SystemExit('Source changed during replay: '+x['path'])
    record={'status':'PASS','scope':'Exact original Liu proofs, restored layout; strict native replay of all 22 published targets. Independent kernel/comparator verification is separate.',
            'source_commit':manifest['liu_commit'],'source_inputs':'source-manifest.json',
            'reconstructed_package_manifest_sha256':sha(work/'source-manifest.json'),
            'native_build_report':'native/build-result.json','native_build_sha256':sha(native/'build-result.json'),
            'command':cmd,'lean_path':build['lean_path'],'package_root':str(package),
            'entry_module':build['entry'],'target_count':len(expected),'axioms':axioms,
            'kernel_log':'native/kernel.log','kernel_log_sha256':sha(log),
            'source_provenance':'source-provenance.json','reproduction_script':'reproduce.py',
            'entry_source_sha256':sha(package/'RHZeroFreeExtension/CombinedPaperVerification.lean'),
            'entry_artifact_sha256':sha(native/'lib/RHZeroFreeExtension/CombinedPaperVerification.olean')}
    (work/'native-verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
