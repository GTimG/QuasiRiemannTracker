#!/usr/bin/env python3
"""Recheck frozen source bytes and native targets after the documented full build."""
from pathlib import Path
import hashlib,json,os,re,subprocess
R=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads((R/'source-inputs.json').read_text())
for name,digest in inputs['files'].items():
    assert sha(R/'compressed/formalization'/name)==digest,name
old=json.loads((R/'verification/native-final-audit.json').read_text())
for name,digest in old['protected_files_unchanged'].items():
    assert sha(R/'compressed/formalization/QRH'/name)==digest,name
build=R/'compressed/build/public-verification';build.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(build)+':'+(R/'compressed/audit/local-lean-path.txt').read_text().strip()
for name in ['Solution','NativeAudit']:
    p=subprocess.run([str(R/'compressed/toolchains/lean-4.34.1-linux/bin/lean'),'-j','2',
      '-o',str(build/(name+'.olean')),str(R/'verification/src'/(name+'.lean'))],
      cwd=R/'verification/src',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (build/(name+'.log')).write_text(p.stdout)
    assert p.returncode==0 and 'declaration uses `sorry`' not in p.stdout,name
audit=(build/'NativeAudit.log').read_text()
groups=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.S)
found={name:sorted(x.strip() for x in body.split(',') if x.strip()) for name,body in groups}
expected=re.findall(r'^#print axioms (\S+)',(R/'verification/src/NativeAudit.lean').read_text(),re.M)
assert set(found)==set(expected)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in found.values())
print(json.dumps({'status':'PASS','scope':'fresh native target audit only','axioms':found},indent=2))
