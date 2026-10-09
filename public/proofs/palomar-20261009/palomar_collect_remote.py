"""Return compact, hashed evidence only after both local proof judges pass."""
from pathlib import Path
import os, sys
import base64,hashlib,json,datetime,socket
assert sys.platform == 'linux', 'Linux with bubblewrap is required'
R=Path(os.environ['QRH_CHECKER_ROOT']).resolve();P=Path(os.environ['QRH_PROOF_ROOT']).resolve()
files={}
for name in ['qrh','openai']:
 w=R/'runs'/name
 result=json.loads((w/'result.json').read_text())
 assert result['status']=='PASS'
 assert result['kernels']==['Lean default','nanoda','con-ron']
 assert set(result['allowed_axioms'])=={'propext','Classical.choice','Quot.sound'}
 for rel,digest in result['artifacts'].items():
  with (w/rel).open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==digest,rel
 for rel in ['result.json','tool-pins.json','comparator.json','judge.log','Challenge-compile.log','Solution-compile.log','Challenge-export.log','Solution-export.log','src/Challenge.lean','src/Solution.lean']:
  data=(w/rel).read_bytes();assert len(data)<10*1024**2
  files[name+'/'+rel]=data
for rel in ['check-status.json','baseline-check-status.json','pins.json','baseline-build/status.json','baseline-build/graph.json']:
 files[rel]=(R/rel).read_bytes()
summary={'collected_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'host':'verification-worker','palomar_registration':False,'files':{n:hashlib.sha256(data).hexdigest() for n,data in files.items()}}
files['collection.json']=(json.dumps(summary,indent=2)+'\n').encode()
# Retain small durable evidence outside the temporary filesystem, without editing the accepted proof snapshot.
archive=P/'palomar-checks-20261009';archive.mkdir(exist_ok=True)
for name,data in files.items():
 dest=archive/name;dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert dest.read_bytes()==data or name=='collection.json',name
 dest.write_bytes(data)
print(json.dumps({'files':{n:base64.b64encode(data).decode() for n,data in files.items()}}))
