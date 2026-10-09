"""Prepare task-owned checker tools on Linux verification worker; does not run submitted proofs."""
from pathlib import Path
import os, sys
import hashlib, json, os, socket, subprocess, urllib.request, time
assert sys.platform == 'linux', 'Linux with bubblewrap is required'
R=Path(os.environ['QRH_CHECKER_ROOT']).resolve()
P=Path(os.environ['QRH_PROOF_ROOT']).resolve()
R.mkdir(mode=0o700,exist_ok=True)
os.chmod(R,0o700)
for d in ['home','tools','downloads','logs','runs']:(R/d).mkdir(exist_ok=True)
env={'PATH':str(P/'toolchains/lean-4.34.1-linux/bin')+':/usr/bin:/bin','HOME':str(R/'home'),'TMPDIR':str(R),'LANG':'C.UTF-8','LEAN_NUM_THREADS':'4','GIT_CONFIG_NOSYSTEM':'1','GIT_TERMINAL_PROMPT':'0'}
def step(label,cmd,cwd=R):
 print(label,flush=True)
 (R/'status.json').write_text(json.dumps({'phase':label,'updated':time.time(),'status':'running'}))
 with (R/'logs'/f'{label}.log').open('w') as f:subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=1200)
def clone(name,url,rev):
 dest=R/'tools'/name
 if not dest.exists():
  step(name+'-init',['git','init',str(dest)])
  step(name+'-fetch',['git','-C',str(dest),'fetch','--depth','1',url,rev])
  step(name+'-checkout',['git','-C',str(dest),'checkout','--detach','FETCH_HEAD'])
 return dest
try:
 source=clone('lean4export','https://github.com/leanprover/lean4export.git','076e8e57707e813375e8f9da8bf989799ace9680')
 step('exporter-build',[str(P/'toolchains/lean-4.34.1-linux/bin/lake'),'build','lean4export'],source)
 url='https://api.github.com/repos/leanprover/lean4/releases/tags/v4.35.0-rc2'
 req=urllib.request.Request(url,headers={'User-Agent':'qrh-proof-verification'})
 release=json.load(urllib.request.urlopen(req,timeout=30))
 (R/'downloads/release.json').write_text(json.dumps(release,indent=2))
 asset=next(a for a in release['assets'] if a['name']=='lean-4.35.0-rc2-linux.tar.zst')
 archive=R/'downloads'/asset['name']
 (R/'status.json').write_text(json.dumps({'phase':'download-current-checkers','updated':time.time(),'status':'running'}))
 if not archive.exists():urllib.request.urlretrieve(asset['browser_download_url'],archive)
 digest=hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()
 if asset.get('digest'):assert asset['digest']=='sha256:'+digest
 else:raise RuntimeError('No official release digest; preserve download for independent validation')
 step('checker-toolchain-extract',['tar','--zstd','-xf',str(archive),'--no-same-owner','-C',str(R/'tools')])
 pins={'lean_proof_toolchain':'v4.34.1','exporter_commit':'076e8e57707e813375e8f9da8bf989799ace9680','checker_toolchain':'v4.35.0-rc2','checker_release_sha256':digest,'palomar_submission_commit':'d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44','host':'verification-worker','status':'tools-ready; export compatibility not yet established'}
 (R/'pins.json').write_text(json.dumps(pins,indent=2))
 (R/'status.json').write_text(json.dumps({'phase':'tools-ready','updated':time.time(),'status':'complete'}))
 print(json.dumps(pins),flush=True)
except Exception as e:
 (R/'status.json').write_text(json.dumps({'phase':'preparation','status':'failed','error':str(e),'updated':time.time()}));raise
