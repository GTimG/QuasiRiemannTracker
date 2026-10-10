#!/usr/bin/env python3
"""Reconstruct exact pinned source checkouts in this isolated project.
Run only with authorized network access. Never touches shared configuration.
"""
from pathlib import Path
import hashlib,json,subprocess,urllib.request,tarfile
R=Path(__file__).resolve().parents[1]
def run(*args):subprocess.run(args,check=True)
def checkout(url,rev,dest):
 if not (dest/'.git').exists():
  dest.mkdir(parents=True,exist_ok=True)
  run('git','init',str(dest));run('git','-C',str(dest),'remote','add','origin',url)
 else:
  actual=subprocess.check_output(['git','-C',str(dest),'remote','get-url','origin'],text=True).strip()
  if actual!=url:raise RuntimeError('Unexpected origin: '+str(dest))
 current=subprocess.run(['git','-C',str(dest),'rev-parse','HEAD'],capture_output=True,text=True)
 if current.returncode or current.stdout.strip()!=rev:
  if subprocess.check_output(['git','-C',str(dest),'status','--porcelain'],text=True).strip():raise RuntimeError('Refuse to replace modified checkout '+str(dest))
  run('git','-C',str(dest),'fetch','--depth','1','origin',rev)
  run('git','-C',str(dest),'checkout','--detach',rev)
checkout('https://github.com/openai/math.git','fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',R/'upstream/openai-math')
for p in json.loads((R/'audit/dependency-licenses.json').read_text()):
 if p['path'].startswith('formalization/.lake/packages/'):
  checkout(p['origin'],p['revision'],R/p['path'])
for p in json.loads((R/'audit/applied-patches.json').read_text()):
 patch=R/p['patch'];dest=R/'formalization/.lake/packages'/p['package']
 assert hashlib.sha256(patch.read_bytes()).hexdigest()==p['sha256']
 if subprocess.run(['git','-C',str(dest),'apply','--reverse','--check',str(patch)],capture_output=True).returncode:
  run('git','-C',str(dest),'apply','--check',str(patch));run('git','-C',str(dest),'apply',str(patch))
link=R/'formalization/OAI'
if not link.exists():link.symlink_to('../upstream/openai-math/lean/OAI',target_is_directory=True)
archive=R/'downloads/lean-4.34.1-linux.tar.zst';archive.parent.mkdir(exist_ok=True)
if not archive.exists():
 urllib.request.urlretrieve('https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst',archive)
assert hashlib.sha256(archive.read_bytes()).hexdigest()=='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'
if not (R/'toolchains/lean-4.34.1-linux/bin/lean').exists():
 (R/'toolchains').mkdir(exist_ok=True)
 run('tar','--use-compress-program=unzstd','-xf',str(archive),'-C',str(R/'toolchains'))
print('Pinned sources and local compiler ready; no theorem build performed.')
