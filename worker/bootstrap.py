"""Trusted ONLINE image construction. Never used to elaborate a submission."""
import json, pathlib, shutil, subprocess, urllib.request, hashlib, os
ROOT=pathlib.Path('/opt/qrh'); PINS=json.loads((ROOT/'verifier/pins.json').read_text())
def run(*args,cwd=None): subprocess.run(args,cwd=cwd,check=True)
def clone(url,rev,dest):
    run('git','clone','--filter=blob:none','--no-checkout',url,str(dest))
    run('git','checkout','--detach',rev,cwd=dest)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=dest,text=True).strip()==rev
project=pathlib.Path('/opt/project');project.mkdir()
source=pathlib.Path('/tmp/openai-math');clone(PINS['openai_math']['url'],PINS['openai_math']['commit'],source)
assert hashlib.sha256((source/'lean/ComparatorChallenges/DirichletSevenEighths.lean').read_bytes()).hexdigest()==PINS['challenge_sha256']
# Copy only the baseline's OAI dependency closure. No rewriting of mathematical sources.
todo=['OAI.NumberTheory.DirichletL.Nonvanishing'];seen=set()
while todo:
    mod=todo.pop()
    if mod in seen: continue
    seen.add(mod);rel=pathlib.Path(mod.replace('.','/')+'.lean');src=source/'lean'/rel;dst=project/rel
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
    for line in src.read_text().splitlines():
        if line.startswith('import '): todo.extend(m for m in line[7:].split() if m.startswith('OAI.'))
shutil.copy(ROOT/'worker/lakefile.lean',project/'lakefile.lean')
shutil.copy(ROOT/'worker/lake-manifest.json',project/'lake-manifest.json')
(project/'lean-toolchain').write_text(PINS['lean']+'\n')
packages=project/'.lake/packages';packages.mkdir(parents=True)
manifest=json.loads((project/'lake-manifest.json').read_text())
for p in manifest['packages']:
    name=p['name'].strip('«»');dest=packages/name
    clone(p['url'],p['rev'],dest)
    patch=source/'lean/patches'/f'{name}-lean4341.patch'
    if name in ('rellich-kondrachov','PrimeNumberTheoremAnd'):
        assert patch.is_file();run('git','apply',str(patch),cwd=dest)
# Download the cache from the trusted pinned Mathlib build, before any candidate exists.
# Cache provenance is part of the image-build TCB; freeze the completed image digest.
run('lake','exe','cache','get',cwd=project)
run('lake','build','OAI.NumberTheory.DirichletL.Nonvanishing',cwd=project)
# Pre-build the complete Mathlib import that the unmodified canonical template requires.
(project/'Challenge.lean').write_text((ROOT/'verifier/upstream-challenge.lean').read_text())
run('lake','build','Challenge',cwd=project)
(project/'Challenge.lean').unlink()
# Clear challenge artifacts. Candidate and wrapper have never been compiled in this image.
for p in (project/'.lake/build').rglob('Challenge.*'): p.unlink()
print('Trusted baseline closure built:',len(seen),'modules')
