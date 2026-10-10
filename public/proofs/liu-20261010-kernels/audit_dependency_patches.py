#!/usr/bin/env python3
"""Reconstruct selected compatibility inputs from exact git objects + upstream patches."""
import argparse,hashlib,json,subprocess,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--dependencies',type=Path,required=True)
 a=ap.parse_args();work=a.work.resolve();deps=a.dependencies.resolve()
 inv=json.loads((work/'judge-input-inventory.json').read_text());root=Path(inv['source_root'])
 pins=json.loads((work/'package/lake-manifest.json').read_text())['packages'];out=[]
 for name in ['PrimeNumberTheoremAnd','rellich-kondrachov']:
  spec=next(p for p in pins if p['name'].strip('«»')==name);repo=deps/name
  patch=work/'package/upstream'/(name+'-lean4341.patch')
  with tempfile.TemporaryDirectory(prefix='liu-patch-audit-') as tmp:
   dest=Path(tmp)
   archive=subprocess.Popen(['git','-C',str(repo),'archive',spec['rev']],stdout=subprocess.PIPE)
   subprocess.run(['tar','-x','-C',str(dest)],stdin=archive.stdout,check=True)
   archive.stdout.close()
   if archive.wait():raise SystemExit('git archive failed')
   subprocess.run(['git','-C',str(dest),'apply',str(patch)],check=True)
   prefix=str(repo.relative_to(root))+'/'
   files={}
   for path,digest in inv['source_files'].items():
    if path.startswith(prefix):
     rel=path[len(prefix):]
     if sha(dest/rel)!=digest:raise SystemExit('Published dependency patch mismatch: '+path)
     files[rel]=digest
   out.append({'package':name,'revision':spec['rev'],'patch_sha256':sha(patch),'selected_files':files})
 result={'status':'PASS','scope':'All selected sources in the two compatibility-patched packages equal exact pinned git source plus the author-supplied patch. Unselected dirty working-tree files are not proof inputs.','packages':out}
 (work/'dependency-patch-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
