#!/usr/bin/env python3
"""Supplement the historical explicit-import inventory with Lean's implicit Init closure."""
import argparse,hashlib,json
from pathlib import Path
from inventory import imports

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--toolchain',type=Path,required=True)
 a=ap.parse_args();work=a.work.resolve();tc=a.toolchain.resolve();original=json.loads((work/'judge-input-inventory.json').read_text());root=Path(original['source_root'])
 visited=set();sources={};artifacts={};sidecars={}
 def visit(m):
  if m in visited:return
  visited.add(m);rel=Path(*m.split('.'));s=tc/'src/lean'/rel.with_suffix('.lean');o=tc/'lib/lean'/rel.with_suffix('.olean')
  if not s.is_file() or not o.is_file():raise SystemExit('Missing compiler Init dependency: '+m)
  if str(s.relative_to(root)) not in original['source_files']:sources[str(s)]=sha(s)
  if str(o) not in original['artifact_files']:artifacts[str(o)]=sha(o)
  for suffix in ['.private','.server']:
   p=Path(str(o)+suffix)
   if p.exists() and str(o) not in original['artifact_files']:sidecars[str(p)]=sha(p)
  for dep in imports(s):visit(dep)
 visit('Init')
 result={'status':'ENUMERATED_ARCHIVE_AUTHENTICATION_REQUIRED','original_inventory_sha256':sha(work/'judge-input-inventory.json'),'scope':'Historical inventory followed explicit imports only. Lean implicitly imports Init for every non-prelude module. These compiler-provided source/main/sidecar files supplement that omission; no proof source or compiled artifact changed.','implicit_init_closure_modules':len(visited),'additional_source_files':sources,'additional_main_artifacts':artifacts,'additional_sidecars':sidecars}
 (work/'implicit-init-supplement.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'Init_closure_modules':len(visited),'additional_sources':len(sources),'additional_main_artifacts':len(artifacts),'additional_sidecars':len(sidecars)}))
if __name__=='__main__':main()
