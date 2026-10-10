#!/usr/bin/env python3
"""Compare every selected optional toolchain sidecar to the pinned release archive."""
import argparse,hashlib,json,subprocess,tarfile
from pathlib import Path
PIN='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--archive',type=Path,required=True);ap.add_argument('--toolchain',type=Path,required=True)
 ap.add_argument('--additional-inventory',type=Path)
 a=ap.parse_args();work=a.work.resolve();tc=a.toolchain.resolve();archive=a.archive.resolve()
 if sha(archive)!=PIN:raise SystemExit('Toolchain release archive hash mismatch')
 records=json.loads((work/'sidecar-inventory.json').read_text())['records'];wanted={}
 for path,digest in json.loads((work/'judge-input-inventory.json').read_text())['artifact_files'].items():
  if path.endswith('.olean'):records[path]={'sha256':digest}
 if a.additional_inventory:
  for path,digest in json.loads(a.additional_inventory.read_text())['artifact_files'].items():
   if path.endswith(('.olean','.olean.private','.olean.server')):
    if path in records and records[path]['sha256']!=digest:raise SystemExit('Conflicting sidecar inventories')
    records[path]={'sha256':digest}
 implicit_path=work/'implicit-init-supplement.json'
 if implicit_path.exists():
  implicit=json.loads(implicit_path.read_text())
  for category in ['additional_source_files','additional_main_artifacts','additional_sidecars']:
   for path,digest in implicit[category].items():records[path]={'sha256':digest}
 for path,rec in records.items():
  p=Path(path)
  if p.is_relative_to(tc):wanted[str(Path(tc.name)/p.relative_to(tc))]=(p,rec)
 if not wanted:raise SystemExit('No selected toolchain sidecars')
 checked={};implementation=None
 process=subprocess.Popen(['zstd','-d','-c',str(archive)],stdout=subprocess.PIPE)
 with tarfile.open(fileobj=process.stdout,mode='r|') as tar:
  for member in tar:
   name=member.name.removeprefix('./')
   if name==str(Path(tc.name)/'src/lean/Lean/Environment.lean'):
    with tar.extractfile(member) as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
    source=tc/'src/lean/Lean/Environment.lean'
    if digest!=sha(source):raise SystemExit('Module loader source differs from pinned release')
    implementation={'path':str(source),'sha256':digest,'archive_member':member.name,'function':'Lean.readModuleDataPartsOfMod','line':2078}
   if name not in wanted:continue
   p,rec=wanted[name]
   if not member.isfile():raise SystemExit('Selected sidecar is not a regular archive member')
   with tar.extractfile(member) as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
   if digest!=rec['sha256'] or sha(p)!=digest:raise SystemExit('Release sidecar mismatch: '+str(p))
   checked[str(p)]={'archive_member':member.name,'sha256':digest,'bytes':member.size}
 process.stdout.close()
 if process.wait() or len(checked)!=len(wanted) or implementation is None:raise SystemExit('Archive incomplete or decompression failed')
 sidecar_count=sum(p.endswith(('.olean.private','.olean.server')) for p in checked)
 main_count=sum(p.endswith('.olean') for p in checked)
 result={'status':'PASS','archive_url':'https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst','archive_sha256':PIN,'sidecar_count':sidecar_count,'main_olean_count':main_count,'scope':'Byte-for-byte comparison of all selected Lean toolchain main objects, optional sidecars, and supplemental implicit-Init sources to the pinned release archive; live files were not modified.','module_loader_source':implementation,'files':checked}
 if implicit_path.exists():
  result['implicit_init_supplement_sha256']=sha(implicit_path)
  result['additional_implicit_init_sources']=len(implicit['additional_source_files'])
  result['additional_implicit_init_main_artifacts']=len(implicit['additional_main_artifacts'])
 (work/'toolchain-sidecar-audit.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','toolchain_sidecars':sidecar_count,'toolchain_main_objects':main_count,'implicit_Init_source_files':len(checked)-sidecar_count-main_count,'archive_sha256':PIN}))
if __name__=='__main__':main()
