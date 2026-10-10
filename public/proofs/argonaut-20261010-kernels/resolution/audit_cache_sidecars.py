#!/usr/bin/env python3
"""Extract freshly authenticated official archives in scratch and compare live sidecars."""
import argparse,hashlib,json,subprocess
from pathlib import Path

def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--downloads',type=Path,required=True);ap.add_argument('--scratch',type=Path,required=True);ap.add_argument('--leantar',type=Path,required=True);ap.add_argument('--additional-inventory',type=Path,required=True);ap.add_argument('--jobs',type=int,default=4)
 ap.add_argument('--reuse-scratch',action='store_true')
 ap.add_argument('--key-source-audit',type=Path,required=True)
 a=ap.parse_args();work=a.work.resolve();scratch=a.scratch.resolve();scratch.mkdir(parents=True,exist_ok=a.reuse_scratch)
 downloads=json.loads(a.downloads.read_text())
 if downloads['status']!='PASS' or downloads['source']!='https://cache.mathlib.org/mathlib4-master/f/':raise SystemExit('Official fresh download audit required')
 for record in downloads['modules'].values():
  if sha(Path(record['file']))!=record['sha256']:raise SystemExit('Fresh downloaded archive changed')
 config=[{'file':r['file'],'base':str(scratch)} for r in downloads['modules'].values()]
 (work/'cache-extraction-config.json').write_text(json.dumps(config,indent=2)+'\n')
 command=[str(a.leantar.resolve()),'-x','-f','--jobs',str(a.jobs),'-j','-']
 with (work/'cache-extraction.log').open('w') as log:
  subprocess.run(command,input=json.dumps(config),text=True,stdout=log,stderr=subprocess.STDOUT,check=True)
 index={}
 for p in scratch.rglob('*.olean*'):
  if not p.name.endswith(('.olean','.olean.private','.olean.server')):continue
  part=str(p).split('/lib/lean/')[-1]
  module,_,suffix=part.partition('.olean');key=(module.replace('/','.'),suffix)
  if key in index and sha(index[key])!=sha(p):raise SystemExit('Conflicting extracted module parts')
  index[key]=p
 original=json.loads((work/'sidecar-inventory.json').read_text())
 targets={path:rec['sha256'] for path,rec in original['records'].items() if '/.lake/' in path}
 for path,digest in json.loads((work/'judge-input-inventory.json').read_text())['artifact_files'].items():
  if '/.lake/' in path and path.endswith('.olean'):targets[path]=digest
 for path,digest in json.loads(a.additional_inventory.read_text())['artifact_files'].items():
  if '/.lake/' in path and path.endswith(('.olean','.olean.private','.olean.server')):
   if path in targets and targets[path]!=digest:raise SystemExit('Conflicting recorded sidecar hashes')
   targets[path]=digest
 checked={}
 for path,expected in targets.items():
  part=path.split('/lib/lean/')[-1];module,_,suffix=part.partition('.olean');module=module.replace('/','.')
  fresh=index.get((module,suffix))
  if fresh is None or module not in downloads['modules']:raise SystemExit('Missing fresh sidecar: '+path)
  if sha(fresh)!=expected or sha(Path(path))!=expected:raise SystemExit('Official cache sidecar mismatch: '+path)
  checked[path]=expected
 keyaudit=json.loads(a.key_source_audit.read_text())
 if keyaudit['status']!='PASS':raise SystemExit('Source-derived cache-key audit did not pass')
 mains={p:h for p,h in checked.items() if p.endswith('.olean')}
 sidecars={p:h for p,h in checked.items() if not p.endswith('.olean')}
 result={'status':'PASS','scope':'All selected official dependency-cache main .olean objects and optional sidecars in the Liu and Argonaut inventories match fresh official master-cache archives, unpacked only into isolated scratch. No live artifacts changed.','source':'https://cache.mathlib.org/mathlib4-master/f/','download_manifest_sha256':sha(a.downloads),'cache_key_source_audit_sha256':sha(a.key_source_audit),'module_key_map_sha256':downloads['source_key_map_sha256'],'original_liu_sidecar_inventory_sha256':sha(work/'sidecar-inventory.json'),'argonaut_inventory_sha256':sha(a.additional_inventory),'leantar_sha256':sha(a.leantar),'command':command,'module_count':len(mains),'sidecar_count':len(sidecars),'main_olean_count':len(mains),'main_oleans':mains,'sidecars':sidecars}
 (work/'dependency-sidecar-audit.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','sidecars':len(sidecars),'main_oleans':len(mains),'official_archives':len(downloads['modules'])}))
if __name__=='__main__':main()
