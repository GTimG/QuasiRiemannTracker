"""Inventory the exact native import closure, sources, and resulting artifacts."""
from pathlib import Path
import hashlib,json,re,sys
BASE=Path(__file__).resolve().parent
PROJECT=BASE/'project'
TOOLCHAIN=BASE.parents[1]/'compressed/toolchains/lean-4.34.1-linux'
EVIDENCE=BASE/'evidence'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    out=[];i=depth=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='--':
            k=s.find('\n',i);i=len(s) if k<0 else k
        else:out.append(s[i]);i+=1
    return ''.join(out)
roots=[PROJECT]
config=PROJECT/'lakefile.task18-reviewed-overlay-v1.lean'
roots += [PROJECT/x for x in re.findall(r'srcDir\s*:=\s*"([^"]+)"',config.read_text())]
for package in (PROJECT/'.lake/packages').iterdir():
    roots.append(package)
    for conf in [package/'lakefile.lean',package/'lakefile.toml']:
        if conf.exists():
            roots += [package/x for x in re.findall(r'srcDir\s*(?::=|=)\s*"([^"]+)"',conf.read_text())]
roots += [TOOLCHAIN/'src/lean', TOOLCHAIN/'src/lean/lake']
roots=list(dict.fromkeys(x.resolve() for x in roots))
native_paths=EVIDENCE.joinpath('native-lean-path.txt').read_text().strip().split(':')
artifact_roots=[Path(x) for x in native_paths]+[TOOLCHAIN/'lib/lean']
def find(module):
    rel=Path(*module.split('.')).with_suffix('.lean')
    matches=[r/rel for r in roots if (r/rel).is_file()]
    if not matches:raise RuntimeError('Missing source: '+module)
    if len(matches)>1 and len({sha(x) for x in matches})>1:
        raise RuntimeError('Ambiguous source: '+module+' '+str(matches))
    return matches[0]
old_path=EVIDENCE/'source-build-manifest.json'
old_graph=json.loads(old_path.read_text())['modules'] if old_path.exists() else {}
graph={};todo=['PerturbedBoundaryMain']
while todo:
    module=todo.pop()
    if module in graph:continue
    p=find(module);source=p.read_bytes();source_hash=hashlib.sha256(source).hexdigest()
    previous=old_graph.get(module,{})
    if previous.get('source_sha256')==source_hash and previous.get('source')==str(p):
        imports=previous['imports']
    else:
        text=clean(source.decode())
        imports=[]
        if not re.search(r'^\s*prelude\s*$',text,re.M) and module!='Init':imports=['Init']
        for line in text.splitlines():
            match=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
            if match:imports += [x for x in match.group(1).split() if x!='all']
            elif line.strip() and line.strip() not in ['prelude','module']:break
    imports=list(dict.fromkeys(imports));rel=Path(*module.split('.')).with_suffix('.olean')
    artifacts={}
    for root in artifact_roots:
        out=root/rel
        if out.exists():
            for suffix in ['', '.private', '.server']:
                q=Path(str(out)+suffix)
                if q.exists():artifacts[str(q)]=sha(q)
            break
    graph[module]={'source':str(p),'source_sha256':source_hash,'imports':imports,'artifacts':artifacts}
    todo += imports
missing=[m for m,v in graph.items() if not v['artifacts']]
result={'schema':1,'candidate':'Argonaut v0.1.8','root_module':'PerturbedBoundaryMain','module_count':len(graph),'missing_artifact_count':len(missing),'missing_artifacts':missing,'native_lean_path':native_paths,'compiler':{'path':str(TOOLCHAIN/'bin/lean'),'sha256':sha(TOOLCHAIN/'bin/lean')},'modules':graph}
(EVIDENCE/'source-build-manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(graph),'missing_artifacts':len(missing),'manifest_sha256':sha(EVIDENCE/'source-build-manifest.json')}))
if '--require-complete' in sys.argv:assert not missing,missing
source_files={}
artifact_files={}
for m,entry in graph.items():
    p=Path(entry['source'])
    if p.is_relative_to(PROJECT):
        source_files[str(p.relative_to(PROJECT))]=entry['source_sha256']
        artifact_files.update(entry['artifacts'])
for p in [config, PROJECT/'lake-manifest.json', PROJECT/'lean-toolchain']:
    if p.exists():source_files[str(p.relative_to(PROJECT))]=sha(p)
inventory={'source_root':str(PROJECT),'source_files':source_files,
           'artifact_files':artifact_files,
           'source_manifest_sha256':hashlib.sha256(json.dumps(source_files,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
           'native_build_success':'--native-pass' in sys.argv and not missing,
           'candidate_imports_no_QRH':not any(m=='QRH' or m.startswith('QRH.') for m in graph),
           'module_count':len(graph),'compiler':result['compiler']}
(EVIDENCE/'operator-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
