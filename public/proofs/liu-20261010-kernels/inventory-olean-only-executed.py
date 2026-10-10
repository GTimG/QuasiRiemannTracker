#!/usr/bin/env python3
"""Bind the successful Liu build and its actual import closure for the judge."""
import argparse
import hashlib
import json
from pathlib import Path
import re

def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def imports(path):
    # Remove nested Lean block comments before reading import commands.
    text=path.read_text();out=[];depth=0;i=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text) if j<0 else j
        else:out.append(text[i]);i+=1
    result=[]
    for line in ''.join(out).splitlines():
        if not line.strip() or line.strip() in {'module','prelude'}:
            continue
        m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.*)$',line)
        if m:
            result.extend(m.group(1).split())
        else:
            # Lean imports are restricted to the module header. In particular,
            # JavaScript import text inside later widget strings is not Lean.
            break
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path,required=True)
    ap.add_argument('--source-root',type=Path,required=True)
    ap.add_argument('--dependencies',type=Path,required=True)
    args=ap.parse_args();work=args.work.resolve();root=args.source_root.resolve()
    verified=json.loads((work/'native-verification.json').read_text())
    if verified['status']!='PASS':raise SystemExit('Strict native verification must pass first')
    build=json.loads((work/'native/build-result.json').read_text())
    if build['status']!='PASS':raise SystemExit('Native build must pass first')
    package=work/'package';lean=Path(build['lean'])
    source_roots=[package,package/'vendor',*sorted(args.dependencies.resolve().iterdir()),
                  lean.parent.parent/'src/lean',lean.parent.parent/'src/lean/lake']
    artifact_roots=[Path(x) for x in build['lean_path'].split(':')]+[lean.parent.parent/'lib/lean']
    sources={};artifacts={};visited=set();core=[]
    def source_record(path):sources[str(path.relative_to(root))]=sha(path)
    def visit(module):
        if module in visited:return
        if module=='QRH' or module.startswith('QRH.'):
            raise SystemExit('Forbidden stronger-proof import: '+module)
        visited.add(module);rel=Path(*module.split('.'))
        obj=next((p/rel.with_suffix('.olean') for p in artifact_roots
                  if (p/rel.with_suffix('.olean')).exists()),None)
        if obj is None:raise SystemExit('Missing built artifact: '+module)
        artifacts[str(obj.resolve())]=sha(obj)
        source=next((p/rel.with_suffix('.lean') for p in source_roots
                     if (p/rel.with_suffix('.lean')).exists()),None)
        if source is None:
            if module.split('.')[0] in {'Init','Lean','Std'}:
                core.append(module);return
            raise SystemExit('Missing dependency source: '+module)
        source_record(source)
        for child in imports(source):visit(child)
    visit(build['entry'])
    manifest=json.loads((work/'source-manifest.json').read_text())
    for rec in manifest['files']:source_record(package/rec['path'])
    digest=hashlib.sha256(json.dumps(sources,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    result={'source_files':sources,'artifact_files':artifacts,
            'native_build_success':True,'candidate_imports_no_QRH':True,
            'source_manifest_sha256':digest,'source_root':str(root),
            'selected_module_count':len(visited),'modules':sorted(visited),
            'core_source_exemptions':core,'native_verification_sha256':sha(work/'native-verification.json')}
    dest=work/'judge-input-inventory.json';dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','source_root':str(root),'inventory':str(dest),
                      'source_count':len(sources),'artifact_count':len(artifacts),
                      'source_manifest_sha256':digest,'core_source_exemptions':len(core)},indent=2))

if __name__=='__main__':main()
