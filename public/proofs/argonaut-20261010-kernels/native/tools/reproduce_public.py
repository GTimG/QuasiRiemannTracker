"""Rehearse the published compact bundle in a new, independent source tree."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib,json,os,stat,subprocess,sys,time,zipfile

BASE=Path(__file__).resolve().parent
REPO=BASE.parents[1]
WORK=BASE/'reproduction-check'
WORK.mkdir(exist_ok=True)
ARCHIVE=BASE/'argonaut-v0.1.8-reviewed-source.zip'
EXPECTED='01d24d12c4645ff334aa4bf3656cb3154cc5080a380127a564503b8a84e13abf'
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
assert sha(ARCHIVE)==EXPECTED
BUNDLE=WORK/'bundle'
BUNDLE.mkdir(exist_ok=False)
with zipfile.ZipFile(ARCHIVE) as z:
    entries=z.infolist()
    assert sum(x.file_size for x in entries)<=100*1024*1024
    for e in entries:
        p=PurePosixPath(e.filename)
        assert not p.is_absolute() and '..' not in p.parts and '\\' not in e.filename
        assert e.file_size<=10*1024*1024
        assert stat.S_IFMT(e.external_attr>>16)==stat.S_IFREG
        out=BUNDLE.joinpath(*p.parts)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(z.read(e))
PUB=BUNDLE/'argonaut-v0.1.8-reviewed-source'
ORIGINAL=WORK/'original-from-public'
subprocess.run([sys.executable,str(PUB/'reproducibility/fetch_original.py'),'--output',str(ORIGINAL)],check=True)
PACKET=ORIGINAL/'Lean_Proof'
for name in ['PINS.json','SOURCE-MANIFEST.json','DEPENDENCY-LICENSES.json']:
    assert sha(PACKET/'provenance'/name)==sha(PUB/'provenance'/name)
assert sha(PACKET/'reproducibility/reconstruct.py')==sha(PUB/'reproducibility/upstream_reconstruct.py')
PINS=json.loads((PACKET/'provenance/PINS.json').read_text())
PROJECT=WORK/'project'
PROJECT.mkdir(exist_ok=False)
def git(args,**kwargs):
    return subprocess.run(['git','-c','pack.threads=1','-c','index.threads=1',*args],check=True,**kwargs)
def clone(pin):
    destination=PROJECT/'.lake/packages'/pin['name']
    cached=BASE/'project/.lake/packages'/pin['name']
    log=WORK/('clone-'+pin['name']+'.log')
    destination.parent.mkdir(parents=True,exist_ok=True)
    with log.open('w') as f:
        git(['clone','--shared','--no-checkout',str(cached),str(destination)],stdout=f,stderr=f)
        git(['-C',str(destination),'remote','set-url','origin',pin['url']],stdout=f,stderr=f)
        git(['-C',str(destination),'config','core.autocrlf','false'],stdout=f,stderr=f)
        git(['-C',str(destination),'checkout','--detach',pin['revision']],stdout=f,stderr=f)
    actual=git(['-C',str(destination),'rev-parse','HEAD'],capture_output=True,text=True).stdout.strip()
    origin=git(['-C',str(destination),'remote','get-url','origin'],capture_output=True,text=True).stdout.strip()
    assert actual==pin['revision'] and origin==pin['url']
    return {'name':pin['name'],'revision':actual,'origin':origin,'git_object_reuse_only':True}
with ThreadPoolExecutor(max_workers=8) as pool:
    dependencies=list(pool.map(clone,PINS['locked_dependencies']))
subprocess.run([sys.executable,str(PACKET/'reproducibility/reconstruct.py'),'--project',str(PROJECT),'--apply-overlay'],check=True)
manifest=json.loads((PACKET/'provenance/SOURCE-MANIFEST.json').read_text())
for entry in manifest['files']:
    rel=Path(entry['path'])
    if rel.parts[0]=='project':p=PROJECT/Path(*rel.parts[1:])
    elif rel.parts[0]=='dependencies':p=PROJECT/'.lake/packages'/Path(*rel.parts[1:])
    else:raise RuntimeError(entry['path'])
    assert sha(p)==entry['sha256'],p
compiled=json.loads((BASE/'native/build-result.json').read_text())
for m,e in compiled['compiled'].items():
    p=PROJECT/Path(e['source']).relative_to(BASE/'project')
    assert sha(p)==e['source_sha256'],m
for entry in json.loads((PUB/'source-provenance.json').read_text())['included_original_project_files']:
    a=PUB/entry['path'];b=PROJECT/Path(*Path(entry['upstream_overlay_path']).parts[1:])
    assert sha(a)==sha(b)==entry['sha256']

# Audits are freshly read from reconstructed sources. Imported native artifacts
# are authenticated against the completed local build, not rebuilt or modified.
env=dict(os.environ);env['LEAN_PATH']=(BASE/'native/lean-path.txt').read_text().strip()
lean=REPO/'compressed/toolchains/lean-4.34.1-linux/bin/lean'
audit_results=[]
for name in ['PerturbedBoundaryMainCurrentFullAuditV2.lean','HUBBLE-PrincipalV2-TerminalAudit.lean']:
    log=WORK/(name+'.log');source=PROJECT/'audits'/name
    command=[str(lean),'-j1','-DautoImplicit=false','-R',str(PROJECT),str(source)]
    with log.open('w') as out:
        process=subprocess.run(command,cwd=PROJECT,env=env,stdout=out,stderr=subprocess.STDOUT)
    assert process.returncode==0,name
    reference=BASE/'evidence'/(name+'.log')
    assert log.read_bytes()==reference.read_bytes(),name
    audit_results.append({'source':str(source.relative_to(WORK)),'source_sha256':sha(source),
                          'command':command,'log':str(log.relative_to(WORK)),'log_sha256':sha(log),
                          'returncode':process.returncode,'output_byte_equal_to_original_native_audit':True})
result={'status':'PASS','verified_utc':datetime.now(timezone.utc).isoformat(),
        'compact_archive_sha256':sha(ARCHIVE),'compact_file_count':len(entries),
        'downloaded_original_archive_sha256':json.loads((PUB/'source-provenance.json').read_text())['archive_sha256'],
        'original_overlay_files_rehashed':len(manifest['files']),
        'fresh_compiled_source_files_byte_equal':len(compiled['compiled']),
        'dependency_revisions':dependencies,'fresh_source_audits':audit_results,
        'native_artifact_policy':'Existing authenticated artifacts imported read-only; original proof and protected final result unchanged.',
        'stronger_local_result_used':False}
(BASE/'evidence/public-reconstruction-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','dependencies':len(dependencies),'reconstructed_files':len(manifest['files']),'fresh_source_audits':len(audit_results)}))
