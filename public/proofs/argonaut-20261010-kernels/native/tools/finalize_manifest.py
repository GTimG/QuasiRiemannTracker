"""Bind the unchanged source closure to the completed, actually used build."""
from pathlib import Path
import hashlib,json,shutil
BASE=Path(__file__).resolve().parent
EVIDENCE=BASE/'evidence'
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
build=json.loads((BASE/'native/build-result.json').read_text())
assert build['status']=='PASS'
path=EVIDENCE/'source-build-manifest.json'
initial=EVIDENCE/'initial-lake-source-build-manifest.json'
if not initial.exists():shutil.copyfile(path,initial)
manifest=json.loads(initial.read_text())
reused=json.loads((BASE/'native/reused-foundation.json').read_text())
for name,entry in manifest['modules'].items():
    if name in build['compiled']:
        record=build['compiled'][name]
        assert record['returncode']==0 and record['source_sha256']==entry['source_sha256']
        entry.update(mode='fresh-native-compile',artifacts=record['artifacts'],compiled_source=record['source'],compiled_source_sha256=record['source_sha256'])
    else:
        record=reused[name]
        assert record['original_source_sha256']==entry['source_sha256']
        entry.update(mode='audited-foundation-cache',artifacts=record['artifacts'],compiled_source=record['compiled_source'],compiled_source_sha256=record['compiled_source_sha256'],newline_normalization_only=record['newline_normalization_only'])
    assert entry['artifacts'],name
manifest.update(missing_artifact_count=0,missing_artifacts=[],
                native_lean_path=build['lean_path'].split(':'),
                native_build_status='PASS',fresh_module_count=len(build['compiled']),
                reused_module_count=len(reused),native_build_report_sha256=sha(BASE/'native/build-result.json'))
path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','modules':manifest['module_count'],'fresh':manifest['fresh_module_count'],'reused':len(reused),'manifest_sha256':sha(path)}))
