#!/usr/bin/env python3
"""Authenticate the additive algebraic source snapshot and native receipt.

This does not execute Lean or assert independent kernel acceptance. Run the
separate check-algebraic-kernels.mjs gate for that dossier and catalogue status.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

sys.dont_write_bytecode = True
ID='nielstron-algebraic-20261009'
THETA='874957019420098946128603850561452983/1000000000000000000000000000000000000'
TARGETS=['QRHPalomar.'+n for n in ('allDirichlet','zeta','allHecke','allDirichletExact',
                                  'zetaExact','allHeckeExact','existsUniqueRoot')]

def read(path):return json.loads(path.read_text())
def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--binding',type=Path)
    args=parser.parse_args();root=args.root.resolve()
    sys.path.insert(0,str(root/'scripts'))
    from publication_policy import approved_files,check_archive,check_content
    binding=read(args.binding or root/'core/algebraic-kernel-pins.json')
    assert binding['id']==ID and binding['theta']==THETA
    proof=root/'proofs'/ID;public=root/'public/proofs'/ID
    names=approved_files(proof)
    manifest=read(root/'proofs'/(ID+'.sha256.json'))
    assert set(names)==set(manifest)
    for name,digest in manifest.items():assert sha(proof/name)==digest,name
    assert not public.is_symlink()
    assert all(p.is_file() and not p.is_symlink() for p in public.iterdir())
    collection=read(public/'collection.json')
    assert collection['status']=='verification-pending','Historical native snapshot must retain pending status'
    assert set(collection['files'])=={p.name for p in public.iterdir() if p.name!='collection.json'}
    for name,digest in collection['files'].items():
        assert Path(name).name==name and sha(public/name)==digest,name
        if name!='source-public.tar.gz':check_content(name,(public/name).read_bytes())
    for target,source in collection['snapshot_exports'].items():
        assert source in manifest and (public/target).read_bytes()==(proof/source).read_bytes(),target
    assert read(public/'source-sha256.json')==manifest
    archive=public/'source-public.tar.gz';check_archive(archive,proof,manifest)
    assert sha(archive)==binding['source_archive_sha256']
    expected,name=(public/'SHA256SUMS.txt').read_text().strip().split('  ')
    assert name==archive.name and expected==sha(archive)
    inputs=read(proof/'source-inputs.json')
    calculated=hashlib.sha256(json.dumps(inputs['files'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
    assert calculated==inputs['manifest_sha256']==binding['source_manifest_sha256']
    assert len(inputs['files'])==binding['source_files']
    for name,digest in inputs['files'].items():
        assert manifest['compressed/formalization/'+name]==digest,name
    native=read(proof/'verification/native-final-audit.json')
    assert native['status']=='PASS' and native['declarations']==TARGETS
    assert len(native['axioms'])>=24 and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in native['axioms'].values())
    changes={x['path']:x for x in read(proof/'publication-transformations.json')['changes']}
    for name,item in changes.items():
        assert manifest[name]==item['published_sha256'],name
    for kind in ('files','logs'):
        for name,original in native[kind].items():
            relative='verification/'+name
            assert changes.get(relative,{}).get('original_sha256',manifest[relative])==original,relative
    for name,digest in native['protected_files_unchanged'].items():
        relative='compressed/formalization/QRH/'+name
        assert manifest[relative]==digest
        assert sha(root/'proofs/nielstron-20261009-tightening'/relative)==digest
    assert len(native['protected_files_unchanged'])==7
    counts=read(proof/'compressed/audit/token-counts.json')['qrh_package']
    assert sum(p['after_tokens'] for p in counts['files'])==counts['after_tokens']
    for item in counts['files']:
        assert item['after_sha256']==manifest.get('compressed/formalization/'+item['path']),item['path']
    summary=read(proof/'result.json')
    assert summary['status']=='verification-pending' and summary['native_status']=='PASS'
    assert summary['catalogue_rational_upper_bound']==THETA and summary['declarations']==TARGETS
    assert summary['source_manifest_sha256']==binding['source_manifest_sha256']
    assert summary['qrh_package']['after_tokens']==counts['after_tokens']
    print(f'Algebraic native publication authenticated: {len(names)} exact files; independent acceptance is checked separately.')

if __name__=='__main__':main()
