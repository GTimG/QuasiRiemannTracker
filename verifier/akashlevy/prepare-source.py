#!/usr/bin/env python3
"""Prepare the pinned source bundle from Git objects; never execute project code."""
from pathlib import Path
import argparse,hashlib,json,subprocess,zipfile
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def git_blobs(repo, revision, names):
    requests=[f'{revision}:{name}' for name in names]
    data=subprocess.check_output(['git','-C',str(repo),'cat-file','--batch'],input=('\n'.join(requests)+'\n').encode())
    offset=0;result={}
    for name in names:
        end=data.index(b'\n',offset);header=data[offset:end].split();assert len(header)==3 and header[1]==b'blob','Missing pinned Git blob'
        size=int(header[2]);offset=end+1;result[name]=data[offset:offset+size];assert len(result[name])==size and data[offset+size:offset+size+1]==b'\n';offset+=size+1
    assert offset==len(data);return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tracker',type=Path,required=True);parser.add_argument('--fork',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();pins=json.loads((HERE/'pins.json').read_text())
    prefix='proofs/akashlevy-20261009-weighted-numerator/'
    package=git_blobs(args.tracker,pins['source_commit'],[prefix+p for p in pins['submission_files']])
    for name,digest in pins['submission_files'].items():assert sha(package[prefix+name])==digest,'Pinned submission changed: '+name
    fork=git_blobs(args.fork,pins['dependency_fork']['commit'],['lean/'+r['path'] for r in pins['source_manifest'] if r['origin']=='dependency-fork'])
    assert not args.output.exists(),'Use a new output path'
    with zipfile.ZipFile(args.output,'x',zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for row in pins['source_manifest']:
            data=package[prefix+'formalization/'+row['path']] if row['origin']=='submission' else fork['lean/'+row['path']]
            assert len(data)==row['bytes'] and sha(data)==row['sha256'],'Pinned source changed'
            info=zipfile.ZipInfo(row['path'],date_time=(1980,1,1,0,0,0));info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
            archive.writestr(info,data)
    assert args.output.stat().st_size==pins['source_bundle']['bytes'] and sha(args.output.read_bytes())==pins['source_bundle']['sha256'],'Source bundle differs'
    print('Pinned source bundle authenticated:',len(pins['source_manifest']),'modules;',pins['source_bundle']['sha256'])
if __name__=='__main__':main()
