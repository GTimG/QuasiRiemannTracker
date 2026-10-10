#!/usr/bin/env python3
"""Fetch pinned sources, restore their layout, and optionally build or replay.

--build uses the tested bounded native compiler driver with explicit cache
inputs. --replay-from authenticates an existing successful build and replays
its original 22-target Lean entry against a fresh source reconstruction.
Neither mode claims a clean, cache-free Lake dependency build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from prepare import LIU, OAI

def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def run(args, cwd=None):
    subprocess.run([str(x) for x in args], cwd=cwd, check=True)

def fetch(url, revision, dest):
    if not (dest / '.git').exists():
        dest.mkdir(parents=True, exist_ok=True)
        run(['git', 'init', dest])
        run(['git', '-C', dest, 'remote', 'add', 'origin', url])
    actual_url=subprocess.check_output(['git','-C',str(dest),'remote','get-url','origin'],text=True).strip()
    if actual_url != url:
        raise SystemExit('Unexpected source remote: '+str(dest))
    run(['git','-C',dest,'fetch','--depth=1','origin',revision])
    run(['git','-C',dest,'checkout','--detach',revision])
    actual=subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()
    if actual != revision:
        raise SystemExit('Fetched revision mismatch')

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--work',type=Path,required=True)
    modes=ap.add_mutually_exclusive_group()
    modes.add_argument('--build',action='store_true')
    modes.add_argument('--replay-from',type=Path)
    ap.add_argument('--lean',type=Path)
    ap.add_argument('--lean-path-file',type=Path)
    ap.add_argument('--inventory-sha256',help='Required authenticated inventory digest for artifact replay')
    ap.add_argument('--workers',type=int,default=8)
    args=ap.parse_args();here=Path(__file__).resolve().parent
    work=args.work.resolve();work.mkdir(parents=True,exist_ok=True)
    if args.workers<1:raise SystemExit('workers must be positive')
    if args.build and not (args.lean and args.lean_path_file):
        raise SystemExit('--build requires --lean and --lean-path-file; these are explicit cache inputs')
    if args.replay_from and not args.inventory_sha256:
        raise SystemExit('--replay-from requires --inventory-sha256 from the authenticated report')
    if hasattr(os,'sched_getaffinity'):
        os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:args.workers])
    liu=work/'liu-source';oai=work/'openai-source';package=work/'package'
    fetch('https://github.com/liubaiying101/Slightly-improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis.git',LIU,liu)
    fetch('https://github.com/openai/math.git',OAI,oai)
    run([sys.executable,here/'prepare.py','--liu',liu,'--openai',oai,'--output',package])
    mode='fetch-and-reconstruct'
    if args.build:
        run([sys.executable,here/'build_native.py','--package',package,'--lean',args.lean.resolve(),
             '--lean-path-file',args.lean_path_file.resolve(),'--workers',args.workers])
        run([sys.executable,here/'verify_native.py','--work',work,'--workers',args.workers])
        mode='native-build-with-explicit-cache-inputs'
    elif args.replay_from:
        previous=args.replay_from.resolve();inventory_path=previous/'judge-input-inventory.json'
        if sha(inventory_path)!=args.inventory_sha256:
            raise SystemExit('Authenticated inventory file digest mismatch')
        inventory=json.loads(inventory_path.read_text())
        if not inventory['native_build_success'] or not inventory['candidate_imports_no_QRH']:
            raise SystemExit('Previous input closure did not pass')
        old_verification=previous/'native-verification.json'
        if sha(old_verification)!=inventory['native_verification_sha256']:
            raise SystemExit('Native verification report changed')
        verified=json.loads(old_verification.read_text())
        if verified['status']!='PASS' or sha(previous/'native/build-result.json')!=verified['native_build_sha256']:
            raise SystemExit('Native build report changed or failed')
        for rel,digest in inventory['source_files'].items():
            if sha(Path(inventory['source_root'])/rel)!=digest:
                raise SystemExit('Reused source changed: '+rel)
        for path,digest in inventory['artifact_files'].items():
            if sha(path)!=digest:
                raise SystemExit('Reused artifact changed: '+path)
        if (work/'source-manifest.json').read_bytes()!=(previous/'source-manifest.json').read_bytes():
            raise SystemExit('Fresh source reconstruction differs from the verified one')
        native=work/'native';native.mkdir(exist_ok=True)
        (native/'lib').symlink_to(previous/'native/lib',target_is_directory=True)
        original_build=previous/'native/build-result.json'
        (native/'build-result.json').write_bytes(original_build.read_bytes())
        run([sys.executable,here/'verify_native.py','--work',work,'--workers',args.workers])
        mode='fresh-source-reconstruction-with-authenticated-artifact-replay'
    record={'status':'PASS','mode':mode,'liu_commit':LIU,'openai_commit':OAI,
            'reconstructed_package_manifest_sha256':sha(work/'source-manifest.json'),
            'proof_source_changes':False,'clean_cache_free_dependency_build_tested':False,
            'original_author_lean_entry_replayed':bool(args.build or args.replay_from),
            'original_author_python_lake_driver_run':False,
            'scope':'Uses the original 22-target Lean verification entry, with our native scheduler/replay driver; cached dependencies are explicit inputs and require the separate independent kernel judge.'}
    if args.replay_from:
        record.update(reused_inventory_sha256=args.inventory_sha256,
                      reused_native_build_sha256=sha(original_build),reused_artifact_root=str(previous/'native/lib'))
    (work/'reproduction-result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
