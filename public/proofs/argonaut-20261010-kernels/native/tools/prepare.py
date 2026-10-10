"""Restore Argonaut's unmodified public v0.1.8 proof package in isolation."""
from pathlib import Path
import concurrent.futures, hashlib, json, subprocess, time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
PACKET = BASE / 'Lean_Proof'
PROJECT = BASE / 'project'
EVIDENCE = BASE / 'evidence'
PINS = json.loads((PACKET / 'provenance/PINS.json').read_text())
CACHE = ROOT / 'compressed/formalization/.lake/packages'

def git(args, **kwargs):
    return subprocess.run(['git', '-c', 'pack.threads=1', '-c', 'index.threads=1', *args], check=True, **kwargs)

def restore(pin):
    folder = PROJECT / '.lake/packages' / pin['name']
    log = EVIDENCE / ('clone-' + pin['name'] + '.log')
    source = CACHE / pin['name']
    mode = 'fetch exact commit'
    folder.parent.mkdir(parents=True, exist_ok=True)
    with log.open('w') as out:
        if (source / '.git').exists() and git(['-C', str(source), 'cat-file', '-e', pin['revision']], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
            git(['clone', '--shared', '--no-checkout', str(source), str(folder)], stdout=out, stderr=out)
            git(['-C', str(folder), 'remote', 'set-url', 'origin', pin['url']], stdout=out, stderr=out)
            mode = 'local Git object reuse; isolated worktree'
        else:
            git(['init', str(folder)], stdout=out, stderr=out)
            git(['-C', str(folder), 'remote', 'add', 'origin', pin['url']], stdout=out, stderr=out)
            git(['-C', str(folder), 'fetch', '--depth=1', 'origin', pin['revision']], stdout=out, stderr=out)
        git(['-C', str(folder), 'config', 'core.autocrlf', 'false'], stdout=out, stderr=out)
        git(['-C', str(folder), 'checkout', '--detach', pin['revision']], stdout=out, stderr=out)
        actual = git(['-C', str(folder), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
        origin = git(['-C', str(folder), 'remote', 'get-url', 'origin'], capture_output=True, text=True).stdout.strip()
        assert actual == pin['revision'] and origin == pin['url']
        tree = git(['-C', str(folder), 'rev-parse', 'HEAD^{tree}'], capture_output=True, text=True).stdout.strip()
    print('READY', pin['name'], actual, flush=True)
    return {'name':pin['name'], 'revision':actual, 'origin':origin, 'tree':tree, 'mode':mode}

if __name__ == '__main__':
    EVIDENCE.mkdir(exist_ok=True)
    started=time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        records=list(pool.map(restore, PINS['locked_dependencies']))
    (EVIDENCE/'dependency-readback.json').write_text(json.dumps(records,indent=2)+'\n')
    subprocess.run(['python3',str(PACKET/'reproducibility/reconstruct.py'),'--project',str(PROJECT),'--apply-overlay'],check=True)
    print('PREPARED', len(records), 'dependencies', time.time()-started, flush=True)
