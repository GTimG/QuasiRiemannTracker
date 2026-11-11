"""Sign and publish the changed shards of the submission build cache.

Runs in its own step after build.py, the only step that receives the signing
key. Compiled outputs are read as data: each shard archive admits only files
named by module keys that plan-cache.py recorded before any submitted code ran.
"""
from pathlib import Path
import datetime, json, os, shutil, subprocess, sys, tempfile, urllib.error, urllib.parse, urllib.request
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache_release import KEY, REPOSITORY, TAG
from standard.build_cache import SUFFIXES, digest, pack_cache, shard_of

OUT = Path('verification').resolve()
API = f'https://api.github.com/repos/{REPOSITORY}'


def api(method, url, token, data=None, headers=None):
    request = urllib.request.Request(url, data=data, method=method, headers={
        'Authorization': 'Bearer '+token, 'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28', **(headers or {})})
    with urllib.request.urlopen(request, timeout=3600) as response:
        body = response.read()
        return json.loads(body) if body else None


def release(token, head):
    try:
        return api('GET', f'{API}/releases/tags/{TAG}', token)
    except urllib.error.HTTPError as error:
        if error.code != 404:
            raise
    body = json.dumps({'tag_name': TAG, 'target_commitish': head, 'name': 'Submission build cache',
                       'body': 'Signed compiled shared submission modules, published by the Build cache workflow.'})
    return api('POST', f'{API}/releases', token, body.encode(), {'Content-Type': 'application/json'})


def upload(current, path, token):
    for asset in current['assets']:
        if asset['name'] == path.name:
            api('DELETE', f'{API}/releases/assets/{asset["id"]}', token)
    url = (f'https://uploads.github.com/repos/{REPOSITORY}/releases/{current["id"]}/assets?'
           + urllib.parse.urlencode({'name': path.name}))
    with path.open('rb') as data:
        api('POST', url, token, data, {'Content-Type': 'application/octet-stream',
                                       'Content-Length': str(path.stat().st_size)})


def pack_shard(name, modules, keys, library, directory):
    """Archive one shard's compiled modules, admitting only their named outputs."""
    staged = directory/'stage'
    shutil.rmtree(staged, ignore_errors=True)
    for module in modules:
        for suffix in SUFFIXES:
            relative = module.replace('.', '/')+suffix
            if (library/relative).is_file():
                (staged/relative).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(library/relative, staged/relative)
    packed = directory/'shard.tar.gz'
    pack_cache(staged, packed, {**keys, 'modules': modules})
    sha = digest(packed)
    archive = directory/(sha+'.tar.gz')
    packed.rename(archive)
    return archive, {'archive': archive.name, 'sha256': sha, 'size': archive.stat().st_size, 'modules': modules}


def main():
    key_pem, token = os.environ.pop('QRH_BUILD_CACHE_KEY', ''), os.environ.pop('GH_TOKEN', '')
    if not key_pem or not token:
        raise SystemExit('The build-cache signing key and a release token are required')
    plan = json.loads((OUT/'cache-plan.json').read_text())
    keys, head = plan['keys'], plan['head_sha']
    if head != os.environ['GITHUB_SHA']:
        raise SystemExit('The cache plan belongs to another commit')
    shards = {}
    for module, key in keys['modules'].items():
        shards.setdefault(shard_of(module), {})[module] = key
    if plan['changed']:
        result = json.loads((OUT/'run/build-result.json').read_text())
        built = json.loads((OUT/'run/build-inputs.json').read_text())
        # The build compiled the planned modules with the planned keys.
        if (result.get('status') != 'BUILT' or result.get('head_sha') != head or
                built['environment'] != keys['environment'] or
                any(keys['modules'].get(m) != k for m, k in built['modules'].items())):
            raise SystemExit('The shared build does not match its plan')
    index_shards = {name: entry for name, entry in plan['previous'].items()
                    if name in shards and name not in plan['changed']}
    with tempfile.TemporaryDirectory(dir=OUT, prefix='cache-publish-') as tmp:
        tmp = Path(tmp)
        archives = []
        for name in plan['changed']:
            archive, index_shards[name] = pack_shard(name, shards[name], keys, OUT/'run/candidate-lib', tmp)
            archives.append(archive)
        index = tmp/'cache.json'
        index.write_text(json.dumps({'schema_version': 2, 'source_head': head,
            'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'environment': keys['environment'], 'compiler': keys['compiler'],
            'libraries': keys['libraries'], 'shards': index_shards}, sort_keys=True)+'\n')
        signature, key = tmp/'cache.sig', tmp/'signing-key.pem'
        key.touch(mode=0o600)
        key.write_text(key_pem)
        try:
            subprocess.run(['openssl', 'pkeyutl', '-sign', '-inkey', str(key), '-rawin',
                            '-in', str(index), '-out', str(signature)], check=True)
        finally:
            key.unlink()
        # A key that differs from the protected pin would publish an unusable cache.
        subprocess.run(['openssl', 'pkeyutl', '-verify', '-pubin', '-inkey', str(KEY), '-rawin',
                        '-in', str(index), '-sigfile', str(signature)], check=True)
        current = release(token, head)
        # Archives first, then the index naming them. A reader that sees a
        # mismatched index and signature treats it as a cache miss.
        for archive in archives:
            upload(current, archive, token)
        upload(current, index, token)
        upload(current, signature, token)
        # Keep archives of the previous index for workers that already read it.
        keep = {e['archive'] for e in index_shards.values()} | {e['archive'] for e in plan['previous'].values()}
        current = api('GET', f'{API}/releases/tags/{TAG}', token)
        for asset in current['assets']:
            if asset['name'].endswith('.tar.gz') and asset['name'] not in keep:
                api('DELETE', f'{API}/releases/assets/{asset["id"]}', token)
    print(f'Published {len(plan["changed"])} changed shards; index lists {len(index_shards)} '
          f'shards for {head}', flush=True)


if __name__ == '__main__':
    main()
