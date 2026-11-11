"""Sign and publish the changed shards of the submission build cache.

The unprivileged build job uses --prepare to package outputs. A separate hosted
job validates that artifact as data, then signs and publishes it. Neither the
signing key nor a repository write token is available in the build job.
"""
from pathlib import Path
import argparse, datetime, json, os, re, shutil, subprocess, sys, tempfile, urllib.error, urllib.parse, urllib.request
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache_release import KEY, REPOSITORY, TAG, authenticate, download, fetch_shards, INDEX_BYTES, RELEASE
from standard.build_cache import SUFFIXES, approved_names, digest, pack_cache, restore_cache, shard_of

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
            source = library/relative
            if any(p.is_symlink() for p in [source, *source.parents] if p == library or library in p.parents):
                raise ValueError('Symlink in compiled submission')
            if source.is_file():
                (staged/relative).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, staged/relative)
    packed = directory/'shard.tar.gz'
    pack_cache(staged, packed, {**keys, 'modules': modules})
    sha = digest(packed)
    archive = directory/(sha+'.tar.gz')
    packed.rename(archive)
    return archive, {'archive': archive.name, 'sha256': sha, 'size': archive.stat().st_size, 'modules': modules}


def validate_plan(directory):
    plan = json.loads((directory/'cache-plan.json').read_text())
    keys, head = plan['keys'], plan['head_sha']
    if head != os.environ['GITHUB_SHA']:
        raise ValueError('The cache plan belongs to another commit')
    approved_names(keys)
    shards = {}
    for module, key in keys['modules'].items():
        shards.setdefault(shard_of(module), {})[module] = key
    if plan['changed']:
        result = json.loads((directory/'run/build-result.json').read_text())
        built_path = directory/'run/build-inputs.json'
        built = json.loads(built_path.read_text())
        required = {m for name in plan['changed'] for m in shards[name]}
        # The build compiled the planned modules with the planned keys.
        if (result.get('status') != 'BUILT' or result.get('head_sha') != head or
                result.get('build_inputs_sha256') != digest(built_path) or
                built['environment'] != keys['environment'] or not required <= built['modules'].keys() or
                any(keys['modules'].get(m) != k for m, k in built['modules'].items())):
            raise ValueError('The shared build does not match its plan')
    return plan, shards


def prepare():
    plan, shards = validate_plan(OUT)
    keys, head = plan['keys'], plan['head_sha']
    bundle = OUT/'cache-publication'
    bundle.mkdir()
    shutil.copyfile(OUT/'cache-plan.json', bundle/'cache-plan.json')
    if plan['changed']:
        (bundle/'run').mkdir()
        for name in ['build-result.json', 'build-inputs.json']:
            shutil.copyfile(OUT/'run'/name, bundle/'run'/name)
    index_shards = {name: entry for name, entry in plan['previous'].items()
                    if name in shards and name not in plan['changed']}
    with tempfile.TemporaryDirectory(dir=OUT, prefix='cache-pack-') as tmp:
        tmp = Path(tmp)
        for name in plan['changed']:
            archive, index_shards[name] = pack_shard(name, shards[name], keys, OUT/'run/candidate-lib', tmp)
            archive.rename(bundle/archive.name)
    (bundle/'cache.json').write_text(json.dumps({'schema_version': 2, 'source_head': head,
        'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'environment': keys['environment'], 'compiler': keys['compiler'],
        'libraries': keys['libraries'], 'shards': index_shards}, sort_keys=True)+'\n')


def validate_bundle(bundle):
    plan, shards = validate_plan(bundle)
    index = json.loads((bundle/'cache.json').read_text())
    if (index.get('schema_version') != 2 or index.get('source_head') != plan['head_sha'] or
            any(index.get(k) != plan['keys'][k] for k in ['environment', 'compiler', 'libraries']) or
            set(index['shards']) != set(shards)):
        raise ValueError('Publication index does not match the cache plan')
    archives = []
    for name, modules in shards.items():
        entry = index['shards'][name]
        if entry['modules'] != modules:
            raise ValueError('Publication module keys do not match the cache plan')
        if name not in plan['changed']:
            if entry != plan['previous'][name]:
                raise ValueError('Unchanged shard was replaced')
            continue
        sha = entry['sha256']
        if not re.fullmatch('[a-f0-9]{64}', sha) or entry['archive'] != sha+'.tar.gz':
            raise ValueError('Invalid publication archive name')
        archive = bundle/entry['archive']
        if archive.is_symlink() or archive.stat().st_size != entry['size'] or digest(archive) != sha:
            raise ValueError('Publication archive checksum differs')
        # Reuse the consumer's strict archive validator; never execute its contents.
        with tempfile.TemporaryDirectory(dir=OUT, prefix='cache-validate-') as tmp:
            selected = restore_cache(archive, Path(tmp)/'lib', {**plan['keys'], 'modules': modules})
            if selected != set(modules):
                raise ValueError('Publication archive is missing planned modules')
        archives.append(archive)
    return plan, index, archives


def sign(index, signature, key_pem):
    if not key_pem:
        raise ValueError('The build-cache signing key is required')
    with tempfile.TemporaryDirectory(prefix='qrh-sign-') as tmp:
        key = Path(tmp)/'signing-key.pem'
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


def main():
    bundle = OUT/'cache-publication'
    plan, index_value, archives = validate_bundle(bundle)
    head = plan['head_sha']
    key_pem, token = os.environ.pop('QRH_BUILD_CACHE_KEY', ''), os.environ.pop('GH_TOKEN', '')
    if not key_pem or not token:
        raise ValueError('The build-cache signing key and a release token are required')
    index = bundle/'cache.json'
    with tempfile.TemporaryDirectory(dir=OUT, prefix='cache-publish-') as tmp:
        tmp = Path(tmp)
        signature = tmp/'cache.sig'
        sign(index, signature, key_pem)
        authenticate(index, signature, KEY)
        current = release(token, head)
        # Archives first, then the index naming them. A reader that sees a
        # mismatched index and signature treats it as a cache miss.
        for archive in archives:
            upload(current, archive, token)
        upload(current, index, token)
        upload(current, signature, token)
        # Keep archives of the previous index for workers that already read it.
        keep = {e['archive'] for e in index_value['shards'].values()} | {e['archive'] for e in plan['previous'].values()}
        current = api('GET', f'{API}/releases/tags/{TAG}', token)
        for asset in current['assets']:
            if asset['name'].endswith('.tar.gz') and asset['name'] not in keep:
                api('DELETE', f'{API}/releases/assets/{asset["id"]}', token)
        # Test the public download path, signature, and exact uploaded archive hashes.
        download(RELEASE+'cache.json', tmp/'downloaded.json', INDEX_BYTES)
        download(RELEASE+'cache.sig', tmp/'downloaded.sig', 1024)
        actual = authenticate(tmp/'downloaded.json', tmp/'downloaded.sig', KEY)
        if actual != index_value:
            raise ValueError('Published cache index differs from this run')
        for name in plan['changed']:
            with tempfile.TemporaryDirectory(dir=tmp) as check:
                fetch_shards(actual, [name], Path(check))
    print(f'Published and downloaded {len(plan["changed"])} changed shards; index lists {len(index_value["shards"])} '
          f'shards for {head}', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        prepare()
    else:
        main()
