"""The signed, sharded submission build cache published by the Build cache workflow.

cache.json lists one shard per submission: the archive of its compiled shared
Submissions.<id>.* modules and their build keys. cache.sig signs cache.json with
the key pinned in verifier/standard/build-cache-public.pem.
"""
from pathlib import Path
import json, re, subprocess, sys, urllib.error, urllib.request
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from standard.build_cache import MAX_BYTES, digest, shard_of

REPOSITORY = 'GTimG/QuasiRiemannTracker'
TAG = 'submission-build-cache-v2'
RELEASE = f'https://github.com/{REPOSITORY}/releases/download/{TAG}/'
KEY = Path(__file__).resolve().parents[1]/'standard/build-cache-public.pem'
INDEX_BYTES = 64 * 1024 * 1024
HEX = re.compile('[a-f0-9]{64}')


def download(url, destination, limit):
    with urllib.request.urlopen(url, timeout=60) as response, destination.open('xb') as output:
        count = 0
        while data := response.read(1024*1024):
            count += len(data)
            if count > limit:
                raise ValueError('Cache download exceeds size limit')
            output.write(data)


def authenticate(index, signature, key=KEY):
    subprocess.run(['openssl', 'pkeyutl', '-verify', '-pubin', '-inkey', str(key),
                    '-rawin', '-in', str(index), '-sigfile', str(signature)],
                   check=True, capture_output=True, timeout=15)
    value = json.loads(index.read_text())
    if value.get('schema_version') != 2 or not isinstance(value.get('shards'), dict):
        raise ValueError('Invalid signed cache index')
    for name, shard in value['shards'].items():
        if (not HEX.fullmatch(shard.get('sha256', '')) or
                shard.get('archive') != shard['sha256']+'.tar.gz' or
                type(shard.get('size')) is not int or not 0 < shard['size'] <= MAX_BYTES or
                not isinstance(shard.get('modules'), dict) or not shard['modules'] or
                any(shard_of(m) != name or not HEX.fullmatch(k) for m, k in shard['modules'].items())):
            raise ValueError(f'Invalid signed cache shard: {name}')
    return value


def fetch_index(directory, fetch=download, verify=authenticate):
    """Return the authenticated index, or None when nothing is published yet."""
    try:
        fetch(RELEASE+'cache.json', directory/'cache.json', INDEX_BYTES)
        fetch(RELEASE+'cache.sig', directory/'cache.sig', 1024)
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return None
        raise
    return verify(directory/'cache.json', directory/'cache.sig')


def fetch_shards(index, names, directory, fetch=download):
    """Download the named shards and bind each archive to the signed index."""
    shards = []
    for name in sorted(names):
        entry = index['shards'][name]
        archive = directory/entry['archive']
        fetch(RELEASE+entry['archive'], archive, entry['size'])
        if archive.stat().st_size != entry['size'] or digest(archive) != entry['sha256']:
            raise ValueError(f'Authenticated cache archive differs: {name}')
        shards.append({'name': name, 'path': str(archive), 'sha256': entry['sha256'],
                       'url': RELEASE+entry['archive']})
    return shards
