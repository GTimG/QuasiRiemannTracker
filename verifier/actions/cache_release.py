"""The signed, sharded submission build cache published by the Build cache workflow.

cache.json lists one logical shard per submission, split into bounded archives
of compiled shared modules and their build keys. cache.sig signs cache.json with
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
# New pieces stay below GitHub's per-asset limit and the consumer's 4 GiB cap.
PART_ARCHIVE_BYTES = 1024 ** 3
MAX_PARTS = 10000


def download(url, destination, limit):
    with urllib.request.urlopen(url, timeout=60) as response, destination.open('xb') as output:
        count = 0
        while data := response.read(1024*1024):
            count += len(data)
            if count > limit:
                raise ValueError('Cache download exceeds size limit')
            output.write(data)


def validate_index(value):
    """Validate exact, disjoint module coverage before downloading any archive.

    Version 2 is read-only compatibility for previously signed single archives;
    new publication uses version 3 and smaller, individually authenticated parts.
    """
    if not isinstance(value, dict):
        raise ValueError('Invalid signed cache index')
    version = value.get('schema_version')
    if type(version) is not int or version not in (2, 3) or not isinstance(value.get('shards'), dict):
        raise ValueError('Invalid signed cache index')
    archives = set()
    for name, shard in value['shards'].items():
        expected = {'archive', 'sha256', 'size', 'modules'} if version == 2 else {'modules', 'parts'}
        if (not isinstance(shard, dict) or set(shard) != expected or not isinstance(shard.get('modules'), dict) or
                not shard['modules'] or any(shard_of(m) != name or not isinstance(k, str) or
                not HEX.fullmatch(k) for m, k in shard['modules'].items())):
            raise ValueError(f'Invalid signed cache shard: {name}')
        parts = [shard] if version == 2 else shard.get('parts')
        if not isinstance(parts, list) or not parts:
            raise ValueError(f'Missing cache parts: {name}')
        covered = {}
        for part in parts:
            if (not isinstance(part, dict) or not isinstance(part.get('sha256'), str) or
                    not HEX.fullmatch(part['sha256']) or part.get('archive') != part['sha256']+'.tar.gz' or
                    type(part.get('size')) is not int or not 0 < part['size'] <=
                    (MAX_BYTES if version == 2 else PART_ARCHIVE_BYTES) or
                    not isinstance(part.get('modules'), dict) or not part['modules']):
                raise ValueError(f'Invalid cache part: {name}')
            if part['archive'] in archives or len(archives) >= MAX_PARTS:
                raise ValueError('Duplicate or excessive cache parts')
            archives.add(part['archive'])
            for module, key in part['modules'].items():
                if module in covered or module not in shard['modules'] or shard['modules'][module] != key:
                    raise ValueError(f'Duplicate or unexpected cache part module: {module}')
                covered[module] = key
        if covered != shard['modules']:
            raise ValueError(f'Cache parts do not cover shard: {name}')
    return value


def shard_parts(shard):
    """Return archive entries for a validated v2 or v3 logical shard."""
    return [shard] if 'archive' in shard else shard['parts']


def authenticate(index, signature, key=KEY):
    if index.stat().st_size > INDEX_BYTES or signature.stat().st_size > 1024:
        raise ValueError('Oversized cache index or signature')
    subprocess.run(['openssl', 'pkeyutl', '-verify', '-pubin', '-inkey', str(key),
                    '-rawin', '-in', str(index), '-sigfile', str(signature)],
                   check=True, capture_output=True, timeout=15)
    return validate_index(json.loads(index.read_text()))


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
        for entry in shard_parts(index['shards'][name]):
            archive = directory/entry['archive']
            fetch(RELEASE+entry['archive'], archive, entry['size'])
            if archive.stat().st_size != entry['size'] or digest(archive) != entry['sha256']:
                raise ValueError(f'Authenticated cache archive differs: {name}')
            shards.append({'name': name, 'path': str(archive), 'sha256': entry['sha256'],
                           'url': RELEASE+entry['archive']})
    return shards
