#!/usr/bin/env python3
"""Fetch source-keyed artifacts from Mathlib's official master cache in isolation."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import requests
import threading
import time

HERE = Path(__file__).resolve().parent
KEYS = HERE / 'mathlib-cache-keys.tsv'
DEST = HERE / 'official-mathlib-cache'
BASE = 'https://cache.mathlib.org/mathlib4-master/f/'
LOCAL = threading.local()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def fetch(item):
    module, filename = item
    if not hasattr(LOCAL, 'session'):
        LOCAL.session = requests.Session()
    url = BASE + filename
    for attempt in range(4):
        try:
            response = LOCAL.session.get(url, timeout=(20, 120))
            response.raise_for_status()
            if response.url != url:
                raise ValueError('Unexpected cache redirect: ' + response.url)
            data = response.content
            if data[:4] not in (b'LTAR', b'LTR2', b'LTR3'):
                raise ValueError('Unexpected archive magic: ' + filename)
            path = DEST / filename
            path.write_bytes(data)
            return module, {'file': str(path), 'url': url, 'sha256': sha(data),
                            'bytes': len(data), 'http_status': response.status_code,
                            'etag': response.headers.get('etag'),
                            'last_modified': response.headers.get('last-modified')}
        except Exception:
            if attempt == 3:
                raise
            time.sleep(attempt + 1)

def main():
    DEST.mkdir(exist_ok=True)
    items = [line.rstrip().split('\t') for line in KEYS.read_text().splitlines()]
    assert len(dict(items)) == len(items)
    records = {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = [pool.submit(fetch, item) for item in items]
        for future in as_completed(futures):
            module, value = future.result()
            records[module] = value
            if len(records) % 500 == 0:
                print(f'{len(records)}/{len(items)} authenticated HTTPS downloads', flush=True)
    result = {'status': 'PASS', 'retrieved_at_utc': datetime.now(timezone.utc).isoformat(),
              'source': BASE, 'module_count': len(records),
              'source_key_map_sha256': sha(KEYS.read_bytes()),
              'fetch_script_sha256': sha(Path(__file__).read_bytes()),
              'scope': 'Fresh HTTPS downloads from the official master-only Mathlib cache. Module keys derive from the separately pinned source tree using Cache.Hashing; cache hashes are source-address keys, not cryptographic artifact digests. SHA256 below pins fetched bytes.',
              'modules': dict(sorted(records.items()))}
    (HERE / 'official-mathlib-cache-downloads.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f'PASS: {len(records)} archives, {sum(v["bytes"] for v in records.values())} bytes', flush=True)

if __name__ == '__main__':
    main()
