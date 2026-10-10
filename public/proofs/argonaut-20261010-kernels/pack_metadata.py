#!/usr/bin/env python3
"""Publish authenticated UTF-8 audit metadata as bounded, lossless gzip chunks."""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json

LIMIT = 4 * 1024 * 1024
TOTAL_LIMIT = 100 * 1024 * 1024

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--config', type=Path, required=True)
    args = ap.parse_args()
    cfg = json.loads(args.config.read_text())
    destination = Path(cfg['destination'])
    destination.mkdir(parents=True, exist_ok=True)
    spec = importlib.util.spec_from_file_location('publication_policy', cfg['publication_policy'])
    policy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(policy)
    policy.validate_publication_paths(sorted(cfg['files']))
    records = {}
    total = 0
    for name, filename in cfg['files'].items():
        raw = Path(filename).read_bytes()
        data = raw.replace(cfg['workspace'].encode(), b'WORKSPACE')
        assert data.replace(b'WORKSPACE', cfg['workspace'].encode()) == raw, 'Non-reversible prefix replacement'
        policy.check_content(name, data)
        total += len(data)
        assert total <= TOTAL_LIMIT, 'Expanded metadata exceeds total resource bound'
        parts, current = [], bytearray()
        for line in data.splitlines(keepends=True):
            assert len(line) <= LIMIT, 'Single metadata line exceeds chunk bound'
            if len(current) + len(line) > LIMIT:
                parts.append(bytes(current))
                current.clear()
            current.extend(line)
        if current:
            parts.append(bytes(current))
        chunks = []
        for index, part in enumerate(parts):
            chunk_name = f'{name}.{index:04d}.txt.gz'
            policy.check_content(chunk_name[:-3], part)
            encoded = gzip.compress(part, compresslevel=9, mtime=0)
            target = destination / chunk_name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(encoded)
            assert gzip.decompress(target.read_bytes()) == part
            chunks.append({'path': chunk_name, 'sha256': sha(encoded),
                           'expanded_sha256': sha(part), 'expanded_bytes': len(part)})
        joined = b''.join(gzip.decompress((destination / c['path']).read_bytes()) for c in chunks)
        assert joined == data
        records[name] = {'original_sha256': sha(raw), 'original_bytes': len(raw),
                         'published_sha256': sha(data), 'published_bytes': len(data),
                         'workspace_prefix_neutralized': raw != data, 'chunks': chunks}
    report = {'schema_version': 1, 'status': 'PASS', 'files': records,
              'expanded_total_bytes': total, 'expanded_chunk_limit': LIMIT,
              'expanded_total_limit': TOTAL_LIMIT,
              'checks': ['Complete UTF-8 content scan using repository publication policy',
                         'Every expanded chunk scanned, bounded and hash-checked',
                         'Lossless concatenation and reversible workspace normalization'],
              'policy_sha256': sha(Path(cfg['publication_policy']).read_bytes()),
              'packer_sha256': sha(Path(__file__).read_bytes())}
    (destination / 'metadata-manifest.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'files': len(records), 'expanded_bytes': total,
                      'manifest_sha256': sha((destination/'metadata-manifest.json').read_bytes())}))

if __name__ == '__main__':
    main()
