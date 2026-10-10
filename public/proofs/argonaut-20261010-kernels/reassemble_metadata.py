#!/usr/bin/env python3
"""Authenticate and reconstruct losslessly chunked public audit metadata.

Usage: python3 reassemble_metadata.py BUNDLE_DIRECTORY OUTPUT_DIRECTORY
Optional --workspace /original/workspace restores original paths and checks the
original SHA256; without it, reconstructed records retain the WORKSPACE label.
"""
from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import json

def sha(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    p = PurePosixPath(name)
    return not p.is_absolute() and '..' not in p.parts and str(p) == name and '\\' not in name

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('bundle', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--workspace')
    args = ap.parse_args()
    manifest = json.loads((args.bundle/'metadata-manifest.json').read_text())
    assert manifest['status'] == 'PASS' and manifest['schema_version'] == 1
    total = 0
    for name, record in manifest['files'].items():
        assert safe(name)
        parts = []
        for chunk in record['chunks']:
            assert safe(chunk['path']) and chunk['expanded_bytes'] <= 4 * 1024 * 1024
            assert sum(len(part) for part in parts) + chunk['expanded_bytes'] + total <= 100 * 1024 * 1024
            source = args.bundle/chunk['path']
            assert not source.is_symlink()
            encoded = source.read_bytes()
            assert sha(encoded) == chunk['sha256']
            # Read at most the authenticated size plus one, avoiding unbounded decompression.
            with gzip.open(source, 'rb') as stream:
                part = stream.read(chunk['expanded_bytes'] + 1)
            assert len(part) == chunk['expanded_bytes'] and sha(part) == chunk['expanded_sha256']
            parts.append(part)
        data = b''.join(parts)
        assert len(data) == record['published_bytes'] and sha(data) == record['published_sha256']
        total += len(data)
        assert total <= 100 * 1024 * 1024
        if args.workspace:
            data = data.replace(b'WORKSPACE', args.workspace.encode())
            assert len(data) == record['original_bytes'] and sha(data) == record['original_sha256']
        target = args.output/name
        assert not target.exists(), 'Refusing to overwrite an existing output'
        assert target.resolve().is_relative_to(args.output.resolve()), 'Output prefix escapes destination'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    assert total == manifest['expanded_total_bytes']
    print(f'PASS: reconstructed {len(manifest["files"])} authenticated metadata files')

if __name__ == '__main__':
    main()
