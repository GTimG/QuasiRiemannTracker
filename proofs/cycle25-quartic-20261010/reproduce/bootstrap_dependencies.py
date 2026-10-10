#!/usr/bin/env python3
"""Prepare pinned source archives; no Git remote synchronization or lock update."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

HERE = Path(__file__).resolve().parent
DEPS = HERE.parent / 'dependencies'
PINS = json.loads((DEPS / 'dependency-pins.json').read_text())
NEEDED = json.loads((DEPS / 'needed-package-sources.json').read_text())


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def check_package(path, row):
    if any(parent.is_symlink() for parent in [path, path.parent, path.parent.parent]):
        raise ValueError('Dependency root/parent is a symlink: ' + row['name'])
    for item in row['files']:
        file = path / item['path']
        if any(parent.is_symlink() for parent in [file, *file.parents] if parent.is_relative_to(path)) or digest(file) != item['sha256']:
            raise ValueError('Dependency source/config mismatch: ' + row['name'] + '/' + item['path'])


def extract(archive, destination, omitted_symlinks=()):
    """Extract regular files/directories only; refuse links and traversal."""
    with tarfile.open(archive, 'r:gz') as tar:
        roots = set()
        for item in tar.getmembers():
            parts = PurePosixPath(item.name).parts
            if not parts or item.name.startswith('/') or '..' in parts:
                raise ValueError('Unsafe archive path')
            roots.add(parts[0])
            if len(parts) == 1:
                if not item.isdir():
                    raise ValueError('Expected an archive root directory')
                continue
            relative = '/'.join(parts[1:])
            if item.issym() and relative in omitted_symlinks:
                continue
            target = destination.joinpath(*parts[1:])
            if item.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif item.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(item) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
                target.chmod(item.mode & 0o777)
            else:
                raise ValueError('Archive links/special files are not supported')
        if len(roots) != 1:
            raise ValueError('Expected exactly one source archive root')


def check_configs(project):
    for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
        path = project / name
        if path.is_symlink() or path.read_bytes() != (HERE / name).read_bytes():
            raise ValueError('Use the supplied portable configuration: ' + name)
    for patch in PINS['patches']:
        if digest(DEPS / patch['path']) != patch['sha256']:
            raise ValueError('Compatibility patch hash mismatch')


def prepare(project, archive_dir):
    check_configs(project)
    version = subprocess.check_output(['elan', 'run', PINS['toolchain']['toolchain'],
                                       'lean', '--version'], text=True)
    if PINS['toolchain']['commit'] not in version:
        raise ValueError('Unexpected source compiler commit')
    lake = project / '.lake'
    packages = lake / 'packages'
    if lake.is_symlink() or packages.is_symlink():
        raise ValueError('Use a fresh standalone .lake directory')
    packages.mkdir(parents=True, exist_ok=True)
    rows = {row['name']: row for row in NEEDED['packages']}
    for package in PINS['packages']:
        name = package['name'].strip('«»')
        destination = packages / name
        if destination.exists() or destination.is_symlink():
            check_package(destination, rows[name])
            continue
        with tempfile.TemporaryDirectory(prefix='cycle25-' + name + '-', dir=packages) as temp:
            stage = Path(temp)
            archive = stage / 'source.tar.gz'
            if archive_dir is not None:
                source = archive_dir / (name + '-' + package['rev'] + '.tar.gz')
                shutil.copyfile(source, archive)
            else:
                repository = package['url'].removesuffix('.git').removeprefix('https://github.com/')
                if len(repository.split('/')) != 2:
                    raise ValueError('Unexpected dependency repository URL')
                url = 'https://codeload.github.com/' + repository + '/tar.gz/' + package['rev']
                request = urllib.request.Request(url, headers={'User-Agent': 'Cycle25-source-reproduction'})
                with urllib.request.urlopen(request, timeout=120) as source, archive.open('wb') as output:
                    shutil.copyfileobj(source, output)
            source_root = stage / 'extracted'
            source_root.mkdir()
            extract(archive, source_root, PINS['omitted_archive_symlinks'].get(name, []))
            for patch in PINS['patches']:
                if patch['package'] != name:
                    continue
                file = str(DEPS / patch['path'])
                subprocess.run(['git', 'apply', '--check', file], cwd=source_root, check=True)
                subprocess.run(['git', 'apply', file], cwd=source_root, check=True)
            check_package(source_root, rows[name])
            source_root.rename(destination)
        print('Prepared exact needed sources: ' + name, flush=True)
    print('All pinned dependency source and configuration hashes passed.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--prepare', action='store_true')
    modes.add_argument('--check', action='store_true')
    parser.add_argument('--archive-dir', type=Path,
                        help='Offline archives named PACKAGE-COMMIT.tar.gz; otherwise --prepare downloads exact commits')
    args = parser.parse_args()
    project = args.project.resolve()
    if args.prepare:
        prepare(project, args.archive_dir)
    else:
        check_configs(project)
        for row in NEEDED['packages']:
            check_package(project / '.lake/packages' / row['name'], row)
        print('Dependency source/configuration checks passed.')


if __name__ == '__main__':
    main()
