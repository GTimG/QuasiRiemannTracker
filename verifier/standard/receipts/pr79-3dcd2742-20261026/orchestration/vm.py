#!/usr/bin/env python3
"""One-off isolated QRH verification; never register a GitHub runner."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import socket
import subprocess
import sys
import tarfile
import threading
import time
import uuid

VM = Path('/vm')
INPUTS = Path('/opt/inputs.iso')
LIMIT = 256 * 1024 * 1024
MAX_FILES = 20000


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def seed(job, collect):
    bootstrap = (
        "set -eu; trap 'systemctl poweroff --no-block' EXIT; "
        "mkdir -p /opt/qrh-tools /opt/qrh-inputs; "
        "mount -o ro /dev/disk/by-label/QRH_TOOLS /opt/qrh-tools; "
        "mount -o ro /dev/disk/by-label/QRH_INPUTS /opt/qrh-inputs; "
        f"/bin/bash /opt/qrh-inputs/guesthook.sh {job}" + (' --collect' if collect else '')
    )
    config = {
        'hostname': 'qrh-local-' + job, 'manage_etc_hosts': True,
        'users': [], 'ssh_pwauth': False, 'disable_root': True,
        'package_update': False, 'package_upgrade': False,
        'apt': {'preserve_sources_list': True},
        'runcmd': [['bash', '-c', bootstrap]],
    }
    (VM/'user-data').write_text('#cloud-config\n' + json.dumps(config))
    (VM/'meta-data').write_text(json.dumps({'instance-id': str(uuid.uuid4()),
                                           'local-hostname': 'qrh-local-' + job}))
    (VM/'network-config').write_text(json.dumps({'version': 2, 'ethernets': {'worker': {
        'match': {'macaddress': '52:54:00:12:34:56'}, 'dhcp4': True,
        'dhcp6': False, 'accept-ra': False}}}))
    (VM/'seed.iso').unlink(missing_ok=True)
    subprocess.run(['cloud-localds', '--network-config', str(VM/'network-config'),
                    str(VM/'seed.iso'), str(VM/'user-data'), str(VM/'meta-data')], check=True)


def collect_stream(process, errors):
    """A byte-only channel with its size ceiling enforced outside the guest."""
    connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    connection.settimeout(1)
    try:
        deadline = time.monotonic() + 30
        while True:
            try:
                connection.connect(str(VM/'evidence.sock'))
                break
            except (FileNotFoundError, ConnectionRefusedError):
                if process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('QEMU evidence channel did not open')
                time.sleep(0.05)
        size = 0
        with (VM/'evidence.tar').open('xb') as output:
            while True:
                try:
                    block = connection.recv(65536)
                except socket.timeout:
                    if process.poll() is not None:
                        break
                    continue
                if not block:
                    break
                size += len(block)
                if size > LIMIT:
                    raise RuntimeError('Guest exceeded the 256 MiB evidence ceiling')
                output.write(block)
    except Exception as error:
        errors.append(str(error))
        if process.poll() is None:
            process.terminate()
    finally:
        connection.close()


def validate_evidence(path, job):
    """Read bounded regular files; never extract guest paths onto the host."""
    if not 1024 <= path.stat().st_size <= LIMIT:
        raise ValueError('Evidence archive has an invalid size')
    names = set()
    hashes = {}
    total = 0
    metadata = None
    with tarfile.open(path, mode='r:') as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            if (not member.isfile() or name.is_absolute() or '..' in name.parts
                    or str(name) != member.name or member.name in names
                    or len(member.name) > 512 or len(names) >= MAX_FILES
                    or member.size < 0 or member.size > LIMIT):
                raise ValueError('Evidence archive contains an invalid member')
            names.add(member.name)
            total += member.size
            if total > LIMIT:
                raise ValueError('Evidence contents exceed their size limit')
            source = archive.extractfile(member)
            if member.name == 'guest-runtime.json':
                if member.size > 65536:
                    raise ValueError('Guest runtime metadata is too large')
                content = source.read()
                metadata = json.loads(content)
                hashes[member.name] = hashlib.sha256(content).hexdigest()
            else:
                hashes[member.name] = hashlib.file_digest(source, 'sha256').hexdigest()
    if (not isinstance(metadata, dict) or metadata.get('job') != job
            or type(metadata.get('exit_status')) is not int
            or not 0 <= metadata['exit_status'] <= 255
            or metadata.get('evidence_files') != len(names) - 1):
        raise ValueError('Guest runtime metadata is absent or invalid')
    return metadata, hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('job', choices=['pr79', 'pr72'])
    parser.add_argument('--collect', action='store_true',
                        help='recover selected evidence from the existing guest disk')
    args = parser.parse_args()
    os.umask(0o077)
    spec = importlib.util.spec_from_file_location('base_vm', '/opt/runner-vm.py')
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    input_hash = digest(INPUTS)
    if args.collect:
        previous = json.loads((VM/'job.json').read_text())
        if previous != {'job': args.job, 'inputs_sha256': input_hash}:
            raise ValueError('Recovery must use the original job and immutable inputs')
        if not (VM/'guest.qcow2').is_file():
            raise ValueError('Recovery guest disk is missing')
        if (VM/'evidence.tar').exists():
            backup = VM/('evidence-' + str(time.time_ns()) + '.tar')
            (VM/'evidence.tar').rename(backup)
    else:
        if any(VM.iterdir()):
            raise ValueError('Verification requires a fresh anonymous VM volume')
        subprocess.run(['qemu-img', 'create', '-q', '-f', 'qcow2', '-F', 'qcow2',
                        '-b', str(base.BASE), str(VM/'guest.qcow2'), '80G'], check=True)
        (VM/'job.json').write_text(json.dumps({'job': args.job, 'inputs_sha256': input_hash}))
    (VM/'evidence.sock').unlink(missing_ok=True)
    seed(args.job, args.collect)
    command = base.qemu_command() + [
        '-drive', f'file={INPUTS},if=none,id=inputs,format=raw,readonly=on',
        '-device', 'virtio-blk-pci,drive=inputs',
        '-device', 'virtio-serial-pci',
        '-chardev', f'socket,id=evidence,path={VM / "evidence.sock"},server=on,wait=off',
        '-device', 'virtserialport,chardev=evidence,name=qrh.evidence',
    ]
    errors = []
    with subprocess.Popen(command, stdin=subprocess.DEVNULL) as process:
        collector = threading.Thread(target=collect_stream, args=(process, errors), daemon=True)
        collector.start()
        status = process.wait()
        collector.join(timeout=5)
        if collector.is_alive():
            raise RuntimeError('Evidence collector did not terminate')
    if status or errors:
        raise RuntimeError(f'Guest execution failed: QEMU status {status}; {errors}')
    metadata, hashes = validate_evidence(VM/'evidence.tar', args.job)
    report = {'guest': metadata, 'inputs_sha256': input_hash,
              'evidence_sha256': digest(VM/'evidence.tar'), 'files': hashes}
    (VM/'evidence-manifest.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f"Evidence validated: {len(hashes)} files, guest exit {metadata['exit_status']}", flush=True)
    return 0 if args.collect or metadata['exit_status'] == 0 else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, tarfile.TarError, subprocess.CalledProcessError) as error:
        print(f'Local verification stopped safely: {error}', file=sys.stderr)
        sys.exit(1)
