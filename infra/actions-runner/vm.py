#!/usr/bin/env python3
"""Boot one disposable KVM proof worker with no host filesystem shares."""

import argparse
import base64
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import uuid


REPOSITORY = "https://github.com/GTimG/QuasiRiemannTracker"
IDENTITY_FILES = {".runner", ".credentials", ".credentials_rsaparams"}
VM = Path("/vm")
BASE = Path("/opt/guest-base.qcow2")
TOOLS = Path("/opt/tools.iso")


def read_identity(stream):
    """Accept only the three small regular files from ephemeral registration."""
    data = stream.read(1024 * 1024 + 1)
    if len(data) > 1024 * 1024:
        raise ValueError("Runner identity archive exceeds its size limit")
    files = {}
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as archive:
        for member in archive:
            if (member.name not in IDENTITY_FILES or member.name in files
                    or not member.isfile() or not 0 < member.size <= 262144):
                raise ValueError("Runner identity archive has an invalid member")
            files[member.name] = archive.extractfile(member).read()
    if files.keys() != IDENTITY_FILES:
        raise ValueError("Runner identity archive is incomplete")
    registration = json.loads(files[".runner"].decode("utf-8-sig"))
    if (registration.get("ephemeral") is not True
            or registration.get("disableUpdate") is not True
            or registration.get("gitHubUrl", "").rstrip("/") != REPOSITORY):
        raise ValueError("Runner identity must be ephemeral and repository-scoped")
    registration["workFolder"] = "_work"
    files[".runner"] = json.dumps(registration).encode()
    return files


def prepare_seed(identity, smoke):
    files = [{"path": f"/var/lib/qrh-identity/{name}", "owner": "root:root",
              "permissions": "0600", "encoding": "b64",
              "content": base64.b64encode(content).decode("ascii")}
             for name, content in identity.items()]
    # The ISO and this bootstrap are immutable. Only the disposable guest sees
    # runner credentials; registration tokens and host credentials never enter it.
    bootstrap = (
        "set -eu; trap 'systemctl poweroff --no-block' EXIT; "
        "mkdir -p /opt/qrh-tools; "
        "mount -o ro /dev/disk/by-label/QRH_TOOLS /opt/qrh-tools; "
        "/bin/bash /opt/qrh-tools/guest.sh" + (" --smoke" if smoke else "")
    )
    config = {
        "hostname": "qrh-proof", "manage_etc_hosts": True,
        "users": [], "ssh_pwauth": False, "disable_root": True,
        "package_update": False, "package_upgrade": False,
        "apt": {"preserve_sources_list": True},
        "runcmd": [["bash", "-c", bootstrap]],
    }
    if files:
        config["write_files"] = files
    user_data = VM / "user-data"
    user_data.write_text("#cloud-config\n" + json.dumps(config))
    metadata = VM / "meta-data"
    metadata.write_text(json.dumps({"instance-id": str(uuid.uuid4()),
                                    "local-hostname": "qrh-proof"}))
    network = VM / "network-config"
    network.write_text(json.dumps({"version": 2, "ethernets": {"worker": {
        "match": {"macaddress": "52:54:00:12:34:56"}, "dhcp4": True,
        "dhcp6": False, "accept-ra": False}}}))
    subprocess.run(["cloud-localds", "--network-config", str(network),
                    str(VM / "seed.iso"), str(user_data), str(metadata)], check=True)
    user_data.unlink()


def qemu_command():
    return [
        "qemu-system-x86_64", "-no-user-config", "-nodefaults", "-no-reboot",
        "-machine", "q35,usb=off,vmport=off", "-accel", "kvm",
        "-cpu", "host,vmx=off,svm=off", "-smp", "6", "-m", "24576",
        "-display", "none", "-monitor", "none", "-serial", "stdio",
        "-boot", "order=c,strict=on",
        "-drive", f"file={VM / 'guest.qcow2'},if=none,id=os,format=qcow2,cache=none,discard=unmap",
        "-device", "virtio-blk-pci,drive=os",
        "-drive", f"file={VM / 'seed.iso'},if=none,id=seed,format=raw,readonly=on",
        "-device", "virtio-blk-pci,drive=seed",
        "-drive", f"file={TOOLS},if=none,id=tools,format=raw,readonly=on",
        "-device", "virtio-blk-pci,drive=tools",
        "-netdev", "user,id=restricted,restrict=on,ipv6=off,"
                   "guestfwd=tcp:10.0.2.100:3128-cmd:socat STDIO TCP:qrh-runner-proxy:3128",
        "-device", "virtio-net-pci,netdev=restricted,mac=52:54:00:12:34:56",
        # guestfwd calls setsid() before executing its fixed socat command;
        # QEMU groups setsid with privilege syscalls. Nonroot UID, zero Docker
        # capabilities and inherited no-new-privileges prevent elevation.
        "-sandbox", "on,obsolete=deny,elevateprivileges=allow,spawn=allow,resourcecontrol=deny",
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true",
                        help="boot without an identity and exercise the proof sandbox")
    args = parser.parse_args()
    os.umask(0o077)
    identity = {} if args.smoke else read_identity(sys.stdin.buffer)
    if any(VM.iterdir()):
        raise ValueError("VM storage must be a fresh anonymous volume")
    if not BASE.is_file() or not TOOLS.is_file():
        raise ValueError("Pinned guest image or tools ISO is missing")
    subprocess.run(["qemu-img", "create", "-q", "-f", "qcow2", "-F", "qcow2",
                    "-b", str(BASE), str(VM / "guest.qcow2"), "80G"], check=True)
    prepare_seed(identity, args.smoke)
    identity.clear()
    command = qemu_command()
    if not args.smoke:
        # The controller enforces the outer lifetime and removes the container,
        # anonymous disk and proxy. Guest console output is never a command.
        os.execvp(command[0], command)
    # This mode runs only immutable bootstrap tests, without a registered
    # runner. Its serial marker is a test result, never production job evidence.
    with subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT) as process:
        passed = False
        for line in process.stdout:
            sys.stdout.buffer.write(line)
            sys.stdout.buffer.flush()
            if (line.strip() == b"QRH_GUEST_SMOKE_PASS"
                    or line.strip().endswith(b" QRH_GUEST_SMOKE_PASS")):
                passed = True
        return 0 if process.wait() == 0 and passed else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, tarfile.TarError, OSError, subprocess.CalledProcessError) as error:
        print(f"VM startup failed: {error}", file=sys.stderr)
        sys.exit(1)
