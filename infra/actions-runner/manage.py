#!/usr/bin/env python3
"""Host-side supervisor. GitHub jobs never receive this host's Docker access."""

import argparse
from contextlib import contextmanager
import fcntl
import getpass
import io
import ipaddress
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tarfile
import time
import uuid

ROOT = Path(__file__).resolve().parent
STATE_ROOT = Path.home() / ".local/share/qrh-actions-runner"
SLOTS = (1, 2)
SERVICE = "qrh-proof-runner@.service"
SERVICES = tuple(f"qrh-proof-runner@{slot}.service" for slot in SLOTS)
SLOT = 1
STATE = STATE_ROOT / "proof" / "slot-1"
CONTAINER = "qrh-proof-job-1"
REGISTER = "qrh-proof-register-1"
VM_LIFETIME_SECONDS = 16 * 60 * 60
PROXY = "qrh-proof-proxy"
NETWORK = "qrh-proof-internal"
EGRESS = "qrh-proof-egress"
REPOSITORY = "GTimG/QuasiRiemannTracker"
COMPOSE = ["docker", "compose", "-p", "qrh-proof", "-f", str(ROOT / "compose.yaml")]
STOPPING = False


def run(args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def docker_json(*args):
    return json.loads(run(["docker", *args], capture_output=True, text=True).stdout)


def select_slot(slot):
    global SLOT, STATE, CONTAINER, REGISTER
    if type(slot) is not int or slot not in SLOTS:
        raise ValueError("Runner slot must be 1 or 2")
    SLOT = slot
    STATE = STATE_ROOT / "proof" / f"slot-{slot}"
    CONTAINER = f"qrh-proof-job-{slot}"
    REGISTER = f"qrh-proof-register-{slot}"


def private_state():
    for path in (STATE_ROOT, STATE_ROOT / "proof", STATE):
        path.mkdir(mode=0o700, parents=True, exist_ok=True)
        path.chmod(0o700)


@contextmanager
def file_lock(path, operation):
    with open(path, "w") as lock:
        fcntl.flock(lock, operation)
        yield


@contextmanager
def slot_lock():
    # Shared capacity allows both slots, but excludes smoke tests and the old
    # single supervisor/local proof batch, which take this lock exclusively.
    with file_lock(STATE_ROOT / "proof" / "supervisor.lock", fcntl.LOCK_SH | fcntl.LOCK_NB):
        with file_lock(STATE / "supervisor.lock", fcntl.LOCK_EX | fcntl.LOCK_NB):
            yield


def private_write(path, data):
    temporary = path.with_suffix(".new")
    with open(temporary, "wb", opener=lambda p, f: os.open(p, f, 0o600)) as output:
        output.write(data)
    temporary.chmod(0o600)
    temporary.replace(path)


def ensure_network(name, internal):
    existing = subprocess.run(["docker", "network", "inspect", name], capture_output=True, text=True)
    if existing.returncode:
        args = ["docker", "network", "create", "--driver", "bridge", "--label", "qrh.runner=true"]
        if internal:
            args += ["--internal", "--opt", "com.docker.network.bridge.gateway_mode_ipv4=isolated"]
        run([*args, name], stdout=subprocess.DEVNULL)
    network = docker_json("network", "inspect", name)[0]
    if network["Driver"] != "bridge" or network["Internal"] != internal:
        raise RuntimeError(f"Refusing unexpected network configuration: {name}")
    if internal and network["Options"].get("com.docker.network.bridge.gateway_mode_ipv4") != "isolated":
        raise RuntimeError("Runner network must have isolated gateway mode")


def ensure_proxy():
    # Both supervisors may start together; only one may create/connect the
    # shared networks and proxy container at a time.
    with file_lock(STATE_ROOT / "proof" / "proxy.lock", fcntl.LOCK_EX):
        _ensure_proxy()


def _ensure_proxy():
    ensure_network(NETWORK, True)
    ensure_network(EGRESS, False)
    existing = subprocess.run(["docker", "container", "inspect", PROXY], capture_output=True, text=True)
    if existing.returncode:
        interfaces = json.loads(run(["ip", "-json", "address", "show"], capture_output=True, text=True).stdout)
        host_addresses = [address["local"] for interface in interfaces for address in interface["addr_info"]
                          if ipaddress.ip_address(address["local"]).is_global]
        run([
            "docker", "create", "--name", PROXY, "--label", "qrh.runner=true",
            "--runtime", "runc", "--cgroupns", "private",
            "--network", EGRESS, "--read-only", "--user", "10002:10002",
            "--cap-drop", "ALL",
            "--security-opt", "apparmor=docker-default", "--cpus", "0.5",
            "--memory", "128m", "--memory-swap", "128m", "--pids-limit", "80",
            "--ulimit", "nofile=256:256", "--ulimit", "core=0", "--restart", "unless-stopped",
            "--log-driver", "local", "--log-opt", "max-size=5m", "--log-opt", "max-file=2",
            "--env", "PROXY_DENY_CIDRS=" + ",".join(host_addresses),
            "qrh-runner-proxy:local",
        ], stdout=subprocess.DEVNULL)
        run(["docker", "network", "connect", "--alias", "qrh-runner-proxy", NETWORK, PROXY])
    info = docker_json("container", "inspect", PROXY)[0]
    config = info["HostConfig"]
    if (config["Privileged"] or not config["ReadonlyRootfs"] or info["Mounts"]
            or config["PortBindings"] or info["Config"]["User"] != "10002:10002"
            or set(info["NetworkSettings"]["Networks"]) != {NETWORK, EGRESS}
            or "ALL" not in config["CapDrop"]
            or info["Config"]["Entrypoint"][:2] != ["/usr/bin/setpriv", "--no-new-privs"]):
        raise RuntimeError("Refusing unexpected egress proxy configuration")
    if not info["State"]["Running"]:
        run(["docker", "start", PROXY], stdout=subprocess.DEVNULL)


def registration_token():
    # Only a short-lived registration token enters the registration container.
    # The host's gh authentication and any admin token remain on the host.
    result = subprocess.run([
        "gh", "api", "--method", "POST",
        f"repos/{REPOSITORY}/actions/runners/registration-token", "--jq", ".token",
    ], capture_output=True, text=True)
    if result.returncode == 0 and result.stdout.strip():
        return result.stdout.strip()
    path = STATE_ROOT / "registration-token"
    if path.exists():
        return path.read_text().strip()
    raise RuntimeError("Runner registration requires an admin gh login or a fresh registration token; run manage.py token")


def validate_identity(data):
    required = {".runner", ".credentials", ".credentials_rsaparams"}
    if len(data) > 1024 * 1024:
        raise RuntimeError("Oversized runner identity")
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        members = archive.getmembers()
        if len(members) != 3 or {item.name for item in members} != required:
            raise RuntimeError("Unexpected runner identity files")
        if any(not item.isfile() or not 0 < item.size <= 262144 for item in members):
            raise RuntimeError("Invalid runner identity files")
        settings = json.load(archive.extractfile(".runner"))
        if settings.get("ephemeral") is not True or settings.get("disableUpdate") is not True:
            raise RuntimeError("Refusing a reusable or automatically updating runner identity")
        if settings.get("gitHubUrl", "").rstrip("/") != f"https://github.com/{REPOSITORY}":
            raise RuntimeError("Runner identity belongs to an unexpected repository")
    return data


def register():
    token = registration_token()
    try:
        result = subprocess.run([
            *COMPOSE, "run", "--rm", "--no-deps", "-T", "--name", REGISTER,
            "-e", "ACTIONS_RUNNER_PRINT_LOG_TO_STDOUT=0",
            "-e", f"QRH_RUNNER_NAME=qrh-proof-{SLOT}-{uuid.uuid4().hex[:12]}", "registration", "--register",
        ], input=(token + "\n").encode(), stdout=subprocess.PIPE, timeout=120)
    finally:
        del token
        subprocess.run(["docker", "rm", "--force", "--volumes", REGISTER], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if result.returncode:
        raise RuntimeError("Ephemeral runner registration failed; refresh the registration token or admin gh login")
    identity = validate_identity(result.stdout)
    private_write(STATE / "pending-identity.tar", identity)
    print("A fresh one-job runner identity is ready.", flush=True)


def stop_job(*_args):
    global STOPPING
    STOPPING = True
    subprocess.run(["docker", "stop", "--time", "20", CONTAINER], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def serve():
    private_state()
    with slot_lock():
        ensure_proxy()
        signal.signal(signal.SIGTERM, stop_job)
        signal.signal(signal.SIGINT, stop_job)
        while not STOPPING:
            pending = STATE / "pending-identity.tar"
            if not pending.exists():
                register()
            if STOPPING:
                break
            identity = validate_identity(pending.read_bytes())
            # Consume the identity before startup. Never replay it after any
            # exit, failure, or machine reboot, including interrupted jobs.
            pending.unlink()
            subprocess.run(["docker", "rm", "--force", "--volumes", CONTAINER], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if STOPPING:
                break
            print("Starting a fresh proof VM for one admission job.", flush=True)
            try:
                result = subprocess.run([
                    *COMPOSE, "run", "--rm", "--no-deps", "-T", "--name", CONTAINER, "runner",
                ], input=identity, timeout=VM_LIFETIME_SECONDS)
            except subprocess.TimeoutExpired:
                result = None
                print("Proof VM lifetime limit reached; replacing its identity and disk.", flush=True)
            finally:
                del identity
                subprocess.run(["docker", "rm", "--force", "--volumes", CONTAINER], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            if result is not None and result.returncode and not STOPPING:
                raise RuntimeError(f"Runner exited with status {result.returncode}; inspect service logs before restarting")
            if not STOPPING:
                time.sleep(2)


def install_service():
    unit = Path.home() / ".config/systemd/user" / SERVICE
    unit.parent.mkdir(parents=True, exist_ok=True)
    for legacy in ("qrh-proof-runner.service", "qrh-actions-runner.service",
                   *[f"qrh-actions-runner@{slot}.service" for slot in (1, 2, 3)]):
        if unit.with_name(legacy).exists() or ("@" in legacy and unit.with_name("qrh-actions-runner@.service").exists()):
            run(["systemctl", "--user", "disable", "--now", legacy])
    kvm_gid = os.stat("/dev/kvm").st_gid
    unit.write_text(f"""[Unit]
Description=Ephemeral QRH admission proof VM slot %i (Docker/KVM)
After=network-online.target

[Service]
Type=simple
WorkingDirectory={ROOT}
ExecStart=/usr/bin/python3 {ROOT / 'manage.py'} serve --slot %i
ExecStopPost=-/usr/bin/env docker rm --force --volumes qrh-proof-job-%i qrh-proof-register-%i
Environment=PATH=/usr/local/bin:/usr/bin:/bin:/snap/bin
Environment=QRH_KVM_GID={kvm_gid}
UMask=0077
LogRateLimitIntervalSec=30s
LogRateLimitBurst=500
Restart=no
TimeoutStopSec=45

[Install]
WantedBy=default.target
""")
    run(["systemctl", "--user", "daemon-reload"])
    run(["systemctl", "--user", "enable", *SERVICES])
    print(f"Installed {unit}; use manage.py start to provision both slots.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["build", "smoke", "token", "register", "install-service", "start", "stop", "status", "serve"])
    parser.add_argument("--slot", type=int, choices=SLOTS,
                        help="select one slot; start/stop/status otherwise address both")
    args = parser.parse_args()
    command = args.command
    if args.slot is not None and command not in ("register", "serve", "start", "stop", "status"):
        parser.error("--slot is only valid for register, serve, start, stop, and status")
    select_slot(args.slot or 1)
    private_state()
    os.environ["QRH_KVM_GID"] = str(os.stat("/dev/kvm").st_gid)
    if command == "build":
        run([*COMPOSE, "build", "runner"])
        run(["docker", "build", "-t", "qrh-runner-proxy:local", "-f", str(ROOT / "Proxy.Dockerfile"), str(ROOT)])
    elif command == "smoke":
        with file_lock(STATE_ROOT / "proof" / "supervisor.lock", fcntl.LOCK_EX | fcntl.LOCK_NB):
            ensure_proxy()
            try:
                run([*COMPOSE, "run", "--rm", "--no-deps", "-T", "--name", "qrh-proof-smoke", "runner", "--smoke"], timeout=1800)
            finally:
                subprocess.run(["docker", "rm", "--force", "--volumes", "qrh-proof-smoke"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    elif command == "token":
        token = getpass.getpass("GitHub runner registration token: ") if sys.stdin.isatty() else sys.stdin.readline().strip()
        if not token or len(token) > 1024 or any(character.isspace() for character in token):
            raise RuntimeError("Invalid registration token")
        private_write(STATE_ROOT / "registration-token", token.encode())
        print("Registration token stored privately on the host; it is never passed to jobs.")
    elif command == "register":
        with slot_lock():
            if (STATE / "pending-identity.tar").exists():
                raise RuntimeError("An unused identity already exists; start the service to consume it")
            ensure_proxy()
            register()
    elif command == "install-service":
        install_service()
    elif command == "serve":
        serve()
    else:
        services = (f"qrh-proof-runner@{args.slot}.service",) if args.slot else SERVICES
        run(["systemctl", "--user", command, *services, *(["--no-pager"] if command == "status" else [])])


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError, subprocess.TimeoutExpired, BlockingIOError) as error:
        print(f"Runner stopped safely: {error}", file=sys.stderr)
        sys.exit(78)
