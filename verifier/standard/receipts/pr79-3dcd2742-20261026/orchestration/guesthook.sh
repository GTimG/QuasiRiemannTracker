#!/usr/bin/env bash
# One-off guest bootstrap; no GitHub identity or host directory is supplied.
set -Eeuo pipefail
umask 022
if [[ "$(id -u)" != 0 || "$#" -lt 1 || "$#" -gt 2 || ! "$1" =~ ^pr(79|72)$ || ( "$#" == 2 && "$2" != --collect ) ]]; then
  echo 'Usage: guesthook.sh pr79|pr72 [--collect] (inside the guest)' >&2
  exit 1
fi
job="$1"
trap 'printf "Local guest bootstrap failed at line %s (status %s)\n" "$LINENO" "$?" >&2' ERR
test -c /dev/virtio-ports/qrh.evidence
chmod 0600 /dev/virtio-ports/qrh.evidence

collect_evidence() {
  python3 - "$job" <<'PY'
import io
import json
import os
from pathlib import Path
import stat
import sys
import tarfile

root = Path('/home/runner/repository/local-evidence')
metadata = json.loads(Path('/var/lib/qrh-local-job.json').read_text())
assert metadata['job'] == sys.argv[1]
limit = 256 * 1024 * 1024
paths = []
total = 0
if root.exists():
    for directory, subdirs, files in os.walk(root, followlinks=False):
        for name in subdirs:
            if (Path(directory)/name).is_symlink():
                raise RuntimeError('Evidence directory is a symbolic link')
        for name in files:
            path = Path(directory)/name
            info = path.lstat()
            relative = path.relative_to(root).as_posix()
            if not stat.S_ISREG(info.st_mode) or len(relative) > 512 or relative == 'guest-runtime.json':
                raise RuntimeError('Invalid evidence file')
            total += info.st_size
            paths.append((relative, path))
            if total > limit - 1024 * 1024 or len(paths) >= 20000:
                raise RuntimeError('Selected evidence exceeds the collection limit')
metadata['evidence_files'] = len(paths)

class BoundedWriter:
    def __init__(self, target):
        self.target, self.size = target, 0
    def write(self, data):
        self.size += len(data)
        if self.size > limit:
            raise RuntimeError('Evidence tar exceeds the collection limit')
        remaining = memoryview(data)
        while remaining:
            written = self.target.write(remaining)
            if not written:
                raise RuntimeError('Evidence device stopped accepting bytes')
            remaining = remaining[written:]
        return len(data)

with open('/dev/virtio-ports/qrh.evidence', 'wb', buffering=0) as device:
    with tarfile.open(fileobj=BoundedWriter(device), mode='w|', format=tarfile.PAX_FORMAT) as archive:
        contents = (json.dumps(metadata, indent=2) + '\n').encode()
        header = tarfile.TarInfo('guest-runtime.json')
        header.size, header.mode = len(contents), 0o600
        archive.addfile(header, io.BytesIO(contents))
        for relative, path in sorted(paths):
            fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            with os.fdopen(fd, 'rb') as source:
                info = os.fstat(source.fileno())
                if not stat.S_ISREG(info.st_mode):
                    raise RuntimeError('Evidence file type changed')
                header = tarfile.TarInfo(relative)
                header.size, header.mode = info.st_size, 0o600
                archive.addfile(header, source)
print(f'Collected {len(paths)} evidence files through the dedicated device', flush=True)
PY
}

if [[ "${2:-}" == --collect ]]; then
  collect_evidence
  exit 0
fi

export http_proxy=http://10.0.2.100:3128 https_proxy=http://10.0.2.100:3128
export HTTP_PROXY="$http_proxy" HTTPS_PROXY="$https_proxy"
export no_proxy=127.0.0.1,localhost NO_PROXY=127.0.0.1,localhost
export DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=l NODE_USE_ENV_PROXY=1
sed -i -E 's@http://([a-z0-9.-]*archive.ubuntu.com|security.ubuntu.com)/@https://\1/@g' \
  /etc/apt/sources.list.d/ubuntu.sources
cat > /etc/apt/apt.conf.d/90qrh-proxy <<'EOF'
Acquire::http::Proxy "http://10.0.2.100:3128";
Acquire::https::Proxy "http://10.0.2.100:3128";
Acquire::Retries "3";
EOF
apt-get -q -o APT::Update::Error-Mode=any update
apt-get -q install -y --no-install-recommends \
  ca-certificates git curl jq sudo dbus-user-session apparmor-utils \
  build-essential meson ninja-build libcap-dev pkg-config zstd libgmp-dev \
  python3 python3-yaml libicu74 liblttng-ust1t64 libssl3t64 libunwind8 xz-utils
systemctl disable --now ssh.service ssh.socket 2>/dev/null || true
# Avoid package mutations and apt-lock contention during the long proof replay.
systemctl disable --now apt-daily.timer apt-daily-upgrade.timer
useradd --uid 10001 --create-home --shell /bin/bash runner
printf '%s\n' 'runner ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/qrh-runner
chmod 0440 /etc/sudoers.d/qrh-runner
visudo -cf /etc/sudoers.d/qrh-runner
mkdir -p /opt/node /home/runner/repository
tar -xJf /opt/qrh-tools/node.tar.xz --strip-components=1 -C /opt/node
ln -s /opt/node/bin/node /usr/local/bin/node
ln -s /opt/node/bin/npm /usr/local/bin/npm
ln -s /opt/node/bin/npx /usr/local/bin/npx
# This archive contains the reviewed protected orchestration, with its explicit
# recorded timeout-only diff; candidate inputs remain separate on the ISO.
tar -xzf /opt/qrh-inputs/runtime.tar.gz --no-same-owner -C /home/runner/repository
chown -R runner:runner /home/runner/repository
loginctl enable-linger runner
systemctl start user@10001.service
for attempt in {1..20}; do
  [[ -S /run/user/10001/bus ]] && break
  sleep 0.5
done
test -S /run/user/10001/bus

cat > /etc/qrh-local.env <<'EOF'
HOME=/home/runner
PATH=/opt/node/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
HTTP_PROXY=http://10.0.2.100:3128
HTTPS_PROXY=http://10.0.2.100:3128
http_proxy=http://10.0.2.100:3128
https_proxy=http://10.0.2.100:3128
NO_PROXY=127.0.0.1,localhost
no_proxy=127.0.0.1,localhost
NODE_USE_ENV_PROXY=1
XDG_RUNTIME_DIR=/run/user/10001
DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/10001/bus
LANG=C.UTF-8
QRH_WORKER_THREADS=12
QRH_KERNEL_JOBS=1
QRH_REPLAY_BUDGET_SECONDS=129600
EOF

python3 - "$job" <<'PY'
import datetime
import json
from pathlib import Path
import platform
import os
import sys
metadata = {'job': sys.argv[1], 'started_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'kernel': platform.release(), 'processors': os.cpu_count(),
            'memory': Path('/proc/meminfo').read_text().splitlines()[0],
            'exit_status': 125, 'phase': 'job-starting'}
Path('/var/lib/qrh-local-job.json').write_text(json.dumps(metadata))
PY
if systemd-run --unit=qrh-local-job --wait --pipe --collect \
    --uid=runner --gid=runner --working-directory=/home/runner/repository \
    --property=EnvironmentFile=/etc/qrh-local.env \
    /bin/bash /opt/qrh-inputs/local-job.sh "$job"; then
  job_status=0
else
  job_status="$?"
fi
python3 - "$job_status" <<'PY'
import datetime
import json
from pathlib import Path
import sys
path = Path('/var/lib/qrh-local-job.json')
metadata = json.loads(path.read_text())
metadata.update(exit_status=int(sys.argv[1]), phase='job-finished',
                finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
path.write_text(json.dumps(metadata))
PY
collect_evidence
exit "$job_status"
