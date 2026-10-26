#!/usr/bin/env bash
# Executes as root inside a new guest kernel, never on the Docker host.
set -Eeuo pipefail
umask 022
if [[ "$(id -u)" != 0 || "$#" -gt 1 || ( "$#" == 1 && "$1" != --smoke ) ]]; then
  echo 'Usage: guest.sh [--smoke] (inside the disposable guest)' >&2
  exit 1
fi
# The cloud-init wrapper powers off after this script exits, including failures.
trap 'printf "Guest bootstrap failed at line %s (status %s)\n" "$LINENO" "$?" >&2' ERR
# Keep cloud-init's journal/console pipe: restarting a serial getty invalidates
# a directly opened ttyS0 descriptor and would discard subsequent diagnostics.

export http_proxy=http://10.0.2.100:3128 https_proxy=http://10.0.2.100:3128
export HTTP_PROXY="$http_proxy" HTTPS_PROXY="$https_proxy"
export no_proxy=127.0.0.1,localhost NO_PROXY=127.0.0.1,localhost
export DEBIAN_FRONTEND=noninteractive
export NEEDRESTART_MODE=l
export NODE_USE_ENV_PROXY=1

# Only HTTPS archive requests can cross the external allowlisted proxy.
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
useradd --uid 10001 --create-home --shell /bin/bash runner
printf '%s\n' 'runner ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/qrh-runner
chmod 0440 /etc/sudoers.d/qrh-runner
visudo -cf /etc/sudoers.d/qrh-runner

mkdir -p /opt/node /opt/hostedtoolcache/node/22.22.1/x64 /home/runner/actions-runner
tar -xJf /opt/qrh-tools/node.tar.xz --strip-components=1 -C /opt/node
ln -s /opt/node/bin/node /usr/local/bin/node
ln -s /opt/node/bin/npm /usr/local/bin/npm
ln -s /opt/node/bin/npx /usr/local/bin/npx
cp -a /opt/node/. /opt/hostedtoolcache/node/22.22.1/x64/
touch /opt/hostedtoolcache/node/22.22.1/x64.complete
tar -xzf /opt/qrh-tools/runner.tar.gz -C /home/runner/actions-runner
mkdir -p /home/runner/actions-runner/_work
chown -R runner:runner /home/runner /opt/hostedtoolcache
loginctl enable-linger runner
systemctl start user@10001.service
for attempt in {1..20}; do
  [[ -S /run/user/10001/bus ]] && break
  sleep 0.5
done
test -S /run/user/10001/bus

cat > /etc/qrh-runner.env <<'EOF'
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
RUNNER_TOOL_CACHE=/opt/hostedtoolcache
AGENT_TOOLSDIRECTORY=/opt/hostedtoolcache
LANG=C.UTF-8
EOF

if [[ "${1:-}" == --smoke ]]; then
  # Use the same pinned installer and composed preflight as actual admissions.
  # No GitHub runner identity exists anywhere in this smoke-test guest.
  cat > /home/runner/smoke.sh <<'SMOKE'
#!/usr/bin/env bash
set -euo pipefail
test "$(id -u)" = 10001
test "$(node --version)" = v22.22.1
test "$(nproc)" = 6
test -e /sys/fs/cgroup/cgroup.controllers
test "$(cat /sys/module/apparmor/parameters/enabled)" = Y
sudo -n true
systemd-run --user --scope --quiet --property=Delegate=yes true
git init /home/runner/palomar
git -C /home/runner/palomar fetch --depth=1 https://github.com/PalomarRegistry/PalomarSubmission.git d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
git -C /home/runner/palomar checkout --detach FETCH_HEAD
bash /home/runner/palomar/scripts/install_bwrap.sh /home/runner/bwrap-bin
python3 - <<'PY'
import hashlib
import os
from pathlib import Path
import socket
import sys

root = Path('/home/runner/palomar')
assert hashlib.sha256((root/'scripts/verify_submission.py').read_bytes()).hexdigest() == 'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2'
sys.path.insert(0, str(root))
from scripts import verify_submission as v

# The guest can reach its explicit proxy, but not the host gateway or internet
# directly. Native Node fetch must also use the proxy configured above.
with socket.create_connection(('10.0.2.100', 3128), timeout=5):
    pass
for address in [('10.0.2.2', 22), ('1.1.1.1', 443)]:
    try:
        connection = socket.create_connection(address, timeout=2)
    except OSError:
        continue
    connection.close()
    raise RuntimeError('Guest network bypassed the proxy')
work = Path('/home/runner/preflight')
work.mkdir()
for name in ['control', 'home', 'tmp']:
    (work/name).mkdir()
probe = work/'control/read.txt'
probe.write_text('positive read control\n')
python, touch = Path('/usr/bin/python3').resolve(), Path('/usr/bin/touch')
v._BWRAP = Path('/home/runner/bwrap-bin/bwrap')
v.install_execution_deadline(budget_seconds=300)
tools = v.tool_snapshot([v._BWRAP, python, touch])
v.verify_sandbox_confinement(
    work/'control/denied-write', work/'denied-read', positive_read=probe,
    python=python, touch=touch, cwd=work/'control',
    environment={'PATH':'/usr/bin:/bin', 'HOME':str(work/'home'),
                 'TMPDIR':str(work/'tmp'), 'LANG':'C.UTF-8'},
    writable_directories=[work/'home', work/'tmp'],
    protected_write_directories=[work/'control'],
    readable_paths=[work/'control', *v.system_readable_paths()],
    executable_paths=[Path('/usr')], tools=tools)
print('Pinned Palomar filesystem, namespace, network and cgroup preflight passed', flush=True)
PY
node -e 'fetch("https://api.github.com", {signal: AbortSignal.timeout(15000)}).then(r => { if (!r.ok) throw Error(r.status); console.log("Native Node fetch via proxy passed"); }).catch(e => { console.error(e); process.exit(1); })'
SMOKE
  chmod 0755 /home/runner/smoke.sh
  systemd-run --unit=qrh-smoke --wait --pipe --collect \
    --uid=runner --gid=runner --working-directory=/home/runner \
    --property=EnvironmentFile=/etc/qrh-runner.env /home/runner/smoke.sh
  echo QRH_GUEST_SMOKE_PASS
  exit 0
fi

for name in .runner .credentials .credentials_rsaparams; do
  install -m 0600 -o runner -g runner "/var/lib/qrh-identity/$name" "/home/runner/actions-runner/$name"
done
rm -rf /var/lib/qrh-identity
printf '%s\n' /opt/node/bin:/usr/local/bin:/usr/bin:/bin > /home/runner/actions-runner/.path
touch /home/runner/actions-runner/.env
chown runner:runner /home/runner/actions-runner/.path /home/runner/actions-runner/.env

# An idle guest expires after an hour. A trusted pre-job hook cancels only this
# guest timer; the host independently enforces the absolute VM lifetime.
cat > /usr/local/bin/qrh-job-started.sh <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
sudo -n systemctl stop qrh-idle.timer
EOF
chmod 0755 /usr/local/bin/qrh-job-started.sh
printf '%s\n' 'ACTIONS_RUNNER_HOOK_JOB_STARTED=/usr/local/bin/qrh-job-started.sh' >> /etc/qrh-runner.env
systemd-run --unit=qrh-idle --on-active=60m /usr/bin/systemctl poweroff
systemd-run --unit=qrh-runner --wait --pipe --collect \
  --uid=runner --gid=runner --working-directory=/home/runner/actions-runner \
  --property=EnvironmentFile=/etc/qrh-runner.env \
  /home/runner/actions-runner/bin/Runner.Listener run
