# QRH admission proof runner

Only `pr-admission.verify` uses `[self-hosted, Linux, X64, qrh-proof]`.
Website CI, admission preparation and publication, integration tests, and GitHub
Pages stay on GitHub-hosted runners. The workflow checks out the trusted workflow
commit and gives the proof worker read-only repository permissions.

Two admission jobs can run independently, each with 6 CPUs and 24 GiB RAM.
Compilation uses six workers per job; the three independent kernels run
sequentially so each can use that job's memory allocation. Admission replay has
a bounded twelve-hour budget to accommodate the split CPU allocation; the
other verifier entry points retain their three-hour default. The serial kernel
phase can use up to three hours, combining the one-hour allowance for each of the
three checkers, and is capped by the remaining replay budget. Individual module
deadlines and sandbox resource limits still apply.

## Isolation

Each job boots a fresh Ubuntu KVM guest inside a constrained Docker container.
The guest provides the AppArmor policy management and delegated cgroups required
by the existing Palomar proof sandbox. Workflow `sudo` operates inside that guest;
setup and operation require no host sudo when Docker and `/dev/kvm` are accessible.

- Outer container: nonroot, no capabilities, no-new-privileges, default Docker
  seccomp and AppArmor, read-only root, private PID/cgroup namespaces.
- Only `/dev/kvm` is exposed. There are no host directories, Docker socket,
  published ports, guest filesystem shares, or QEMU management interfaces.
- Per-slot limits: 6 CPUs, 26 GiB outer memory without swap, 512 outer processes,
  an 80 GiB guest disk with an 82 GiB backing-file limit, and bounded logs.
  Leave at least 164 GiB free in Docker storage before starting both slots.
- The guest has no direct route to the host, LAN, or Internet. Its only network
  forwarding reaches an HTTPS proxy allowing required GitHub, Ubuntu, npm, Node,
  Mathlib cache, and Azure hosts. The proxy rejects private and host public addresses.
- A separate registration container creates an ephemeral runner identity. The
  registration container has one CPU, 1 GiB RAM, bounded temporary filesystems,
  and no VM disk or KVM access. Its file-size limit permits .NET's sparse memory
  mappings; the proof VM retains its 82 GiB backing-file limit. The guest receives
  only the identity, never registration tokens or host credentials.
- After one job the guest shuts down; Docker removes its anonymous disk volume.
  An idle guest expires after one hour. The host enforces a sixteen-hour absolute
  lifetime, including boot and idle time, independent of guest behavior.
  Identities are consumed before startup and never reused after any exit.

Docker, KVM, QEMU and the guest sandbox remain security boundaries that need
updates. The proxy permits uploads to allowed services; do not give proof jobs
personal secrets or additional host access. The immutable Docker entrypoint sets
`no-new-privs` after the AppArmor transition to support Snap Docker.

## Setup

From the repository root, with Docker, accessible `/dev/kvm`, Python 3 and `gh`:

```sh
python3 infra/actions-runner/manage.py build
python3 infra/actions-runner/manage.py smoke
```

The smoke run boots a guest without a GitHub identity and checks the actual pinned
Palomar sandbox, user cgroup delegation, AppArmor, proxy access and blocked direct
egress. It uses the same resource allocation as a job and excludes concurrent
operation of both slots.

For automatic registration, authenticate the host's `gh` with repository
runner-administration access. A fine-grained token needs repository
[Administration write permission](https://docs.github.com/en/rest/actions/self-hosted-runners#create-a-registration-token-for-a-repository).
Alternatively, enter a registration token from **Settings → Actions → Runners →
New self-hosted runner**:

```sh
python3 infra/actions-runner/manage.py token
python3 infra/actions-runner/manage.py install-service
python3 infra/actions-runner/manage.py start
python3 infra/actions-runner/manage.py status
```

The hidden token prompt stores it mode 0600 under
`~/.local/share/qrh-actions-runner/`. Registration tokens expire after one hour;
an already registered runner can finish its job, but future registrations need
a fresh token or admin `gh` login. Registration failure stops the service.

Installation disables the previous website and single proof runner services and enables the
two user services `qrh-proof-runner@1.service` and `qrh-proof-runner@2.service`.
Each slot has its own identity, disk, container and supervisor lock. User lingering
is required for operation after logout or reboot. Keep the previous host runner disabled. The
admission workflow routing takes effect after this change reaches the default
branch because admission uses `pull_request_target` and the trusted workflow SHA.

## Operations

```sh
journalctl --user -u 'qrh-proof-runner@*.service' -f
python3 infra/actions-runner/manage.py stop
python3 -m unittest discover -s infra/actions-runner -p 'test_*.py'
```

After a failure, inspect the journal, refresh credentials if needed, and run
`manage.py start`. Start, stop and status address both slots by default; append
`--slot 1` or `--slot 2` to select one. `manage.py register --slot 1` can prepare
one identity before startup. Each slot's supervisor lock and pending identity
live under the private `proof/slot-1/` or `proof/slot-2/` state directory.
Admins can remove unused offline registrations in GitHub settings.

For image updates, stop both slots, update version/checksum pins and rebuild.
Remove only `qrh-proof-proxy` to pick up a changed proxy image, then restart.
Runner automatic updates are disabled; follow
[GitHub's update requirements](https://docs.github.com/en/actions/reference/runners/self-hosted-runners).
Keep the guest Node version, toolcache and admission workflow in sync for native
fetch proxy support. Keep the Palomar smoke-test pin aligned with the verifier.
