"""Choose replay limits within the worker's time, CPU and memory allocation."""
from pathlib import Path
import os

GIB = 1024 ** 3


def replay_budget_seconds(environ=None):
    environ = os.environ if environ is None else environ
    value = environ.get('QRH_REPLAY_BUDGET_SECONDS', '10800')
    if (not value.isascii() or not value.isdecimal()
            or not 1 <= int(value) <= 43200):
        raise ValueError('QRH_REPLAY_BUDGET_SECONDS must be an integer from 1 to 43200')
    return int(value)


def worker_capacity(*, environ=None, affinity=None, memory_bytes=None,
                   cgroup_root=Path('/sys/fs/cgroup'),
                   membership=Path('/proc/self/cgroup')):
    environ = os.environ if environ is None else environ
    if affinity is None:
        affinity = len(os.sched_getaffinity(0))
    if memory_bytes is None:
        memory_bytes = os.sysconf('SC_PHYS_PAGES') * os.sysconf('SC_PAGE_SIZE')
    cpus = max(1, affinity)
    root = cgroup_root.resolve()
    directories = [root]
    if membership.exists():
        for line in membership.read_text().splitlines():
            if line.startswith('0::'):
                current = (root / line[3:].lstrip('/')).resolve()
                if current.is_relative_to(root):
                    while current != root:
                        directories.append(current)
                        current = current.parent
    # Ancestor limits also constrain delegated runner/job cgroups.
    for directory in directories:
        cpu_limit, memory_limit = directory/'cpu.max', directory/'memory.max'
        if cpu_limit.exists():
            quota, period = cpu_limit.read_text().split()
            if quota != 'max':
                cpus = min(cpus, max(1, int(quota) // int(period)))
        if memory_limit.exists():
            value = memory_limit.read_text().strip()
            if value != 'max':
                memory_bytes = min(memory_bytes, int(value))
    # Budget 2 GiB per thread within 75% of allocated RAM. The sandbox retains
    # its separate hard memory/task limits for each verification phase.
    threads = max(1, min(cpus, memory_bytes * 3 // 4 // (2 * GIB)))
    requested = environ.get('QRH_WORKER_THREADS')
    if requested is not None:
        if not requested.isascii() or not requested.isdecimal() or int(requested) < 1:
            raise ValueError('QRH_WORKER_THREADS must be a positive integer')
        threads = min(threads, int(requested))
    # Large exports can need several GiB in each independent checker.
    kernels = max(1, min(3, threads, memory_bytes * 3 // 4 // (8 * GIB)))
    requested_kernels = environ.get('QRH_KERNEL_JOBS')
    if requested_kernels is not None:
        if requested_kernels not in ['1', '2', '3']:
            raise ValueError('QRH_KERNEL_JOBS must be 1, 2 or 3')
        kernels = min(int(requested_kernels), threads)
    return {'threads': threads, 'kernel_jobs': kernels, 'memory_bytes': memory_bytes}


def worker_threads(**kwargs):
    return worker_capacity(**kwargs)['threads']
