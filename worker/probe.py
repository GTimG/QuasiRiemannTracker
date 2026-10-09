"""Trusted preflight. Never emits a proof acceptance or candidate-authored receipt."""
import ctypes, errno, os, pathlib, socket, subprocess, sys, tempfile
assert sys.platform == 'linux' and os.geteuid() != 0, 'Must be unprivileged Linux'
assert ctypes.CDLL(None, use_errno=True).syscall(444, 0, 0, 1) >= 6, 'Landlock ABI >= 6 required (IPC/signal isolation)'
for family in (socket.AF_UNIX, socket.AF_INET, socket.AF_INET6):
    try:
        s = socket.socket(family, socket.SOCK_STREAM)
    except OSError:
        pass
    else:
        s.close()
        raise RuntimeError('Socket restriction absent')
status=pathlib.Path('/proc/self/status').read_text()
fields=dict(line.split(':',1) for line in status.splitlines() if ':' in line)
assert int(fields['CapEff'].strip(),16)==0 and fields['NoNewPrivs'].strip()=='1', 'Privilege restrictions absent'
cgroup=pathlib.Path('/sys/fs/cgroup')
assert int((cgroup/'memory.max').read_text()) <= 24*1024**3, 'Memory limit not enforced'
assert int((cgroup/'memory.swap.max').read_text()) == 0, 'Swap must be disabled'
assert int((cgroup/'pids.max').read_text()) <= 256, 'PID limit not enforced'
quota,period=(cgroup/'cpu.max').read_text().split()
assert quota!='max' and int(quota)<=4*int(period), 'CPU quota not enforced'
assert not pathlib.Path('/var/run/docker.sock').exists()
assert not pathlib.Path('/root/.ssh').exists()
assert not any(k.endswith('_TOKEN') or k.endswith('_KEY') or k.startswith('ACTIONS_') for k in os.environ)
# Prove the actual landrun binary prevents writes outside its allowed private .lake.
with tempfile.TemporaryDirectory(dir='/work') as d:
    p = pathlib.Path(d)
    (p/'outside').write_text('original')
    (p/'cache').mkdir()
    args = ['/opt/bin/landrun','--best-effort','--ro','/','--rw','/dev','-ldd','-add-exec','--rwx',str(p/'cache'),'--','/usr/bin/python3','-c',f"open({str(p/'outside')!r}, 'w').write('tampered')"]
    r = subprocess.run(args, capture_output=True)
    assert r.returncode != 0 and (p/'outside').read_text() == 'original', 'Filesystem isolation failed'
    # Signal 0 checks permission without killing the orchestrator.
    args[-1] = f'import os; os.kill({os.getpid()},0)'
    assert subprocess.run(args,capture_output=True).returncode != 0, 'Signal isolation failed'
    args[-1] = f"open({str(p/'cache'/'allowed')!r}, 'w').write('allowed')"
    assert subprocess.run(args,capture_output=True).returncode == 0, 'Sandbox cannot run permitted work'
print('Isolation probes passed', flush=True)
