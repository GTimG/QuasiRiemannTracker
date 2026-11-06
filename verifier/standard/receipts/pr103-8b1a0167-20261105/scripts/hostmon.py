"""Host monitor: sample loadavg/swap/lean-RSS every 120s for the build receipt."""
import subprocess
import time

def line():
    ts = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    load = subprocess.run(["sysctl", "-n", "vm.loadavg"], capture_output=True, text=True).stdout.strip()
    swap = subprocess.run(["sysctl", "-n", "vm.swapusage"], capture_output=True, text=True).stdout.strip()
    ps = subprocess.run(["ps", "-axo", "rss,comm"], capture_output=True, text=True).stdout
    lean = []
    for f in ps.splitlines():
        parts = f.split(maxsplit=1)
        if len(parts) == 2 and ("lean" in parts[1] or "lake" in parts[1]):
            try:
                lean.append(int(parts[0]))
            except ValueError:
                pass
    return f"{ts} load={load} swap=[{swap}] lean_procs={len(lean)} lean_rss_mb={sum(lean)//1024}\n"

with open("/tmp/qr_rebuild/hostmon.log", "a") as log:
    while True:
        try:
            log.write(line())
            log.flush()
        except Exception as e:  # keep the monitor alive no matter what
            log.write(f"sample-error {e}\n")
            log.flush()
        time.sleep(120)
