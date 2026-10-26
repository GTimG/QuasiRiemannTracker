"""Execute the protected replay and classify failures from supervisor telemetry."""
from pathlib import Path
import json, os, runpy, subprocess, sys, traceback
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'verification'
context = json.loads((ROOT/'verification-context/context.json').read_text())
identity = context['expected']
def save(status, reason=None, report=None):
    (OUT/'attempt.json').write_text(json.dumps({**identity,'status':status,'reason':reason,'report':report},indent=2)+'\n')
save('checking', 'Proof verification did not complete')
profile = json.loads((OUT/'profile.json').read_text())
sys.path.insert(0,profile['palomar'])
from scripts.verify_submission import ResourceExhausted
# The orchestration needs the user bus for delegated cgroups. Candidate phases
# receive the separate minimal environment constructed by replay.py.
for key in list(os.environ):
    if key not in ['PATH','HOME','LANG','XDG_RUNTIME_DIR','DBUS_SESSION_BUS_ADDRESS','QRH_WORKER_THREADS','QRH_KERNEL_JOBS','QRH_REPLAY_BUDGET_SECONDS']:
        del os.environ[key]
sys.argv = ['replay.py','--profile',str(OUT/'profile.json'),'--prepared',str(OUT/'prepared'),
            '--work',str(OUT/'run'),'--tool-pins',str(OUT/'tool-pins.json')]
try:
    runpy.run_path(str(ROOT/'verifier/standard/replay.py'),run_name='__main__')
    report = json.loads((OUT/'run/result.json').read_text())
    save('accepted',report=report)
except BaseException as error:
    if isinstance(error,(ResourceExhausted,subprocess.TimeoutExpired)):
        status = 'resource-exhausted'
    elif getattr(error,'owner',None) == 'provider':
        status = 'infrastructure-blocked'
    else:
        status = 'checking-failed'
    save(status,str(error)[-4000:])
    traceback.print_exc()
    sys.exit(1)
