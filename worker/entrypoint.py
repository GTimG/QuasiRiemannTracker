import json, os, pathlib, shutil, subprocess, sys
# Everything in this script is baked into the maintainer-built image.
subprocess.run(['/usr/bin/python3','/opt/qrh/worker/probe.py'],check=True)
if sys.argv[1:] == ['probe']:
    sys.exit(0)
base=pathlib.Path('/opt/project'); work=pathlib.Path('/work/project')
shutil.copytree(base,work,symlinks=False)
# No PR lakefile, binary, cache, environment, or configuration is used.
shutil.copy('/input/Challenge.lean',work/'Challenge.lean')
shutil.copy('/input/Solution.lean',work/'Solution.lean')
shutil.copytree('/input/src/Candidate',work/'Candidate')
os.chdir(work)
env={'PATH':'/opt/lean/bin:/opt/bin:/usr/bin:/bin','HOME':'/tmp','TMPDIR':'/tmp','LEAN_ABORT_ON_PANIC':'1','COMPARATOR_LANDRUN':'/opt/bin/landrun','COMPARATOR_LEAN4EXPORT':'/opt/bin/lean4export','COMPARATOR_NANODA':'/opt/bin/nanoda_bin'}
# Comparator extracts Challenge before compiling any adversarial Candidate module.
# The final exit status is Comparator's; candidate stdout is never interpreted as acceptance.
os.execve('/opt/lean/bin/lake',['lake','env','/opt/bin/comparator','/input/comparator.json'],env)
