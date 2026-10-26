import test from "node:test";
import { execFileSync } from "node:child_process";

test("replay keeps the hosted deadline by default and bounds explicit budgets", () => {
  execFileSync(
    "python3",
    [
      "-c",
      String.raw`
from verifier.worker_resources import replay_budget_seconds
assert replay_budget_seconds({}) == 10800
for value in ['1', '10800', '21600', '43200']:
    assert replay_budget_seconds({'QRH_REPLAY_BUDGET_SECONDS': value}) == int(value)
for value in ['', '0', '-1', '43201', '999999', '1.5', 'inf', '1e4', ' 3600', '3600\n', '١']:
    try:
        replay_budget_seconds({'QRH_REPLAY_BUDGET_SECONDS': value})
    except ValueError as error:
        assert 'QRH_REPLAY_BUDGET_SECONDS' in str(error)
    else:
        raise AssertionError('Accepted invalid replay budget: '+repr(value))
`,
    ],
    { stdio: "pipe" },
  );
});

test("the worker forwards replay limits while removing credentials and records invalid budgets", () => {
  execFileSync(
    "python3",
    [
      "-c",
      String.raw`
from pathlib import Path
from tempfile import TemporaryDirectory
import json, os, shutil, subprocess

source = Path.cwd()
with TemporaryDirectory() as temporary:
    root = Path(temporary)
    actions = root/'verifier/actions'
    actions.mkdir(parents=True)
    shutil.copyfile(source/'verifier/actions/run.py', actions/'run.py')
    output = root/'verification'
    output.mkdir()
    context = root/'verification-context'
    context.mkdir()
    (context/'context.json').write_text(json.dumps({'expected': {'head_sha': 'a'*40}}))
    palomar = root/'palomar'
    (palomar/'scripts').mkdir(parents=True)
    (palomar/'scripts/__init__.py').write_text('')
    (palomar/'scripts/verify_submission.py').write_text('class ResourceExhausted(Exception): pass\n')
    (output/'profile.json').write_text(json.dumps({'palomar': str(palomar)}))
    standard = root/'verifier/standard'
    standard.mkdir()
    (standard/'replay.py').write_text(f'''
from pathlib import Path
import json, os, sys
sys.path.insert(0, {str(source/'verifier')!r})
from worker_resources import replay_budget_seconds
assert 'GITHUB_TOKEN' not in os.environ
assert 'UNRELATED_SECRET' not in os.environ
report = {{'budget_seconds': replay_budget_seconds(),
           'threads': os.environ.get('QRH_WORKER_THREADS'),
           'kernels': os.environ.get('QRH_KERNEL_JOBS')}}
work = Path({str(output/'run')!r})
work.mkdir(exist_ok=True)
(work/'result.json').write_text(json.dumps(report))
''')
    for budget in [None, '43200', '43201']:
        environment = {**os.environ, 'GITHUB_TOKEN': 'test-credential',
                       'UNRELATED_SECRET': 'test-credential',
                       'QRH_WORKER_THREADS': '6', 'QRH_KERNEL_JOBS': '1'}
        environment.pop('QRH_REPLAY_BUDGET_SECONDS', None)
        if budget is not None:
            environment['QRH_REPLAY_BUDGET_SECONDS'] = budget
        result = subprocess.run(['python3', str(actions/'run.py')],
                                env=environment, capture_output=True, text=True)
        attempt = json.loads((output/'attempt.json').read_text())
        if budget == '43201':
            assert result.returncode != 0
            assert attempt['status'] == 'checking-failed', attempt
            assert 'QRH_REPLAY_BUDGET_SECONDS' in attempt['reason'], attempt
            assert attempt['report'] is None, attempt
        else:
            assert result.returncode == 0, result.stderr
            assert attempt['status'] == 'accepted', attempt
            assert attempt['report'] == {'budget_seconds': int(budget or '10800'),
                                         'threads': '6', 'kernels': '1'}, attempt
`,
    ],
    { stdio: "pipe" },
  );
});
