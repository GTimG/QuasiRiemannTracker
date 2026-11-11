"""Exercise the live worker with a known proof, then an incomplete proof."""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, sys
root = Path(__file__).resolve().parents[1]
out = root/'verification'
if sys.argv[1] == 'prepare':
    head = subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    expected = dict(repository='GTimG/QuasiRiemannTracker',number=5,head_sha=head,result_id='classical-euler-product',theta_exact='1/1')
    (root/'verification-context').mkdir()
    (root/'verification-context/context.json').write_text(json.dumps({'expected':expected}))
    out.mkdir()
    (out/'empty-libraries.json').write_text('{}\n')
    (out/'imports.json').write_text('[]\n')
    subprocess.run(['node','verifier/standard/prepare.mjs','--checkout',str(root),'--head',head,
        '--repository',expected['repository'],'--id',expected['result_id'],'--bound',expected['theta_exact'],'--libraries',str(out/'empty-libraries.json'),
        '--out',str(out/'prepared')],check=True)
else:
    accepted = json.loads((out/'attempt.json').read_text())
    assert accepted['status'] == 'accepted', accepted
    run_url = f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}/attempts/{os.environ['GITHUB_RUN_ATTEMPT']}"
    subprocess.run(['node', 'verifier/certify-local.mjs', '--context', str(root/'verification-context/context.json'),
        '--attempt', str(out/'attempt.json'), '--report', str(out/'run/result.json'),
        '--report-url', run_url, '--out', str(out/'certificate.json')], check=True)
    certificate = json.loads((out/'certificate.json').read_text())
    assert certificate['source_commit'] == accepted['head_sha']
    assert certificate['theta_exact'] == '1/1'
    assert certificate['report_sha256'] == hashlib.sha256((out/'run/result.json').read_bytes()).hexdigest()
    assert (out/'certificate.json').stat().st_size < 2048
    # Exercise actual Lean imports from a cached source build, then mutate the
    # source below. The old compiled theorem must never mask sorryAx.
    sys.path.insert(0, str(root/'verifier'))
    from standard.build_cache import build_inputs, pack_cache, digest
    profile_path = out/'profile.json'
    profile = json.loads(profile_path.read_text())
    inputs = build_inputs(json.loads((out/'prepared/contract.json').read_text()), profile,
        json.loads((out/'prepared/libraries.json').read_text()), accepted['report']['tool_pins'])
    archive = out/'integration-build.tar.gz'
    pack_cache(out/'run/candidate-lib', archive, inputs)
    profile['candidate_cache'] = dict(shards=[dict(path=str(archive), sha256=digest(archive), url='integration-test')], signer='test-fixture')
    profile_path.write_text(json.dumps(profile))
    shutil.move(out/'run',out/'source-build-run')
    subprocess.run(['python3','verifier/actions/run.py'],check=True)
    reused = json.loads((out/'run/result.json').read_text())
    assert reused['build_cache']['modules_reused'] == len(inputs['modules'])
    shutil.move(out/'run',out/'accepted-run')
    shutil.copyfile(out/'attempt.json',out/'accepted-attempt.json')
    prepared = out/'prepared'
    # This theorem compiles with sorryAx, which the judge must reject.
    source = prepared/'submission/src/Candidate/Main.lean'
    source.chmod(0o644)
    source.write_text('import Mathlib\nnamespace Candidate\ntheorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)\n    {s : ℂ} (hs : (1 / 1 : ℝ) < s.re)\n    (hpole : ¬ (χ = 1 ∧ s = 1)) :\n    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by\n  sorry\nend Candidate\n')
    contract = json.loads((prepared/'contract.json').read_text())
    contract['source_files']['src/Candidate/Main.lean'] = hashlib.sha256(source.read_bytes()).hexdigest()
    (prepared/'contract.json').chmod(0o644)
    (prepared/'contract.json').write_text(json.dumps(contract))
    (prepared/'contract.json').chmod(0o444)
    result = subprocess.run(['python3','verifier/actions/run.py'])
    attempt = json.loads((out/'attempt.json').read_text())
    assert result.returncode != 0 and attempt['status'] == 'checking-failed', attempt
    phases = json.loads((out/'run/phases.json').read_text())
    assert phases[-1]['phase'] == 'Comparator and Lean, NanoDa, con-ron', phases
    logs = '\n'.join(p.read_text() for p in (out/'run/logs').glob('*.log'))
    # The failure must identify the forbidden axiom, after successful compilation.
    assert 'sorryAx' in logs or 'sorryAx' in attempt['reason'], attempt
    print('Known bound accepted; incomplete proof rejected by the judge for sorryAx.')
