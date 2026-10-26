import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";

test("concurrent kernels join every verdict and preserve rejection and resource errors", () => {
  const result = spawnSync(
    "python3",
    [
      "-c",
      `
from pathlib import Path
import json, subprocess, sys, tempfile, threading
sys.path.insert(0,'verifier')
from standard.judge import collect_checks, judge_exports
with tempfile.TemporaryDirectory() as temporary:
    root=Path(temporary)
    barrier=threading.Barrier(3, timeout=5)
    def accepted():
        barrier.wait()
        return subprocess.CompletedProcess([],0,'accepted','')
    checks={name:accepted for name in ['Lean default','nanoda','con-ron']}
    assert collect_checks(checks,workers=3,logs=root/'parallel').returncode==0
    class ResourceError(Exception): pass
    def exhausted(): raise ResourceError('out of memory')
    def rejected(): return subprocess.CompletedProcess([],1,'','ill-typed proof')
    result=collect_checks({'nanoda':exhausted,'Lean default':rejected},workers=2,logs=root/'rejected')
    assert result.returncode!=0 and 'ill-typed proof' in result.stderr
    try:
        collect_checks({'nanoda':exhausted},workers=1,logs=root/'exhausted')
    except ResourceError: pass
    else: raise AssertionError('Resource exhaustion was accepted')

    config=root/'comparator.json'
    config.write_text(json.dumps({'theorem_names':['QRH.canonical_bound'],
        'permitted_axioms':['propext','Quot.sound','Classical.choice'],
        'external_kernels':{'nanoda':['nanoda_bin'],'con-ron':['con-ron','--jobs=2']}}))
    challenge=root/'Challenge.export'; challenge.write_text('challenge')
    solution=root/'Solution.export'; solution.write_text('solution')
    class Verifier:
        VERIFICATION_LIMITS={'memory_high_percent':75,'memory_max_percent':85,'tasks_max':256}
        _BWRAP=root/'bwrap'
        def protected_kernels(self,tools):
            return {'nanoda':[str(tools['nanoda_bin'])], 'con-ron':[str(tools['con-ron']),'--jobs=2']}
        def system_readable_paths(self): return []
        def judge_exports(self,**kwargs):
            assert kwargs['timeout']==600
            assert kwargs['challenge_export']==challenge
            assert kwargs['solution_export']==solution
            cfg=json.loads(kwargs['config'].read_text())
            assert cfg['external_kernels']=={}
            assert cfg['theorem_names']==['QRH.canonical_bound']
            assert cfg['permitted_axioms']==json.loads(config.read_text())['permitted_axioms']
            assert self.VERIFICATION_LIMITS['memory_max_percent']==28
            barrier.wait()
            return subprocess.CompletedProcess([],0,'Your solution is okay!\\nLean default kernel accepts the solution','')
        def sandboxed_run(self,command,**kwargs):
            assert kwargs['timeout']==600
            assert Path('/usr') in kwargs['executable_paths']  # ELF loader and system libraries
            assert solution in kwargs['readable_paths']
            assert solution not in kwargs['writable_directories']
            assert kwargs['writable_directories']==[kwargs['cwd']]
            assert kwargs['check'] is False
            assert self.VERIFICATION_LIMITS['memory_high_percent']==25
            if command[0].endswith('nanoda_bin'):
                cfg=json.loads(Path(command[-1]).read_text())
                assert cfg['export_file_path']==str(solution)
                assert cfg['permitted_axioms']==json.loads(config.read_text())['permitted_axioms']
                assert cfg['num_threads']==1
            else:
                assert command[-1]==str(solution) and '--jobs=1' in command
            barrier.wait()
            return subprocess.CompletedProcess(command,0,'kernel output','')
    verifier=Verifier()
    bundled={x:root/x for x in ['lake','nanoda_bin','con-ron']}
    result=judge_exports(verifier,config=config,challenge_export=challenge,
        solution_export=solution,scratch=root/'judge',bundled=bundled,
        lean_prefix=root,environment={},tools={},capacity={'kernel_jobs':3,'threads':4},timeout=600)
    assert result.returncode==0
    assert all(name+' kernel accepts the solution' in result.stdout for name in checks)
    assert verifier.VERIFICATION_LIMITS['memory_max_percent']==85

    # Serial Comparator runs all three checkers under one process allowance.
    class SerialVerifier(Verifier):
        expired=False
        def judge_exports(self,**kwargs):
            assert kwargs['timeout']==1800
            assert kwargs['config']==config
            assert kwargs['challenge_export']==challenge
            assert kwargs['solution_export']==solution
            assert self.VERIFICATION_LIMITS['memory_max_percent']==85
            if self.expired:
                # The protected verifier still enforces its shared deadline.
                raise subprocess.TimeoutExpired(['lake','comparator'],123)
            return subprocess.CompletedProcess([],0,'all three kernels accepted','')
    serial=SerialVerifier()
    kwargs=dict(config=config,challenge_export=challenge,solution_export=solution,
        scratch=root/'serial',bundled=bundled,lean_prefix=root,environment={},tools={},
        capacity={'kernel_jobs':1,'threads':12},timeout=600)
    assert judge_exports(serial,**kwargs).returncode==0
    serial.expired=True
    try:
        judge_exports(serial,**kwargs)
    except subprocess.TimeoutExpired as error:
        assert error.timeout==123
    else:
        raise AssertionError('Shared execution deadline was swallowed')
`,
    ],
    { encoding: "utf8", timeout: 20_000 },
  );
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stdout + result.stderr);
});
