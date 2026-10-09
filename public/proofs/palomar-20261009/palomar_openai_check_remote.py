"""Run Palomar's exported-proof judge against the original pinned OpenAI proof, on Linux verification worker.
This is a local mechanical check, not a registry submission or editorial review.
The proof is built with its original compiler and exported with its matching exporter.
The judge and all three kernels come from Palomar's current minimum toolchain.
"""
from pathlib import Path
import os, sys
import datetime,hashlib,json,os,socket,subprocess,sys,time,traceback
assert sys.platform == 'linux', 'Linux with bubblewrap is required'
R=Path(os.environ['QRH_CHECKER_ROOT']).resolve(); P=Path(os.environ['QRH_PROOF_ROOT']).resolve()
J=R/'tools/lean-4.35.0-rc2-linux'; OLD=P/'toolchains/lean-4.34.1-linux'
REF=R/'tools/palomar'; W=R/'runs/openai'; W.mkdir(parents=True,exist_ok=False)
def status(phase,**extra):
 report={'phase':phase,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**extra}
 (R/'baseline-check-status.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
def digest(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
try:
 status('fetch-palomar-verifier',status='running')
 if not REF.exists():
  subprocess.run(['git','init',str(REF)],check=True)
  subprocess.run(['git','-C',str(REF),'fetch','--depth','1','https://github.com/PalomarRegistry/PalomarSubmission.git','d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44'],check=True)
  subprocess.run(['git','-C',str(REF),'checkout','--detach','FETCH_HEAD'],check=True)
 sys.path.insert(0,str(REF))
 from scripts import verify_submission as v
 v._BWRAP=Path('/usr/bin/bwrap')
 # Task-specific resource ceilings, stricter than the stock percentages on this large host.
 v.VERIFICATION_LIMITS={**v.VERIFICATION_LIMITS,'memory_high_percent':6,'memory_max_percent':8,'tasks_max':512,'open_files_max':65536,'file_size_max_bytes':64*1024**3}
 v.install_execution_deadline(budget_seconds=10800)
 bundled={n:J/'bin'/n for n in v.TOOLCHAIN_TOOLS}
 oldexport=R/'tools/lean4export/.lake/build/bin/lean4export'
 tools=v.tool_snapshot([*bundled.values(),v._BWRAP,OLD/'bin/lean',oldexport])
 env={'PATH':str(J/'bin')+':/usr/bin:/bin','HOME':str(R/'home'),'TMPDIR':str(W),'LANG':'C.UTF-8','LEAN_ABORT_ON_PANIC':'1'}
 kernels=v.protected_kernels(bundled)
 primitives=v.primitive_targets(J)
 pins=json.loads((R/'pins.json').read_text());pins['binaries']=v.tool_digests(bundled,v._BWRAP);pins['proof_exporter_sha256']=digest(oldexport)
 (W/'tool-pins.json').write_text(json.dumps(pins,indent=2))
 status('palomar-positive-and-negative-preflight',status='running')
 v.comparator_preflight(W,lean=bundled['lean'],leanexport=bundled['leanexport'],lake=bundled['lake'],lean_prefix=J,bwrap=v._BWRAP,kernels=kernels,primitives=primitives,environment=env,executable_paths=[J,v._BWRAP,Path('/usr')],tools=tools,timeout=300)
 status('palomar-preflight-passed',status='running')
 for d in ['src','lib','exports','home','tmp']:(W/d).mkdir()
 statement='''namespace QRHPalomar
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  DIRICHLET_PROOF

theorem zeta {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  ZETA_PROOF

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  HECKE_PROOF
end QRHPalomar
'''
 challenge='import Mathlib.NumberTheory.LSeries.DirichletContinuation\nimport OAI.NumberTheory.DirichletL.Hecke.IdealBridge\n\n'+statement.replace('DIRICHLET_PROOF','sorry').replace('ZETA_PROOF','sorry').replace('HECKE_PROOF','sorry')
 solution='import OAI.NumberTheory.DirichletL.Nonvanishing\nimport OAI.NumberTheory.DirichletL.Hecke.Nonvanishing\n\n'+statement.replace('DIRICHLET_PROOF','exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole').replace('ZETA_PROOF','exact OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs').replace('HECKE_PROOF','apply OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re χ hs\n  intro h\n  rcases hpole with hne | hne\n  · exact hne h.2\n  · exact hne h.1')
 for name,source in [('Challenge',challenge),('Solution',solution)]: (W/'src'/f'{name}.lean').write_text(source)
 names=['QRHPalomar.allDirichlet','QRHPalomar.zeta','QRHPalomar.allHecke']
 config={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':names,'definition_names':[],'permitted_axioms':sorted(v.STANDARD_AXIOMS),'external_kernels':kernels}
 (W/'comparator.json').write_text(json.dumps(config,indent=2))
 targets=v.comparator_export_targets(config,primitives)
 env={**env,'PATH':str(OLD/'bin')+':/usr/bin:/bin','HOME':str(W/'home'),'TMPDIR':str(W/'tmp'),'LEAN_PATH':str(W/'lib')+':'+str(R/'baseline-build/lib')+':'+str(P/'build/source')+':'+str(OLD/'lib/lean')}
 for name in ['Challenge','Solution']:
  status('compile-'+name,status='running')
  proc=v.sandboxed_run([str(OLD/'bin/lean'),'-j1','-o',str(W/'lib'/f'{name}.olean'),str(W/'src'/f'{name}.lean')],cwd=W,environment=env,writable_directories=[W/'lib',W/'home',W/'tmp'],readable_paths=[W/'src',R/'baseline-build/lib',P/'build/source',*v.system_readable_paths()],executable_paths=[OLD,Path('/usr')],tools=tools,timeout=600)
  (W/f'{name}-compile.log').write_text(proc.stdout+'\n'+proc.stderr)
  status('export-'+name,status='running')
  proc=v.export_module(name,targets,output=W/'exports'/f'{name}.export',leanexport=oldexport,cwd=W,environment=env,readable_paths=[W/'lib',R/'baseline-build/lib',P/'build/source',*v.system_readable_paths()],executable_paths=[OLD,oldexport,Path('/usr')],tools=tools,timeout=1800)
  (W/f'{name}-export.log').write_text(proc.stdout+'\n'+proc.stderr)
  if proc.returncode:raise RuntimeError(f'{name} export failed: '+proc.stderr[-2000:])
  v.verify_export(W/'exports'/f'{name}.export')
 status('comparator-and-three-kernels',status='running',exports={n:(W/'exports'/f'{n}.export').stat().st_size for n in ['Challenge','Solution']})
 proc=v.judge_exports(lake=bundled['lake'],config=W/'comparator.json',challenge_export=W/'exports/Challenge.export',solution_export=W/'exports/Solution.export',scratch=W/'judge',bwrap=v._BWRAP,lean_prefix=J,environment=env,tools=tools,timeout=7200)
 log=proc.stdout+'\n'+proc.stderr;(W/'judge.log').write_text(log)
 verdict=v.comparator_verdict(proc.returncode,log)
 if verdict:raise verdict
 assert 'Your solution is okay!' in log,log[-2000:]
 result={'status':'PASS','kind':'local Palomar mechanical judge; not Palomar registration','declarations':names,'theta':'7/8','kernels':['Lean default','nanoda','con-ron'],'palomar_preflight':'passed','statement_definitions_compared':True,'allowed_axioms':config['permitted_axioms'],'source_compiler':'4.34.1','judge_toolchain':'4.35.0-rc2','proof_source_sha256':digest(P/'upstream/openai-math/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean'),'artifacts':{str(x.relative_to(W)):digest(x) for x in [W/'src/Challenge.lean',W/'src/Solution.lean',W/'exports/Challenge.export',W/'exports/Solution.export',W/'comparator.json',W/'judge.log']},'registration_limits':['Source compiler is older than Palomar current submission floor; export compatibility tested by the judge.','Hecke statement imports pinned OpenAI definitions outside Palomar current Challenge import allowlist.','No Palomar editorial review or registry submission performed.']}
 (W/'result.json').write_text(json.dumps(result,indent=2));status('finished',status='PASS',result=str(W/'result.json'))
except Exception as e:
 status('stopped',status='failed',error=str(e),error_type=type(e).__name__)
 traceback.print_exc();raise
