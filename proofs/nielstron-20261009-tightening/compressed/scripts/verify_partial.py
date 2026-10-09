#!/usr/bin/env python3
"""Audit the partial development; always report that final targets are missing.
This script is not a completion certificate. The separate final gate must pass
before anyone can claim the complete mathematical task is finished.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess
R=Path(__file__).resolve().parents[1];os.chdir(R)
lean=R/'toolchains/lean-4.34.1-linux/bin/lean';env=os.environ.copy();env['LEAN_PATH']=str(R/'build/source')
allowed={'propext','Classical.choice','Quot.sound'};results={}
for line in (R/'audit/frozen-targets.sha256').read_text().splitlines():
 digest,path=line.split('  ',1);assert hashlib.sha256((R/path).read_bytes()).hexdigest()==digest
for stem in ['CheckedArithmeticAxioms','PlainReflectionAxioms','ZetaTransferAxioms','StatementParityAxioms']:
 log=R/'logs'/f'{stem}.log'
 with log.open('w') as f:
  rc=subprocess.run([str(lean),'-j1',str(R/'audit'/f'{stem}.lean')],env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 s=log.read_text();groups=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)
 groups += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",s)]
 assert rc==0,(stem,rc)
 expected=re.findall(r'^#print axioms (\S+)',(R/'audit'/f'{stem}.lean').read_text(),re.M)
 assert {n for n,_ in groups}==set(expected),(stem,expected,groups)
 for n,ax in groups:
  axioms={x.strip() for x in ax.split(',') if x.strip()};assert axioms<=allowed,(n,axioms)
 results[stem]={'exit_code':rc,'declarations':len(groups),'allowed_only':True}
log=R/'logs/final-targets-required.log'
with log.open('w') as f:
 rc=subprocess.run([str(lean),'-j1',str(R/'audit/FinalTargetsRequired.lean')],env=env,stdout=f,stderr=subprocess.STDOUT).returncode
results['final_targets']={'exit_code':rc,'status':'UNPROVED' if rc else 'REQUIRES_FINAL_REVIEW',
 'required_declarations':['QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re',
 'QRH.riemannZeta_ne_zero_of_theta_lt_re','QRH.Hecke.LFunction_ne_zero_of_theta_lt_re']}
results['partial_checks_passed']=True
results['task_complete']=False
(R/'audit/partial-verification.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
