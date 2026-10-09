#!/usr/bin/env python3
"""Fail-closed verification of the three exact final targets after a source build.
No placeholders, model invocation, external caches, or credential access.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess
R=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
names=['QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re',
       'QRH.riemannZeta_ne_zero_of_theta_lt_re','QRH.Hecke.LFunction_ne_zero_of_theta_lt_re']
for line in (R/'audit/frozen-targets.sha256').read_text().splitlines():
 digest,path=line.split('  ',1);assert sha(R/path)==digest,path
status=json.loads((R/'audit/source-build-status.json').read_text())
assert status['success'] and not status['failed'] and not status['blocked']
assert {'QRH','QRH.Analytic'}<=set(status['roots'])
graph=json.loads((R/'audit/selected-source-graph.json').read_text())
assert status['checked']==status['closure']==len(graph)
keys={}
def check(m):
 if m in keys:return keys[m]
 item=graph[m];assert sha(R/item['source'])==item['sha256'],m
 key=hashlib.sha256((item['sha256']+''.join(check(d) for d in item['imports'])+
 'lean-4.34.1-package-options-v2-j1'+('mathlib-maxSynthPendingDepth=3' if m.startswith('Mathlib.') else '')+
 ('autoImplicit=false' if m.startswith(('RellichKondrachov.','MathlibExtensions.','PrimeNumberTheoremAnd.')) else '')).encode()).hexdigest()
 out=R/'build/source'/Path(*m.split('.')).with_suffix('.olean')
 assert out.is_file() and out.with_suffix('.source-key').read_text()==key,m
 with (R/'logs/source'/(m+'.log')).open() as f:header=json.loads(f.readline())
 assert header['key']==key and header['source_sha256']==item['sha256'],m
 assert '-j1' in header['command'],m
 keys[m]=key;return key
for m in graph:check(m)
for line in (R/'audit/checked-energy-increments.jsonl').read_text().splitlines():
 record=json.loads(line);assert sha(R/record['source'])==record['sha256'],record['module']
lean=R/'toolchains/lean-4.34.1-linux/bin/lean'
env=os.environ.copy();env['LEAN_PATH']=str(R/'build/source')
log=R/'logs/final-targets-required.log'
with log.open('w') as f:
 rc=subprocess.run([str(lean),'-j1',str(R/'audit/FinalTargetsRequired.lean')],env=env,stdout=f,stderr=subprocess.STDOUT).returncode
assert rc==0,log
s=log.read_text()
groups=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)
groups += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",s)]
assert {n for n,_ in groups}==set(names),s
axioms={n:sorted(a.strip() for a in ax.split(',') if a.strip()) for n,ax in groups}
assert all(set(ax)<=allowed for ax in axioms.values()),axioms
# This existing audit verifies immutable inputs, all pins/notices, definition Git blobs,
# selected source hashes, and applicable Apache owners. It cannot itself prove a theorem.
provenance=subprocess.run(['python3',str(R/'scripts/audit_sources.py')],cwd=R,capture_output=True,text=True)
(R/'logs/final-source-provenance.log').write_text(provenance.stdout+provenance.stderr)
assert provenance.returncode==0,'logs/final-source-provenance.log'
result={'status':'PASS','exact_three_targets_proved':True,'threshold':'874957019421/1000000000000',
 'declarations':axioms,'independent_literal_specifications':'formalization/QRH/IndependentTargets.lean',
 'specification_hash_manifest_sha256':sha(R/'audit/frozen-targets.sha256'),
 'parity_and_axiom_gate':'audit/FinalTargetsRequired.lean','gate_exit_code':rc,
 'source_build':status,'source_graph_sha256':sha(R/'audit/selected-source-graph.json'),
 'source_and_dependency_keys_rechecked':len(keys),'per_module_compiler_logs_matched':len(keys),
 'provenance_rechecked':True,'source':'formalization/QRH/Nonvanishing.lean',
 'source_sha256':sha(R/'formalization/QRH/Nonvanishing.lean'),
 'scope_note':'Proves the three requested nonvanishing targets by the shortest analytic route. Does not separately state every manuscript lemma or optional optimality result.'}
(R/'audit/final-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
