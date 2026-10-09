from pathlib import Path
import os, sys
import concurrent.futures,hashlib,json,os,re,socket,subprocess,time
assert sys.platform == 'linux', 'Linux with bubblewrap is required'
P=Path(os.environ['QRH_PROOF_ROOT']).resolve();R=Path(os.environ['QRH_CHECKER_ROOT']).resolve();B=R/'baseline-build'
B.mkdir(exist_ok=True);out=B/'lib';out.mkdir(exist_ok=True);logs=B/'logs';logs.mkdir(exist_ok=True)
roots=[P/'upstream/openai-math/lean',P/'formalization']+sorted((P/'formalization/.lake/packages').iterdir())
lean=P/'toolchains/lean-4.34.1-linux/bin/lean';base=lean.parent.parent/'lib/lean';cache=P/'build/source'
known=json.loads((P/'audit/final-source-graph.json').read_text()); graph={}
def clean(s):
 result=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if depth:result.append('\n' if s[i]=='\n' else ' ');i+=1;continue
  if s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  result.append(s[i]);i+=1
 return ''.join(result)
def visit(m):
 if m in graph:return
 rel=Path(*m.split('.'))
 if m in known and (cache/rel.with_suffix('.olean')).exists():
  assert hashlib.sha256((P/known[m]['source']).read_bytes()).hexdigest()==known[m]['sha256'],m
  return
 if (base/rel.with_suffix('.olean')).exists():return
 for root in roots:
  f=(root/rel).with_suffix('.lean')
  if f.exists():break
 else:raise RuntimeError('missing source '+m)
 deps=[]
 for line in clean(f.read_text()).splitlines():
  match=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
  if match:deps += [x for x in match[1].split() if x!='all']
  elif line.strip() and line.strip() not in ('module','prelude'):break
 graph[m]=(root,f,deps)
 for d in deps:visit(d)
for target in ['OAI.NumberTheory.DirichletL.Nonvanishing','OAI.NumberTheory.DirichletL.Hecke.Nonvanishing']:visit(target)
# Lean chooses the first matching top-level namespace directory, so build a
# complete read-only symlink overlay rather than shadowing the approved cache.
for m in known:
 if m in graph:continue
 rel=Path(*m.split('.'))
 for ext in ['.olean','.ilean','.olean.private','.olean.server','.ir','.ir.sig']:
  src=cache/(str(rel)+ext);dst=out/(str(rel)+ext)
  if src.is_file() and not dst.exists():
   dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src)
print('additional source modules',len(graph),flush=True)
(B/'graph.json').write_text(json.dumps({m:{'source':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'imports':d} for m,(r,f,d) in graph.items()},indent=2))
env={'PATH':str(lean.parent)+':/usr/bin:/bin','HOME':str(R/'home'),'TMPDIR':str(B),'LEAN_PATH':str(out)+':'+str(cache),'LEAN_NUM_THREADS':'1'}
done=set();pending=set(graph);active={};failed=[];started=time.time()
def compile_one(m):
 root,f,deps=graph[m];output=(out/Path(*m.split('.'))).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(lean),'-j1','-DautoImplicit=false','-o',str(output),str(f.relative_to(root))]
 with (logs/(m+'.log')).open('w') as log:return subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=1800).returncode
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 while pending or active:
  for m in sorted(pending):
   if len(active)>=4:break
   if not all(d not in graph or d in done for d in graph[m][2]):continue
   pending.remove(m);active[pool.submit(compile_one,m)]=m
  if not active:break
  ready,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in ready:
   m=active.pop(f)
   if f.result():failed.append(m)
   else:done.add(m)
  status={'compiled':len(done),'additional_modules':len(graph),'failed':failed,'blocked':len(pending),'seconds':time.time()-started,'status':'running' if not failed else 'failed'}
  (B/'status.json').write_text(json.dumps(status));print(json.dumps(status),flush=True)
status={'compiled':len(done),'additional_modules':len(graph),'failed':failed,'blocked':sorted(pending),'seconds':time.time()-started,'status':'PASS' if not failed and not pending else 'failed'}
(B/'status.json').write_text(json.dumps(status));print(json.dumps(status),flush=True)
if status['status']!='PASS':raise SystemExit(1)
