import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
test("parallel compilation waits for dependencies and isolates published outputs", () => {
  const result = execFileSync(
    "python3",
    [
      "-c",
      String.raw`
from verifier.standard.compile import compile_modules, publish_module
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Barrier, Lock
barrier=Barrier(2);done=set();lock=Lock()
def compile(name, threads):
    if name in ['First', 'Second']: assert threads==1
    else: assert threads==2
    if name in ['First', 'Second']: barrier.wait(timeout=5)
    if name=='Main': assert done=={'First','Second'}
    with lock: done.add(name)
compile_modules(['First','Second','Main'], {'First':[], 'Second':[], 'Main':['First','Second']},compile,jobs=2)
assert done=={'First','Second','Main'}
for graph in [{'First':['Missing']}, {'First':['First']}]:
    try: compile_modules(['First'],graph,compile,jobs=1)
    except ValueError: pass
    else: raise AssertionError('invalid dependency graph accepted')
with TemporaryDirectory() as temporary:
    root=Path(temporary);out=root/'module.olean';out.write_text('compiled')
    Path(str(out)+'.private').write_text('private')
    destination=root/'shared/Example.olean'
    publish_module(out,destination)
    assert destination.read_text()=='compiled'
    assert Path(str(destination)+'.private').read_text()=='private'
    assert destination.stat().st_mode & 0o222==0
    out.unlink();out.symlink_to(destination)
    try: publish_module(out,root/'shared/Other.olean')
    except ValueError: pass
    else: raise AssertionError('symlink output accepted')
print('PASS')
`,
    ],
    { encoding: "utf8" },
  );
  assert.match(result, /PASS/);
});

test("memory-heavy modules retry alone while proof failures and repeated exhaustion fail", () => {
  const result = execFileSync(
    "python3",
    [
      "-c",
      String.raw`
from verifier.standard.compile import compile_modules
from threading import Barrier, Lock
import time

class MemoryLimit(Exception): pass
lock=Lock(); barrier=Barrier(3, timeout=5)
active=set(); attempts={}; done=set(); events=[]
def compile(name, slots):
    with lock:
        attempts[name]=attempts.get(name,0)+1
        attempt=attempts[name]
        if attempt==2:
            assert not active and slots==3, (name,active,slots)
        if name=='Main': assert {'A','B','C','D'} <= done
        active.add(name); events.append((name,attempt))
    try:
        if name in ['A','B','C'] and attempt==1:
            barrier.wait()
            if name in ['A','B']: raise MemoryLimit(name)
            time.sleep(0.05)
        with lock: done.add(name)
    finally:
        with lock: active.remove(name)
compile_modules(['A','B','C','D','Main'],
    {'A':[],'B':[],'C':[],'D':[],'Main':['A','B','C','D']},compile,
    jobs=3,is_memory_error=lambda e:isinstance(e,MemoryLimit))
assert attempts=={'A':2,'B':2,'C':1,'D':1,'Main':1}, attempts
assert events.index(('D',1))>events.index(('A',2))
assert events.index(('D',1))>events.index(('B',2))

for error in [MemoryLimit('OOM'),RuntimeError('ill-typed proof'),RuntimeError('oom-kill printed by candidate')]:
    calls=[]
    def fail(name,slots):
        calls.append((name,slots))
        if name=='Large': raise error
        assert name!='Main', 'dependent compiled after failed prerequisite'
    try:
        compile_modules(['Large','Small','Main'],
            {'Large':[],'Small':[],'Main':['Large','Small']},fail,jobs=2,
            is_memory_error=lambda e:isinstance(e,MemoryLimit))
    except Exception as caught: assert caught is error
    else: raise AssertionError('failed compilation accepted')
    large=[slots for name,slots in calls if name=='Large']
    assert large==([1,2] if isinstance(error,MemoryLimit) else [1]), calls

# Exhaustion with the entire budget has no larger retry allocation.
calls=[]
def fail_alone(name,slots):
    calls.append(slots)
    raise MemoryLimit('OOM')
try:
    compile_modules(['Only'],{'Only':[]},fail_alone,jobs=4,
        is_memory_error=lambda e:isinstance(e,MemoryLimit))
except MemoryLimit: pass
else: raise AssertionError('exhaustion accepted')
assert calls==[4]
print('PASS')
`,
    ],
    { encoding: "utf8", timeout: 15_000 },
  );
  assert.match(result, /PASS/);
});
