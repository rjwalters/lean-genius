#!/usr/bin/env python3
"""Run with lake env python3 from the repository proofs directory."""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,os,re,shutil,subprocess,time
parser=argparse.ArgumentParser()
parser.add_argument('--build-dir',type=Path,required=True)
parser.add_argument('--workers',type=int,default=2,choices=range(1,5))
parser.add_argument('--timeout',type=int,default=180)
a=parser.parse_args();assert a.timeout>0
p=Path(__file__).resolve().parent;b=a.build_dir.resolve()
if b.exists() and any(b.iterdir()):parser.error('build directory must be empty; retained results must not be overwritten')
m=json.loads((p/'MANIFEST.json').read_text());records={x['name']:x for x in m['modules']}
assert len(records)==len(m['modules'])
assert [n for stage in m['stages'] for n in stage]==list(records)
for name,x in records.items():
 assert hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==x['sha256'],name
b.mkdir(parents=True,exist_ok=True)
for name in records:shutil.copy2(p/(name+'.lean'),b/(name+'.lean'))
env=os.environ.copy();env['LEAN_PATH']=str(b)+os.pathsep+env.get('LEAN_PATH','')
results=[];started=time.monotonic()
def save(status):
 tmp=b/'RESULT.tmp';tmp.write_text(json.dumps({'status':status,'elapsed_seconds':time.monotonic()-started,'results':results},indent=2)+'\n');tmp.replace(b/'RESULT.json')
def check(name):
 src=b/(name+'.lean');start=time.monotonic()
 with (b/(name+'.log')).open('w') as log:
  try:
   r=subprocess.run(['lean','--root',str(b),'-o',str(b/(name+'.olean')),str(src)],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=a.timeout);rc=r.returncode;timeout=False
  except subprocess.TimeoutExpired:rc=None;timeout=True
 text=(b/(name+'.log')).read_text();exports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)
 # Lean also reports axiom-free declarations using this sentence.
 zero=len(re.findall(r'does not depend on any axioms',text))
 allowed={'propext','Classical.choice','Quot.sound'}
 axok=all({x.strip() for x in e.split(',') if x.strip()}<=allowed for e in exports)
 count=len(exports)+zero
 unchanged=hashlib.sha256(src.read_bytes()).hexdigest()==records[name]['sha256']
 ok=rc==0 and not timeout and axok and count==records[name]['expected_exports'] and unchanged and (b/(name+'.olean')).is_file()
 result={'name':name,'returncode':rc,'timeout':timeout,'elapsed_seconds':time.monotonic()-start,'source_sha256':records[name]['sha256'],'source_unchanged':unchanged,'standard_axioms_only':axok,'exports':count,'verified':ok}
 (b/(name+'.run.json')).write_text(json.dumps(result,indent=2)+'\n')
 return result
save('running')
for stage in m['stages']:
 failed=False
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
  todo=iter(stage);pending=set()
  for _ in range(min(a.workers,len(stage))):pending.add(pool.submit(check,next(todo)))
  while pending:
   done,pending=concurrent.futures.wait(pending,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in done:
    r=f.result();results.append(r);failed |= not r['verified'];save('stopping_on_failure' if failed else 'running');print(json.dumps(r),flush=True)
    if not failed:
     name=next(todo,None)
     if name is not None:pending.add(pool.submit(check,name))
 if failed:save('failed');raise SystemExit(1)
assert sum(r['exports'] for r in results)==m['expected_exports']
save('complete')
