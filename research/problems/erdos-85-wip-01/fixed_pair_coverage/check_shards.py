from pathlib import Path
import concurrent.futures,json,subprocess,sys,time,hashlib,os
p=Path(__file__).parent
manifest=json.loads((p/'shards_manifest.json').read_text())
assert all(hashlib.sha256((p/(x['name']+'.lean')).read_bytes()).hexdigest()==x['sha256'] for x in manifest)
assert not (p/'shards_progress.json').exists(), 'Existing run; inspect rather than restart'
start=time.monotonic();results=[];failed=False

def run(x):
 name=x['name'];subprocess.run([sys.executable,str(p/'check_one.py'),name,'180'],check=True)
 r=json.loads((p/(name+'.run.json')).read_text())
 log=(p/(name+'.log')).read_text()
 ok=r['returncode']==0 and not r['timeout'] and 'sorryAx' not in log and 'native_decide' not in log and log.count('depends on axioms:')==1
 return dict(x,**r,verified=ok,source_unchanged=hashlib.sha256((p/(name+'.lean')).read_bytes()).hexdigest()==x['sha256'])

def save(status):
 tmp=p/'shards_progress.tmp';tmp.write_text(json.dumps({'pid':os.getpid(),'status':status,'workers':2,'elapsed_seconds':time.monotonic()-start,'results':results},indent=2)+'\n');tmp.replace(p/'shards_progress.json')

save('running')
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 it=iter(manifest);pending={pool.submit(run,x) for x in [next(it),next(it)]}
 while pending:
  done,pending=concurrent.futures.wait(pending,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in done:
   r=f.result();results.append(r);failed |= not (r['verified'] and r['source_unchanged']);save('stopping_on_failure' if failed else 'running')
   if not failed:
    x=next(it,None)
    if x is not None:pending.add(pool.submit(run,x))
save('failed' if failed else 'complete')
raise SystemExit(1 if failed else 0)
