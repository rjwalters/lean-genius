"""Run from repository proofs under lake env; build all retained Lean sources."""
import argparse,concurrent.futures,hashlib,json,os,re,subprocess,tempfile,time
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--build-dir',type=Path)
parser.add_argument('--workers',type=int,default=2)
a=parser.parse_args();assert 1<=a.workers<=8
root=Path(__file__).resolve().parent;manifest=json.loads((root/'manifest.json').read_text())
build=(a.build_dir or Path(tempfile.mkdtemp(prefix='erdos85-fixed-pair-'))).resolve();build.mkdir(parents=True,exist_ok=True)
assert build!=root,'Use a separate build directory'
assert not any(build.iterdir()),'Build directory must be empty'
for name,digest in manifest['source_sha256'].items():
 data=(root/name).read_bytes();assert hashlib.sha256(data).hexdigest()==digest,name
 (build/name).write_bytes(data)
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(filter(None,[str(build),env.get('LEAN_PATH','')]))
allowed={'propext','Classical.choice','Quot.sound'}
start=time.monotonic();receipts=[]
def run(name):
 begin=time.monotonic();src=build/(name+'.lean')
 with src.with_suffix('.log').open('w') as log:
  r=subprocess.run(['lean','--root='+str(build),'-o',str(src.with_suffix('.olean')),str(src)],env=env,stdout=log,stderr=subprocess.STDOUT)
 text=src.with_suffix('.log').read_text();exports=re.findall(r'depends on axioms: \[([^\]]*)\]',text,re.S)
 export_count=len(exports)+text.count('does not depend on any axioms')
 checked=export_count==manifest['expected_exports'][name] and all({s.strip() for s in x.split(',') if s.strip()}<=allowed for x in exports)
 result=dict(module=name,exit_code=r.returncode,seconds=time.monotonic()-begin,exports=export_count,standard_axioms_only=checked,source_sha256=manifest['source_sha256'][src.name])
 src.with_suffix('.run.json').write_text(json.dumps(result,indent=2))
 return result
for number,stage in enumerate(manifest['stages']):
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:results=list(pool.map(run,stage))
 receipts.extend(results)
 (build/'results.json').write_text(json.dumps(dict(results=receipts,elapsed_seconds=time.monotonic()-start),indent=2))
 failed=[x for x in results if x['exit_code']!=0 or not x['standard_axioms_only']]
 print(json.dumps(dict(stage=number,modules=len(results),failed=[x['module'] for x in failed])),flush=True)
 if failed:raise SystemExit(1)
print(json.dumps(dict(status='PASS',modules=len(receipts),exports=sum(x['exports'] for x in receipts),build_dir=str(build),elapsed_seconds=time.monotonic()-start)),flush=True)
