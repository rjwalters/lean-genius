from pathlib import Path
import subprocess, json, hashlib, time, os, threading, argparse, shutil
from concurrent.futures import ThreadPoolExecutor, as_completed

script_root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--renderer',type=Path,default=script_root/'render.py')
parser.add_argument('--witnesses',type=Path,default=script_root.parent/'witnesses.json')
args=parser.parse_args()
root=args.output.resolve()
root.mkdir(parents=True,exist_ok=True)
renderer=args.renderer.resolve()
witness=args.witnesses.resolve()
codes=[3,4,5,6,7,8,9,10,12,13]
stop=threading.Event()
assert not (root/'RUN.json').exists(), 'Inspect existing run before restarting'
started=time.monotonic()
manifest={'renderer_sha256':hashlib.sha256(renderer.read_bytes()).hexdigest(),
          'witness_sha256':hashlib.sha256(witness.read_bytes()).hexdigest(),
          'mask_codes':codes,'workers':2,'planned_shards':100,'results':[]}
(root/'RUN.json').write_text(json.dumps(manifest,indent=2)+'\n')
for a in codes:
    for b in codes:
        subprocess.run(['python3',str(renderer),'--witnesses',str(witness),'--a',str(a),'--b',str(b),
                        '--output',str(root/f'Full_{a}_{b}.lean')],check=True,stdout=subprocess.DEVNULL)

def compile_one(a,b):
    if stop.is_set(): return {'a':a,'b':b,'status':'not_started'}
    name=f'Full_{a}_{b}'
    t=time.monotonic()
    with (root/f'{name}.log').open('w') as log:
        p=subprocess.run(['lean','-R',str(root),'-o',str(root/f'{name}.olean'),str(root/f'{name}.lean')],stdout=log,stderr=subprocess.STDOUT)
    text=(root/f'{name}.log').read_text()
    good=p.returncode==0 and 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
    result={'a':a,'b':b,'exit_code':p.returncode,'status':'pass' if good else 'fail',
            'elapsed_seconds':time.monotonic()-t,
            'source_sha256':hashlib.sha256((root/f'{name}.lean').read_bytes()).hexdigest(),
            'log_sha256':hashlib.sha256((root/f'{name}.log').read_bytes()).hexdigest()}
    (root/f'{name}.run.json').write_text(json.dumps(result,indent=2)+'\n')
    if not good: stop.set()
    return result

with ThreadPoolExecutor(max_workers=2) as pool:
    futures=[pool.submit(compile_one,a,b) for a in codes for b in codes]
    for f in as_completed(futures):
        result=f.result();manifest['results'].append(result)
        manifest['elapsed_seconds']=time.monotonic()-started
        tmp=root/'RUN.json.tmp';tmp.write_text(json.dumps(manifest,indent=2)+'\n');tmp.replace(root/'RUN.json')
        print(json.dumps(result),flush=True)
manifest['complete']=len(manifest['results'])==100 and all(r['status']=='pass' for r in manifest['results'])
manifest['elapsed_seconds']=time.monotonic()-started
(root/'RUN.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'complete':manifest['complete'],'elapsed_seconds':manifest['elapsed_seconds']}),flush=True)
if not manifest['complete']:
    raise SystemExit(1)
env=os.environ.copy()
env['LEAN_PATH']=env.get('LEAN_PATH','')+os.pathsep+str(root)
for name in ['Assembly','Representatives']:
    source=script_root/f'{name}.lean'
    if source.resolve()!=(root/source.name).resolve(): shutil.copy2(source,root/source.name)
    t=time.monotonic()
    with (root/f'{name}.log').open('w') as log:
        p=subprocess.run(['lean','-R',str(root),'-o',str(root/f'{name}.olean'),str(root/f'{name}.lean')],
                         env=env,stdout=log,stderr=subprocess.STDOUT)
    result={'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-t}
    (root/f'{name}.run.json').write_text(json.dumps(result,indent=2)+'\n')
    print(name,result,flush=True)
    if p.returncode: raise SystemExit(p.returncode)
