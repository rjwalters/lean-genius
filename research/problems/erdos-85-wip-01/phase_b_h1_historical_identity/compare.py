import concurrent.futures,hashlib,json,sys,time,threading
from pathlib import Path
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
sys.path.insert(0,str(ROOT/'research/problems/erdos-85-wip-01/sat49'))
import materialize_h1_verdict_input as m
P=Path(__file__).parent
MANIFEST=ROOT/'research/problems/erdos-85-wip-01/phase_b_h1_h3/h1-frozen-candidates.json'
DIGEST=m.sha256(MANIFEST)
JOBS=json.loads((P/'remote-candidate-paths.json').read_text())
(P/'work').mkdir(exist_ok=True)
ABORT=threading.Event()
DEADLINE=float('inf')

def compare(job):
 tag=job['tag'];case='h1_'+tag;row,table,expected=m.select_input(MANIFEST,DIGEST,case)
 sparse=json.loads(table);baselines=[]
 for name in job['paths']:
  path=Path(name);verdict=path.with_suffix('.verdict');raw=verdict.read_text() if verdict.exists() else ''
  fields=raw.split();valid=False
  if fields and fields[0]==tag and all(t in fields for t in ['UNSAT','drat:VERIFIED','arm:v2']) and 'table:' in raw:
   parsed=json.loads(raw.split('table:',1)[1]);valid=sorted(parsed)==sorted(sparse)
  proofs=[]
  for suffix in ['.drat','.drat.gz','.lrat','.lrat.gz']:
   f=path.with_suffix(suffix)
   if f.exists():proofs.append({'path':str(f),'bytes':f.stat().st_size})
  baselines.append({'path':str(path),'sha256':m.sha256(path),'bytes':path.stat().st_size,
                    'verdict_path':str(verdict),'verdict':raw,'verified_verdict_and_table':valid,
                    'proof_paths':proofs,'proof_bytes_rechecked':False,
                    'mode':next((f.split(':',1)[1] for f in fields if f.startswith('mode:')),None)})
 target=P/'work'/tag
 result=m.materialize(MANIFEST,DIGEST,case,target,timeout=120,
                      cancelled=lambda: ABORT.is_set() or time.monotonic()>DEADLINE)
 native=Path(result['cnf_path']);matches=[b for b in baselines if b['sha256']==result['cnf_sha256']]
 record={'tag':tag,'profile':row['profile'],'canonical_sha256':result['cnf_sha256'],
         'canonical_bytes':result['cnf_bytes'],'materialization_receipt':result,
         'baselines':baselines,'byte_matching_baselines':len(matches),
         'matching_verified_baselines':sum(b['verified_verdict_and_table'] for b in matches),
         'status':'BYTE_MATCH' if matches else 'DIFFERENT','solver_launched':False,
         'scope':'Input identity and historical metadata only; no proof replay or automatic exclusion.'}
 if not matches:
  with native.open('rb') as a,Path(baselines[0]['path']).open('rb') as b:
   for i,(x,y) in enumerate(zip(a,b),1):
    if x!=y:record['first_difference']={'line':i,'canonical':x.decode().strip(),'historical':y.decode().strip()};break
 (target/'comparison.json').write_text(json.dumps(record,indent=2)+'\n')
 if matches:
  assert m.sha256(native)==result['cnf_sha256'];native.unlink();record['owned_input_removed_after_comparison']=True
 (target/'comparison.json').write_text(json.dumps(record,indent=2)+'\n')
 return record

if __name__=='__main__':
 count=int(sys.argv[1]) if len(sys.argv)>1 else 3
 jobs=JOBS[:count]
 t=time.monotonic();results=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  for r in pool.map(compare,jobs):
   results.append(r);print(json.dumps({k:r.get(k) for k in ['tag','status','byte_matching_baselines','matching_verified_baselines','first_difference']}),flush=True)
 (P/f'results-{count}.json').write_text(json.dumps({'count':len(results),'seconds':time.monotonic()-t,'results':results},indent=2)+'\n')
