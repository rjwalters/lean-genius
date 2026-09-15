"""One bounded residual pass over the already-reviewed a6 F16 host cover."""
import collections,gzip,hashlib,importlib.util,json,sqlite3,time
from pathlib import Path
B=Path(__file__).parent
P=B/'residual';P.mkdir(exist_ok=True)
ROOT=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
S=B/'hosts';A=ROOT/'q7_h7_a6_residual_batch_api/original'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (P/'launch.json').exists(),'No overwrite or restart'
db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
reviews={}
for rid in [2118,2122,2125,2120,2126,2701]:
 st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
for root,manifest in [(B,'host-pins.json'),(A,'pins.json')]:
 for n,h in json.loads((root/manifest).read_text()).items():assert sha(root/n)==h
with gzip.open(B/'inputs.jsonl.gz','rt') as f:raw=list(map(json.loads,f))
assert len(raw)==48759 and len({r['global_index'] for r in raw})==48759
inputs={r['global_index']:r for r in raw}
host=json.loads((S/'results.json').read_text());assert host['counts']=={'COMPLETE':48759} and host['unvisited']==0 and host['unknown']==[] and host['leaves']==500280
records=[];expected=[];seen=[]
for shard in host['shards']:
 for line in gzip.open(S/shard,'rt'):
  r=json.loads(line);gid=r['global_index'];h=r['receipt'];src=inputs[gid]
  assert h['status']=='COMPLETE' and h['empty_vertices']==list(range(42,49))
  assert all(r[k]==src[k] for k in ['completion_index','singleton_index','colouring_index'])
  seen.append(gid)
  for j,ms in enumerate(h['solutions']):
   assert len(ms)==7 and all(m>=0 and m&((1<<21)-1)==0 and m>>42==0 for m in ms)
   expected.append([gid,j])
  records.append({'global_index':gid,'empty_vertices':h['empty_vertices'],'solutions':h['solutions']})
assert seen==[r['global_index'] for r in raw] and expected==json.loads((S/'survivors.json').read_text()) and len(expected)==500280
(P/'input-survivors.json').write_bytes((S/'survivors.json').read_bytes())
spec=importlib.util.spec_from_file_location('reviewed_a6_batch',A/'api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
with (P/'launch.json').open('x') as f:json.dump({'total':500280,'aggregate_seconds':120,'max_nodes':100000,'shard_byte_cap':50000000,'artifact_byte_cap':150000000,'source_path':str(S),'source_pins_sha256':sha(B/'host-pins.json'),'api_path':str(A),'api_pins_sha256':sha(A/'pins.json'),'input_survivors_sha256':sha(P/'input-survivors.json'),'driver_sha256':sha(Path(__file__)),'reviews':reviews},f,indent=2)
start=time.monotonic();deadline=start+120
visited=nodes=allsize=size=groups=0;counts=collections.Counter();retained=[];shards=[];stream=None;stop=None;unsaved=0
for r in records:
 if time.monotonic()>=deadline:stop='AGGREGATE_CAP';break
 hs=r['solutions'];gid=r['global_index']
 if not hs:continue
 receipts=api.check_hosts(inputs[gid]['neighbors'],r['empty_vertices'],hs,max_nodes=100000,deadline=deadline)
 assert len(receipts)<=len(hs)
 blob=gzip.compress((json.dumps({'global_index':gid,'receipts':receipts},separators=(',',':'))+'\n').encode(),mtime=0)
 assert len(blob)<50000000
 if allsize+len(blob)>150000000:stop='ARTIFACT_CAP';unsaved=len(receipts);break
 if stream is None or size+len(blob)>50000000:
  if stream:stream.close()
  name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('xb');size=0
 stream.write(blob);size+=len(blob);allsize+=len(blob);groups+=1
 for j,cert in enumerate(receipts):
  assert cert['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN']
  counts[cert['status']]+=1;visited+=1;nodes+=cert['nodes']
  if cert['status'] in ['ARC_FEASIBLE','UNKNOWN']:retained.append([gid,j,cert['status']])
 if len(receipts)<len(hs):stop='AGGREGATE_CAP';break
if stream:stream.close()
out={'total':500280,'visited':visited,'unvisited':500280-visited,'counts':dict(counts),'nodes':nodes,'retained':retained,'shards':shards,'groups':groups,'artifact_bytes':allsize,'seconds':time.monotonic()-start,'stop':stop,'computed_not_saved':unsaved,'scope':'Necessary a6 residual row/arc consistency; UNKNOWN/positive/suffix remain unresolved.'}
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='retained'}))
