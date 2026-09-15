"""One bounded host pass on the reviewed F17 quotient input slice."""
import collections,gzip,hashlib,importlib.util,json,sqlite3,time
from pathlib import Path
P=Path(__file__).parent;D=P/'hosts'
A=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_monotone_host_api/original')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 D.mkdir(exist_ok=True);assert not (D/'launch.json').exists(),'No overwrite or capped retry'
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);reviews={}
 for rid in [2118,2122,2123,2125,2698]:
  st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS');reviews[rid]=res
 for base,manifest in [(P,'input-pins.json'),(A,'pins.json')]:
  for n,h in json.loads((base/manifest).read_text()).items():assert sha(base/n)==h,n
 spec=importlib.util.spec_from_file_location('host_api',A/'api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
 inputs=[json.loads(s) for s in gzip.open(P/'inputs.jsonl.gz','rt')]
 assert len(inputs)==77813 and [r['global_index'] for r in inputs]==json.loads((P/'input-verification.json').read_text())['global_indices']
 launch=dict(F_index=17,total=77813,max_nodes=100000,seconds=240,shard_byte_cap=50000000,artifact_byte_cap=450000000,input_pins_sha256=sha(P/'input-pins.json'),api_pins_sha256=sha(A/'pins.json'),driver_sha256=sha(Path(__file__)),reviews=reviews)
 with (D/'launch.json').open('x') as f:json.dump(launch,f,indent=2)
 start=time.monotonic();counts=collections.Counter();visited=nodes=prunes=leaves=zero=0;survivors=[];unknown=[];shards=[];stream=None;size=allsize=0;stop=None;discarded=0
 try:
  for r in inputs:
   remaining=240-(time.monotonic()-start)
   if remaining<=0:stop='AGGREGATE_CAP';break
   result=api.enumerate_hosts(r['neighbors'],max_nodes=100000,seconds=remaining)
   assert result['status'] in ['COMPLETE','UNKNOWN']
   record={k:r[k] for k in ['global_index','completion_index','singleton_index','colouring_index']};record['receipt']=result
   blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0)
   if len(blob)>50000000 or allsize+len(blob)>450000000:stop='ARTIFACT_CAP';discarded=1;break
   if stream is None or size+len(blob)>50000000:
    if stream:stream.close()
    name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(D/name).open('xb');size=0
   stream.write(blob);size+=len(blob);allsize+=len(blob)
   visited+=1;nodes+=result['nodes'];prunes+=len(result['prunes']);leaves+=len(result['solutions']);counts[result['status']]+=1
   if result['status']=='UNKNOWN':unknown.append(r['global_index'])
   elif not result['solutions']:zero+=1
   for j in range(len(result['solutions'])):survivors.append([r['global_index'],j])
 finally:
  if stream:stream.close()
 summary=dict(total=77813,visited=visited,unvisited=77813-visited,counts=dict(counts),nodes=nodes,prunes=prunes,leaves=leaves,zero_leaf_complete=zero,seconds=time.monotonic()-start,shards=shards,unknown=unknown,artifact_bytes=allsize,stop=stop,computed_but_not_saved=discarded)
 (D/'results.json').write_text(json.dumps(summary,indent=2)+'\n');(D/'survivors.json').write_text(json.dumps(survivors,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='unknown'}))
if __name__=='__main__':main()
