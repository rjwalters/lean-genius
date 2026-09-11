"""One bounded residual pass over the accepted F15 host leaves."""
from pathlib import Path
import json,gzip,hashlib,sqlite3,importlib.util,time,collections
P=Path(__file__).parent;S=P.parent/'h7-a6-f15-host-pass';A=Path('/tmp/erdos85-sol1-h7-a6-residual-batch-api')
def main():
 assert not (P/'launch.json').exists() and not (P/'results.json').exists(),'No overwrite or retry'
 c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;prem=[]
 for rid in [2120,2126,2128]:
  r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');prem.append(r)
 for root,manifest in [(S,'pins.json'),(A,'pins.json'),(P,'prepared-pins.json')]:
  for f,h in json.loads((root/manifest).read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
 assert (P/'source-pins.json').read_bytes()==(S/'pins.json').read_bytes() and (P/'source-indices.json').read_bytes()==(S/'survivors.json').read_bytes() and (P/'source-bases.jsonl.gz').read_bytes()==(S/'inputs.jsonl.gz').read_bytes()
 sp=importlib.util.spec_from_file_location('batch',A/'api.py');api=importlib.util.module_from_spec(sp);sp.loader.exec_module(api)
 bases={r['global_index']:r['neighbors'] for r in map(json.loads,gzip.open(P/'source-bases.jsonl.gz','rt'))};indices=json.loads((P/'source-indices.json').read_text());assert len(indices)==142812
 (P/'premises.json').write_text(json.dumps(prem,indent=2)+'\n');(P/'api-pins.json').write_bytes((A/'pins.json').read_bytes());(P/'launch.json').write_text(json.dumps(dict(F_index=15,total=142812,max_nodes=100000,seconds=60,shard_limit=50000000))+'\n')
 start=time.monotonic();deadline=start+60;seen=[];retained=[];counts=collections.Counter();nodes=0;shards=[];stream=None;size=0
 try:
  for line in gzip.open(P/'source-leaves.jsonl.gz','rt'):
   if time.monotonic()>deadline:break
   group=json.loads(line);gid=group['global_index'];results=api.check_hosts(bases[gid],list(range(42,49)),group['hosts'],max_nodes=100000,deadline=deadline);assert len(results)<=len(group['hosts'])
   for li,r in enumerate(results):
    assert r['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN'];seen.append([gid,li]);assert seen[-1]==indices[len(seen)-1];counts[r['status']]+=1;nodes+=r['nodes']
    if r['status'] in ['ARC_FEASIBLE','UNKNOWN']:retained.append([gid,li,r['status']])
    blob=gzip.compress((json.dumps(dict(global_index=gid,leaf_index=li,receipt=r),separators=(',',':'))+'\n').encode(),mtime=0);assert len(blob)<50000000
    if stream is None or size+len(blob)>50000000:
     if stream is not None:stream.close()
     name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('wb');size=0
    stream.write(blob);size+=len(blob)
   if len(results)<len(group['hosts']):break
 finally:
  if stream is not None:stream.close()
 assert seen==indices[:len(seen)]
 out=dict(total=len(indices),visited=len(seen),unvisited=len(indices)-len(seen),counts=dict(counts),nodes=nodes,retained=retained,shards=shards,seconds=time.monotonic()-start)
 (P/'results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
