"""One bounded pass on accepted F9 high graphs; host API acceptance required."""
import argparse,pathlib,json,sqlite3,hashlib,importlib.util,time,gzip,collections
from inputs import load,base_graph,given_high
P=pathlib.Path(__file__).parent;A=pathlib.Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api')
arg=argparse.ArgumentParser();arg.add_argument('--api-review',type=int,required=True);opts=arg.parse_args();assert not (P/'launch.json').exists() and not (P/'results.json').exists(),'No overwrite or retry'
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row;premises=[]
for rid in [2116,2121,opts.api_review]:
 r=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS');premises.append(r)
assert str(A) in str(premises[-1]['refs'])
for f,h in json.loads((A/'pins.json').read_text()).items():assert hashlib.sha256((A/f).read_bytes()).hexdigest()==h
spec=importlib.util.spec_from_file_location('host_api',A/'api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
cover,edges,highs=load();total=sum(len(r['pairings']) for r in highs['results']);assert total==28336
(P/'premises.json').write_text(json.dumps(premises,indent=2)+'\n');(P/'api-pins.json').write_bytes((A/'pins.json').read_bytes());(P/'launch.json').write_text(json.dumps(dict(total=total,max_nodes=100000,aggregate_seconds=60,artifact_shard_limit=50000000))+'\n')
start=time.monotonic();deadline=start+60;counts=collections.Counter();visited=nodes=negative=prunes=0;survivors=[];unknown=[];shards=[];stream=None;size=0;stop=False
for r in highs['results']:
 if stop:break
 base=base_graph(cover,edges,r)
 for pi,pairing in enumerate(r['pairings']):
  remaining=deadline-time.monotonic()
  if remaining<=0:stop=True;break
  adj=given_high(base,pairing);receipt=api.enumerate_hosts(adj,max_nodes=100000,seconds=remaining)
  assert receipt['status'] in ['COMPLETE','UNKNOWN']
  record=dict(case_index=r['case_index'],pairing_index=pi,source_index=r['source_index'],singleton_index=r['singleton_index'],receipt=receipt)
  blob=gzip.compress((json.dumps(record,separators=(',',':'))+'\n').encode(),mtime=0);assert len(blob)<50000000
  if stream is None or size+len(blob)>50000000:
   if stream is not None:stream.close()
   name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);stream=(P/name).open('wb');size=0
  stream.write(blob);size+=len(blob);visited+=1;counts[receipt['status']]+=1;nodes+=receipt['nodes'];prunes+=len(receipt['prunes'])
  if receipt['status']=='UNKNOWN':unknown.append([r['case_index'],pi])
  elif not receipt['solutions']:negative+=1
  survivors.extend([r['case_index'],pi,j] for j in range(len(receipt['solutions'])))
if stream is not None:stream.close()
result=dict(total=total,visited=visited,unvisited=total-visited,counts=dict(counts),negative_high_graphs=negative,surviving_host_leaves=len(survivors),pruned_prefixes=prunes,nodes=nodes,unknown_high_graphs=unknown,receipt_shards=shards,seconds=time.monotonic()-start)
(P/'results.json').write_text(json.dumps(result,indent=2)+'\n');(P/'survivors.json').write_text(json.dumps(survivors,separators=(',',':'))+'\n');print(result)
