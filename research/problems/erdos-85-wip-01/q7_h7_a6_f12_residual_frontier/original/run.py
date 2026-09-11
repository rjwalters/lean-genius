"""One residual pass on the independently accepted F12 host leaves."""
import argparse,collections,gzip,hashlib,importlib.util,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).parent;S=pathlib.Path('/tmp/erdos85-sol1-h7-a6-f12-host-pass');A=pathlib.Path('/tmp/erdos85-sol1-h7-a6-residual-batch-api')
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--host-review',type=int,required=True);args=parser.parse_args()
 assert not (P/'launch.json').exists(),'No overwrite or capped retry'
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row;reviews=[]
 for rid in [2120,2126,args.host_review]:
  r=dict(db.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS'),r;reviews.append(r)
 assert str(S) in str(reviews[-1]['refs'])
 for root in [A,S]:
  for f,h in json.loads((root/'pins.json').read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
 with gzip.open(S/'inputs.jsonl.gz','rt') as f:inputs={r['global_index']:r for r in map(json.loads,f)}
 host_summary=json.loads((S/'results.json').read_text());records=[];expected=[]
 for shard in host_summary['shards']:
  with gzip.open(S/shard,'rt') as f:
   for line in f:
    r=json.loads(line);records.append(r);expected.extend([r['global_index'],j] for j in range(len(r['receipt']['solutions'])))
 assert expected==json.loads((S/'survivors.json').read_text()) and len(expected)==host_summary['leaves']
 spec=importlib.util.spec_from_file_location('batch_api',A/'api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
 (P/'premises.json').write_text(json.dumps(reviews,indent=2)+'\n');(P/'input-survivors.json').write_bytes((S/'survivors.json').read_bytes());(P/'source-pins.json').write_bytes((S/'pins.json').read_bytes())
 (P/'launch.json').write_text(json.dumps(dict(total=len(expected),max_nodes=100000,seconds=60,source_unvisited=host_summary['unvisited'],source_unknown=host_summary['unknown']))+'\n')
 visited=nodes=0;counts=collections.Counter();retained=[];shards=[];raw=stream=None;start=time.monotonic();deadline=start+60
 try:
  for r in records:
   if time.monotonic()>deadline:break
   host=r['receipt'];assignments=host['solutions']
   if not assignments:continue
   source=inputs[r['global_index']]
   result=api.check_hosts(source['neighbors'],host['empty_vertices'],assignments,max_nodes=100000,deadline=deadline)
   assert len(result)<=len(assignments)
   if stream is None or raw.tell()>40000000:
    if stream is not None:stream.close();raw.close()
    name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);raw=open(P/name,'wb');stream=gzip.GzipFile(fileobj=raw,mode='wb',mtime=0)
   for j,receipt in enumerate(result):
    assert receipt['status'] in ['INFEASIBLE_ROW','INFEASIBLE_ARC','ARC_FEASIBLE','UNKNOWN']
    record=dict(global_index=r['global_index'],leaf_index=j,receipt=receipt)
    stream.write((json.dumps(record,separators=(',',':'))+'\n').encode());visited+=1;nodes+=receipt['nodes'];counts[receipt['status']]+=1
    if receipt['status'] in ['ARC_FEASIBLE','UNKNOWN']:retained.append([r['global_index'],j,receipt['status']])
 finally:
  if stream is not None:stream.close();raw.close()
 summary=dict(total=len(expected),visited=visited,unvisited=len(expected)-visited,counts=dict(counts),nodes=nodes,seconds=time.monotonic()-start,retained=retained,shards=shards,source_unvisited=host_summary['unvisited'],source_unknown=host_summary['unknown'])
 (P/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k not in ['retained','source_unknown']})
if __name__=='__main__':main()
