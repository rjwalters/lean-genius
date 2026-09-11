"""One host pass on the accepted complete F13 high quotient."""
import collections,gzip,hashlib,importlib.util,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).parent;Q=pathlib.Path('/tmp/erdos85-sol1-h7-a6-high-quotient');A=pathlib.Path('/tmp/erdos85-sol1-h7-monotone-pair-host-api')
def main():
 assert not (P/'launch.json').exists(),'No overwrite or capped retry'
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);db.row_factory=sqlite3.Row;reviews=[]
 for rid in [2122,2123,2125]:
  r=dict(db.execute('select * from review_requests where id=?',(rid,)).fetchone());assert r['status']=='resolved' and r['resolution'].startswith('PASS'),r;reviews.append(r)
 for root,manifest in [(A,'pins.json'),(Q,'pins.json'),(pathlib.Path('/tmp/erdos85-sol1-h7-a6-projection-extension'),'pins.json'),(P,'prepared-pins.json')]:
  for f,h in json.loads((root/manifest).read_text()).items():assert hashlib.sha256((root/f).read_bytes()).hexdigest()==h
 with gzip.open(P/'inputs.jsonl.gz','rt') as f:inputs=[json.loads(line) for line in f]
 assert len(inputs)==49065 and [r['global_index'] for r in inputs]==json.loads((P/'input-verification.json').read_text())['global_indices']
 spec=importlib.util.spec_from_file_location('host_api',A/'api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
 (P/'premises.json').write_text(json.dumps(reviews,indent=2)+'\n');(P/'launch.json').write_text(json.dumps(dict(F_index=13,total=49065,max_nodes=100000,seconds=60))+'\n')
 counts=collections.Counter();visited=nodes=prunes=leaves=0;survivors=[];unknown=[];shards=[];raw=stream=None;start=time.monotonic()
 try:
  for r in inputs:
   remaining=60-(time.monotonic()-start)
   if remaining<=0:break
   result=api.enumerate_hosts(r['neighbors'],max_nodes=100000,seconds=remaining)
   assert result['status'] in ['COMPLETE','UNKNOWN']
   if stream is None or raw.tell()>40000000:
    if stream is not None:stream.close();raw.close()
    name=f'receipts-{len(shards):03d}.jsonl.gz';shards.append(name);raw=open(P/name,'wb');stream=gzip.GzipFile(fileobj=raw,mode='wb',mtime=0)
   record={k:r[k] for k in ['global_index','completion_index','singleton_index','colouring_index']};record['receipt']=result
   stream.write((json.dumps(record,separators=(',',':'))+'\n').encode())
   visited+=1;nodes+=result['nodes'];prunes+=len(result['prunes']);leaves+=len(result['solutions']);counts[result['status']]+=1
   if result['status']=='UNKNOWN':unknown.append(r['global_index'])
   for j in range(len(result['solutions'])):survivors.append([r['global_index'],j])
 finally:
  if stream is not None:stream.close();raw.close()
 summary=dict(total=49065,visited=visited,unvisited=49065-visited,counts=dict(counts),nodes=nodes,prunes=prunes,leaves=leaves,seconds=time.monotonic()-start,shards=shards,unknown=unknown)
 (P/'results.json').write_text(json.dumps(summary,indent=2)+'\n');(P/'survivors.json').write_text(json.dumps(survivors,separators=(',',':'))+'\n');print({k:v for k,v in summary.items() if k!='unknown'})
if __name__=='__main__':main()
