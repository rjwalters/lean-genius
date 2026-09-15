"""Independent saved-certificate audit; never calls the native projection producer."""
import collections,gzip,hashlib,json,time
from pathlib import Path
from certificate import verify
D=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-h7-a6-f14-incidence-cover-sol2-20260915');B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');S=B/'hosts';T=Path('/Users/rwalters/lean-genius-h7-a6-f14-triangle-sol1-20260915')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert not (D/'launch.json').exists(),'Do not overwrite a launched audit'
 r=read(P/'results.json');launch=read(P/'launch.json');queue=read(T/'repaired/results.json')['remaining'];assert len(queue)==r['total']==445699
 assert len(set(map(tuple,queue)))==len(queue) and read(P/'unvisited.json')==queue[r['visited']:]
 assert r['visited']+r['unvisited']==r['total'] and r['attempted']-r['visited']==r['computed_not_saved']
 assert sha(T/'repaired/results.json')==launch['source_remaining_sha256'] and sha(B/'host-pins.json')==launch['source_host_pins_sha256']
 for base,manifest in [(B,'host-pins.json'),(T,'pins.json')]:
  for n,h in read(base/manifest).items():assert sha(base/n)==h
 files=[P/'results.json',P/'launch.json',P/'unvisited.json']+[P/n for n in r['shards']]
 pins={str(p):sha(p) for p in files};assert sum((P/n).stat().st_size for n in r['shards'])==r['artifact_bytes']<=launch['artifact_byte_cap']
 assert all((P/n).stat().st_size<=launch['shard_byte_cap'] for n in r['shards'])
 (D/'launch.json').write_text(json.dumps({'seconds':600,'input_hashes':pins,'visited':r['visited'],'total':r['total'],'scope':'Independent saved-record verification, not new projection search.'},indent=2)+'\n')
 start=time.monotonic();deadline=start+600;wanted={gid for gid,j in queue[:r['visited']]}
 inputs={x['global_index']:x['neighbors'] for x in map(json.loads,gzip.open(B/'inputs.jsonl.gz','rt')) if x['global_index'] in wanted}
 def records():
  for name in r['shards']:
   yield from map(json.loads,gzip.open(P/name,'rt'))
 records=iter(records());current=next(records,None);visited=nodes=branches=0;counts=collections.Counter();retained=[]
 for name in read(S/'results.json')['shards']:
  for host in map(json.loads,gzip.open(S/name,'rt')):
   gid=host['global_index']
   if gid not in wanted:continue
   assert host['receipt']['status']=='COMPLETE'
   while current is not None and current['global_index']==gid:
    assert time.monotonic()<deadline
    j=current['leaf_index'];assert [gid,j]==queue[visited]
    g=[sum(1<<v for v in ns) for ns in inputs[gid]]
    for e,m in enumerate(host['receipt']['solutions'][j],42):
     g[e]|=m
     for v in range(49):
      if m>>v&1:g[v]|=1<<e
    cert=current['certificate'];st=cert['status'];assert st in ['EMPTY_FAMILY','INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION','UNKNOWN','INVALID']
    if st in ['EMPTY_FAMILY','INFEASIBLE_PROJECTION','FEASIBLE_PROJECTION']:
     n,b=verify(g,cert,deadline);nodes+=n;branches+=b
    if st not in ['EMPTY_FAMILY','INFEASIBLE_PROJECTION']:retained.append([gid,j,st])
    counts[st]+=1;visited+=1;current=next(records,None)
   if current is None:break
  if current is None:break
 assert current is None and visited==r['visited'] and dict(counts)==r['counts'] and retained==r['retained']
 for n,h in pins.items():assert sha(Path(n))==h
 out={'status':'PASS_SAVED_INCIDENCE_CERTIFICATES','visited':visited,'unvisited':r['unvisited'],'counts':dict(counts),'negative':counts['EMPTY_FAMILY']+counts['INFEASIBLE_PROJECTION'],'retained':len(retained),'tree_nodes':nodes,'tree_branches':branches,'seconds':time.monotonic()-start,'whole_suffix_negative':visited==len(queue) and not retained,'scope':'Exact saved certificate/host joins and source queue partition; full F14 composition reviewed separately.'}
 (D/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
if __name__=='__main__':main()
