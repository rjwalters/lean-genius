"""Independent F14 triangle certificates, using set adjacency and exact host join."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent;P=Path('/Users/rwalters/lean-genius-h7-a6-f14-triangle-sol1-20260915/repaired');B=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915');S=B/'hosts';F=B/'residual'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 r=read(P/'results.json');assert r['total']==r['visited']==520726 and not r['unvisited'] and r['stop'] is None
 source=read(F/'results.json');assert source['visited']==1757882 and source['unvisited']==520726
 allkeys=read(S/'survivors.json');expected=set(map(tuple,allkeys[1757882:]));negative={(gid,j):u for gid,j,u in r['certificates']};rest=list(map(tuple,r['remaining']))
 assert len(negative)==len(r['certificates'])==r['negative'] and len(rest)==len(set(rest)) and set(negative).isdisjoint(rest) and set(negative)|set(rest)==expected
 for n,h in read(B/'host-pins.json').items():assert sha(B/n)==h,n
 files=[P/'results.json',P/'launch.json',F/'results.json',B/'host-pins.json']
 pins={str(p):sha(p) for p in files};(D/'launch.json').write_text(json.dumps({'seconds':180,'input_hashes':pins},indent=2)+'\n')
 start=time.monotonic();wanted={};fixed={};common_checks=0
 for (gid,j),u in negative.items():wanted.setdefault(gid,set()).add(u)
 for inp in map(json.loads,gzip.open(B/'inputs.jsonl.gz','rt')):
  gid=inp['global_index']
  if gid not in wanted:continue
  assert time.monotonic()-start<180
  g=[set(ns) for ns in inp['neighbors']];compat={a:{b for b in range(7,21) if b!=a and g[a].isdisjoint(g[b])} for a in range(7,21)}
  for u in wanted[gid]:
   assert 21<=u<42 and len(g[u])==2 and g[u]<=set(range(7))
   candidates={s for s in range(7,21) if all(g[s].isdisjoint(g[h]) for h in g[u])}
   for a in candidates:
    for b in compat[a]&candidates:
     assert not (compat[a]&compat[b]&candidates);common_checks+=1
  fixed[gid]=True
 assert set(fixed)==set(wanted)
 joined=0
 for name in read(S/'results.json')['shards']:
  for host in map(json.loads,gzip.open(S/name,'rt')):
   gid=host['global_index']
   if gid not in wanted:continue
   assert host['receipt']['status']=='COMPLETE'
   for j,ms in enumerate(host['receipt']['solutions']):
    u=negative.get((gid,j))
    if u is None:continue
    assert all(not(m>>u&1) for m in ms);joined+=1
   assert time.monotonic()-start<180
 assert joined==len(negative)
 for n,h in pins.items():assert sha(Path(n))==h,n
 out={'status':'PASS_TRIANGLE_CERTIFICATES','negative':joined,'remaining':len(rest),'source_inputs':len(wanted),'fixed_vertex_checks':sum(map(len,wanted.values())),'compatibility_edge_checks':common_checks,'seconds':time.monotonic()-start,'scope':'Exact negative triangle certificates and complete unfinished suffix partition; prefix exclusions and whole root remain separate.'}
 (D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
