import gzip,hashlib,itertools,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-support-capacity-sol2-20260915');O=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
S=R/'q7_h7_a6_f12_host/original';F=R/'q7_h7_a6_f12_residual_frontier/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d,m in [(S,'pins.json'),(F,'final-pins.json')]:
 for n,h in read(d/m).items():assert sha(d/n)==h
l=read(P/'launch.json');assert l['source_pins']==sha(S/'pins.json') and l['frontier_pins']==sha(F/'final-pins.json') and l['driver']==sha(P/'probe.py')
before={n:sha(P/n) for n in ['probe.py','launch.json','results.json']};out=read(P/'results.json')
start=time.monotonic();old=read(F/'results.json');allkeys=read(S/'survivors.json');assert read(F/'input-survivors.json')==allkeys and len(allkeys)==397234
assert old['visited']==395764 and old['retained']==[[227088,0,'UNKNOWN']]
expected={(227088,0)}|set(map(tuple,allkeys[395764:]));assert len(expected)==1471
certs={(r['global_index'],r['leaf_index']):r for r in out['certificates']};remaining=set(map(tuple,out['remaining']))
assert len(certs)==len(out['certificates'])==out['killed']==1253 and len(remaining)==len(out['remaining'])==218 and not set(certs)&remaining and set(certs)|remaining==expected
wanted={g for g,j in expected};inputs={}
for line in gzip.open(S/'inputs.jsonl.gz','rt'):
 r=json.loads(line)
 if r['global_index'] in wanted:inputs[r['global_index']]=r
hosts={}
for name in read(S/'results.json')['shards']:
 for line in gzip.open(S/name,'rt'):
  r=json.loads(line)
  if r['global_index'] in wanted:
   assert r['receipt']['status']=='COMPLETE'
   hosts[r['global_index']]=r['receipt']['solutions']
checks=0
for (gid,j),cert in certs.items():
 assert time.monotonic()-start<60
 g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,m in enumerate(hosts[gid][j],42):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 u=cert['vertex'];assert 21<=u<42 and len(g[u])==2 and g[u]<=set(range(7))
 eligible={v for v in range(7,21) if all(g[v].isdisjoint(g[w]) for w in g[u])};assert set(cert['singleton_candidates'])==eligible and len(cert['singleton_candidates'])==len(eligible)
 neighbors={v:{w for w in eligible-{v} if g[v].isdisjoint(g[w])} for v in eligible}
 edges={tuple(sorted((v,w))) for v in neighbors for w in neighbors[v]}
 assert edges==set(map(tuple,cert['compatibility_edges'])) and len(edges)==len(cert['compatibility_edges'])
 assert all(neighbors[v].isdisjoint(neighbors[w]) for v,w in edges)
 checks+=len(edges)
assert certs.get((227088,0)) is not None and out['seconds']<l['seconds']==60
for n,h in before.items():assert sha(P/n)==h
result={'status':'PASS_TRIANGLE_CERTIFICATES','negative':1253,'unclassified':218,'total_unfinished':1471,'checked_compatibility_edges':checks,'seconds':time.monotonic()-start,'input_hashes':before,'scope':'New triangle necessary obstruction only; old producer untouched. No full F12/root/global/Lean exclusion.'}
(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
