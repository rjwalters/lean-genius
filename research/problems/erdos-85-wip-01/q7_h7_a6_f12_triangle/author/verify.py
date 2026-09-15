"""Independently check saved triangle certificates using set adjacency."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
S=R/'q7_h7_a6_f12_host/original';F=R/'q7_h7_a6_f12_residual_frontier/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base,manifest in [(S,'pins.json'),(F,'final-pins.json')]:
 for n,h in read(base/manifest).items():assert sha(base/n)==h
result=read(D/'results.json');launch=read(D/'launch.json')
assert sha(D/'probe.py')==launch['driver'] and sha(S/'pins.json')==launch['source_pins'] and sha(F/'final-pins.json')==launch['frontier_pins']
order=read(S/'survivors.json');assert order==read(F/'input-survivors.json') and len(order)==397234
expected={(227088,0)}|set(map(tuple,order[395764:]));assert len(expected)==1471
certs=result['certificates'];keys=[(r['global_index'],r['leaf_index']) for r in certs];rest=list(map(tuple,result['remaining']))
assert len(keys)==len(set(keys))==1253 and len(rest)==len(set(rest))==218 and set(keys).isdisjoint(rest) and set(keys)|set(rest)==expected and (227088,0) in keys
needed={gid for gid,j in expected}
inputs={r['global_index']:r for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in needed}
hosts={}
for name in read(S/'results.json')['shards']:
 for r in map(json.loads,gzip.open(S/name,'rt')):
  if r['global_index'] in needed:
   assert r['receipt']['status']=='COMPLETE';hosts[r['global_index']]=r['receipt']
start=time.monotonic();triangles=0
for cert in certs:
 assert time.monotonic()-start<60
 gid,j=cert['global_index'],cert['leaf_index'];g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,mask in zip(hosts[gid]['empty_vertices'],hosts[gid]['solutions'][j]):
  for v in range(49):
   if mask>>v&1:g[e].add(v);g[v].add(e)
 u=cert['vertex'];assert 21<=u<42 and len(g[u])==2 and g[u]<=set(range(7))
 candidates=[v for v in range(7,21) if all(g[v].isdisjoint(g[w]) for w in g[u])]
 assert candidates==cert['singleton_candidates']
 edges={tuple(sorted((a,b))) for a,b in itertools.combinations(candidates,2) if g[a].isdisjoint(g[b])}
 assert edges==set(map(tuple,cert['compatibility_edges']))
 for a,b,c in itertools.combinations(candidates,3):
  assert not ({(a,b),(a,c),(b,c)}<=edges);triangles+=1
out={'status':'PASS_TRIANGLE_CERTIFICATES','checked':len(certs),'remaining':len(rest),'triangles_checked':triangles,'old_negative_prefix':395763,'composed_negative_count':395763+len(certs),'seconds':time.monotonic()-start,'scope':'Accepted host source and old prefix inherited; new triangle certificate checks only. Remaining218 preserved.'}
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
