"""Independent set-based validation of triangle/colour-capacity certificates."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path(__file__).parent;T=Path('/Users/rwalters/lean-genius-h7-a6-f12-support-capacity-sol2-20260915')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01');S=R/'q7_h7_a6_f12_host/original'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for base in [T,S]:
 for n,h in read(base/'pins.json').items():assert sha(base/n)==h,n
launch=read(D/'launch.json');assert sha(D/'probe.py')==launch['driver'] and sha(T/'pins.json')==launch['source_manifest'] and sha(S/'pins.json')==launch['host_manifest']
result=read(D/'results.json');old=read(T/'results.json')['remaining'];expected=set(map(tuple,old));keys=[(r['global_index'],r['leaf_index']) for r in result['certificates']];rest=list(map(tuple,result['remaining']))
assert len(keys)==len(set(keys))==89 and len(rest)==len(set(rest))==129 and set(keys).isdisjoint(rest) and set(keys)|set(rest)==expected
needed={gid for gid,j in expected};inputs={r['global_index']:r for r in map(json.loads,gzip.open(S/'inputs.jsonl.gz','rt')) if r['global_index'] in needed};hosts={}
for name in read(S/'results.json')['shards']:
 for r in map(json.loads,gzip.open(S/name,'rt')):
  if r['global_index'] in needed:hosts[r['global_index']]=r['receipt']
start=time.monotonic();count=0
for cert in result['certificates']:
 assert time.monotonic()-start<60
 gid,j=cert['global_index'],cert['leaf_index'];g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,mask in zip(hosts[gid]['empty_vertices'],hosts[gid]['solutions'][j]):
  for v in range(49):
   if mask>>v&1:g[e].add(v);g[v].add(e)
 high=set(range(7));u=cert['vertex'];assert 21<=u<42 and len(g[u])==2 and g[u]<=high
 candidates=[v for v in range(7,21) if all(g[v].isdisjoint(g[w]) for w in g[u])]
 triangles=[t for t in itertools.combinations(candidates,3) if all(g[a].isdisjoint(g[b]) for a,b in itertools.combinations(t,2))]
 assert triangles and [list(t) for t in triangles]==[r['triangle'] for r in cert['cuts']]
 for tri,cut in zip(triangles,cert['cuts']):
  covered=set().union(*(g[s]&high for s in tri));assert len(covered)==3;left=high-covered
  assert sum(1<<h for h in left)==cut['remaining_colours']
  pairs=[p for p in range(21,42) if p!=u and (g[p]&high)<=left and all(g[p].isdisjoint(g[w]) for w in g[u]|set(tri))]
  assert pairs==cut['pair_candidates']
  assert all(len(g[p]&high)==2 for p in pairs)
  assert all((g[a]&high)&(g[b]&high) for a,b in itertools.combinations(pairs,2))
  count+=1
out={'status':'PASS_TRIANGLE_COLOUR_CAPACITY','negative_certificates':len(keys),'triangle_cuts':count,'remaining':len(rest),'combined_negative_leaves':395763+1253+len(keys),'total_host_leaves':397234,'seconds':time.monotonic()-start,'scope':'New matching-capacity certificate checks only; remaining129 unclassified; source and earlier exclusions inherited.'}
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
