import gzip,hashlib,itertools,json,sqlite3,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-a6-f12-triangle-capacity-sol2-20260915');T=Path('/Users/rwalters/lean-genius-h7-a6-f12-support-capacity-sol2-20260915');O=Path(__file__).parent
S=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h7_a6_f12_host/original')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for d in [P,T,S]:
 for n,h in read(d/'pins.json').items():assert sha(d/n)==h
l=read(P/'launch.json');assert l['source_manifest']==sha(T/'pins.json') and l['host_manifest']==sha(S/'pins.json') and l['driver']==sha(P/'probe.py')
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
st,res=c.execute('select status,resolution from review_requests where id=2705').fetchone();assert st=='resolved' and res==l['review2705'] and res.startswith('PASS')
start=time.monotonic();out=read(P/'results.json');expected=set(map(tuple,read(T/'results.json')['remaining']));certs={(x['global_index'],x['leaf_index']):x for x in out['certificates']};rem=set(map(tuple,out['remaining']))
assert len(expected)==218 and len(certs)==len(out['certificates'])==out['killed']==89 and len(rem)==len(out['remaining'])==129 and not certs.keys()&rem and certs.keys()|rem==expected
wanted={x for x,y in expected};inputs={}
for line in gzip.open(S/'inputs.jsonl.gz','rt'):
 r=json.loads(line)
 if r['global_index'] in wanted:inputs[r['global_index']]=r
hosts={}
for name in read(S/'results.json')['shards']:
 for line in gzip.open(S/name,'rt'):
  r=json.loads(line)
  if r['global_index'] in wanted:
   assert r['receipt']['status']=='COMPLETE';hosts[r['global_index']]=r['receipt']['solutions']
count=0
for (gid,j),cert in certs.items():
 assert time.monotonic()-start<60
 g=[set(ns) for ns in inputs[gid]['neighbors']]
 for e,m in enumerate(hosts[gid][j],42):
  for v in range(49):
   if m>>v&1:g[e].add(v);g[v].add(e)
 H=set(range(7));u=cert['vertex'];assert 21<=u<42 and len(g[u])==2 and g[u]<=H
 candidates={v for v in range(7,21) if all(g[v].isdisjoint(g[w]) for w in g[u])}
 triangles={tuple(t) for t in itertools.combinations(sorted(candidates),3) if all(g[v].isdisjoint(g[w]) for v,w in itertools.combinations(t,2))}
 assert triangles and {tuple(c['triangle']) for c in cert['cuts']}==triangles and len(cert['cuts'])==len(triangles)
 for cut in cert['cuts']:
  tri=cut['triangle'];used=set().union(*(g[v]&H for v in tri));assert len(used)==3
  left=H-used;assert sum(1<<v for v in left)==cut['remaining_colours']
  eligible={v for v in range(21,42) if v!=u and g[v]&H<=left and all(g[v].isdisjoint(g[w]) for w in g[u]|set(tri))}
  assert eligible==set(cut['pair_candidates']) and len(eligible)==len(cut['pair_candidates'])
  supports={frozenset(g[v]&H) for v in eligible};assert all(len(e)==2 for e in supports)
  assert all(frozenset(left-e) not in supports for e in supports)
  count+=1
assert count==128 and out['seconds']<l['seconds']==60
result={'status':'PASS_REVIEW2706','negative':89,'remaining':129,'triangle_cuts':count,'seconds':time.monotonic()-start,'manifest_sha256':sha(P/'pins.json'),'scope':'Exact support-capacity certificates and prior218case partition only. Combined397105/397234 negative. No wholeF12/Lean/global exclusion.'}
(O/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
