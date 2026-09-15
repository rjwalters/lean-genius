"""Independent source-edge reconstruction of the accepted F14 quotient slice."""
import gzip,hashlib,itertools,json,time
from pathlib import Path
D=Path('/Users/rwalters/lean-genius-h7-a6-f14-sol1-20260915')
OUT=Path(__file__).parent
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
A=R/'q7_h7_a6_high_pairing_cover/original';Q=R/'q7_h7_a6_high_quotient/original'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic()
cover=json.loads((A/'source-cover-results.json').read_text())['cases']
completion=json.loads((A/'source-completion-results.json').read_text())['results']
high={}
for line in gzip.open(A/'high-colourings.jsonl.gz','rt'):
 r=json.loads(line)
 if r['F_index']==14:
  assert r['status']=='COMPLETE'
  key=(r['completion_index'],r['singleton_index']);assert key not in high
  high[key]=r['colourings']
reps=[r for r in json.loads((Q/'representatives.json').read_text()) if completion[r['completion_index']]['F_index']==14]
assert len(reps)==199155 and sum(r['orbit_size'] for r in reps)==238783
assert sum(map(len,high.values()))==238783
count=0
with gzip.open(D/'inputs.jsonl.gz','rt') as f:
 for r in reps:
  assert time.monotonic()-start<90
  saved=json.loads(next(f));assert all(saved[k]==r[k] for k in ['global_index','completion_index','singleton_index','colouring_index'])
  ci,si=r['completion_index'],r['singleton_index'];c=completion[ci];assert c['status']=='COMPLETE'
  src=cover[14];x=src['representatives'][c['X_index']]
  edges=set()
  def edge(u,v):
   assert u!=v
   edges.add(tuple(sorted((u,v))))
  for u,v in src['F_edges']:edge(42+u,42+v)
  for u,v in c['solutions'][si]:
   edge(u+42 if u<7 else u,v+42 if v<7 else v)
  for s,es in enumerate(x['singleton_hosts'],7):
   for e in es:edge(s,42+e)
  for v,(a,b) in enumerate(itertools.combinations(range(7),2),21):edge(v,a);edge(v,b)
  for s,h in enumerate(high[ci,si][r['colouring_index']],7):edge(s,h)
  for h in range(3):edge(h,h+18)
  actual=set()
  for u,ns in enumerate(saved['neighbors']):
   assert ns==sorted(set(ns)) and u not in ns
   for v in ns:
    assert u in saved['neighbors'][v]
    actual.add(tuple(sorted((u,v))))
  assert actual==edges
  count+=1
 assert next(f,None) is None
perm=[2,3,4,1,0,5,6];mask=594051
root_edges=[e for i,e in enumerate(itertools.combinations(range(7),2)) if mask>>i&1]
assert {tuple(sorted((perm[u],perm[v]))) for u,v in root_edges}=={tuple(e) for e in cover[14]['F_edges']}
result={'status':'PASS_INDEPENDENT_SOURCE_EDGES','graphs':count,'raw_high_assignments':238783,'source_classes':164,'es_graphs':len(high),'root':'cube_F6_t18','mask':mask,'parent_to_source':perm,'seconds':time.monotonic()-start,'input_sha256':sha(D/'inputs.jsonl.gz'),'scope':'Exact accepted quotient-source reconstruction and root isomorphism only; no host or residual claim.'}
(OUT/'independent-input-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
