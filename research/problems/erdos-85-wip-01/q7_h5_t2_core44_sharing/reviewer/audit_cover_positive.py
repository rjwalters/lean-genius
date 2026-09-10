import itertools,json
from pathlib import Path
p=Path(__file__).parent;branches=json.loads((p/'branches.json').read_text())['results'];run=json.loads((p/'sharing-empty-results.json').read_text())['results']
def key(r):return (r['shared'],r['omitted'],tuple(map(tuple,r['internal'])),r['af'],r['bf'])
by={key(r):r for r in branches};assert len(by)==len(branches)==76
expected=set()
for shared in [1,2]:
 for internal in ([[],[(0,1)],[(0,3)]] if shared==1 else [[],[(0,1)],[(0,3)],[(1,3)]]):
  f0partners=[v if u==0 else u for u,v in internal if 0 in (u,v)]
  for targets in itertools.permutations(range(6),5): # 0=f0,1=a0,2=b0,3..5=freeS0
   if targets[0]==0:continue
   if [i for i,t in enumerate(targets) if t==0]!=f0partners:continue
   af=next((i for i,t in enumerate(targets) if t==1),None);bf=next((i for i,t in enumerate(targets) if t==2),None)
   if af is not None and af not in [3,4]:continue
   if bf is not None and (bf not in [1,2] or bf==shared):continue
   for omitted in [0,4,7,11]:expected.add((shared,omitted,tuple(internal),af,bf))
assert expected==set(by)
seen=set();positive=[]
for group in run:
 assert group['unvisited']==0
 for row in group['choices']:
  k=key(dict(row,shared=group['shared'],omitted=group['omitted']));assert k not in seen;seen.add(k)
  if row['status']!='PARTIAL_WITNESS':assert row['status']=='EXHAUSTED';continue
  G=list(map(set,row['adjacency']));assert len(G)==32
  assert all(v not in G[v] and all(v in G[w] for w in G[v]) for v in range(32))
  assert all(len(G[u]&G[v])<=1 for u,v in itertools.combinations(range(32),2))
  assert all(set(ns)<=G[v] for v,ns in enumerate(by[k]['adjacency']))
  for e in range(11,23):assert len(G[e]&set(range(11,23)))==2+sum(len(G[h]&set(range(5)))-1 for h in G[e] if 5<=h<11)
  for c in range(5):assert len(G[27+c]&set(range(11,23)))==(3 if c==group['shared'] else 2)
  positive.append(dict(shared=group['shared'],omitted=group['omitted'],internal=row['internal'],af=row['af'],bf=row['bf']))
assert seen==expected and len(positive)==12
(p/'cover-positive-audit.json').write_text(json.dumps(dict(covered_cases=76,method='Injective five colour0 targets drawn from six; no source enumeration imported',positive_count=12,positives=positive),indent=2)+'\n');print('76-case cover and12positive graphs independently checked')
