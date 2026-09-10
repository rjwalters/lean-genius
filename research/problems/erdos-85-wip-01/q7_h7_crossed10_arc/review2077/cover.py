import pathlib,json,itertools,time
P=pathlib.Path('/Users/rwalters/lean-genius-q7-outside-first-20260910/h7-crossed10-arc')
source=json.load(open('/tmp/erdos85-sol1-h7-profile-partitions/remaining-results.json'));r=next(x for x in source['results'] if not x['twins_adjacent'] and x['profile_index']==10)
sd=json.load(open('/tmp/erdos85-sol1-h7-high0-cover/results.json'));base=next(s['adjacency'] for s in sd['patterns'] if not s['twins_adjacent']);names=sd['names'];idx={s:i for i,s in enumerate(names)}
g0=list(map(set,base));H=sorted(g0[0]);edges=list(itertools.combinations(range(1,7),2));assert edges==list(map(tuple,r['edge_order']))
# Derive host colour slots from base graph common-high incidences.
avail=[{c for c in range(1,7) if not g0[h]&g0[c]} for h in H]
pc=r['profile']['pair_counts'];domain=[]
for h in range(8):
 choices=[]
 for es in itertools.combinations(range(15),pc[h]):
  ends=[c for e in es for c in edges[e]]
  if len(set(ends))==len(ends) and set(ends)<=avail[h]:choices.append(sum(1<<e for e in es))
 domain.append(choices)
# Profile fixes colours1,2. Its eight automorphisms permute the two
# unordered matched pairs {3,4},{5,6}, with independent endpoint flips.
actions=[]
for flip_order in (False,True):
 pairs=[(3,4),(5,6)][::(-1 if flip_order else 1)]
 for flips in itertools.product((False,True),repeat=2):
  vals=sum((list(p[::-1] if f else p) for p,f in zip(pairs,flips)),[]);cp=dict(zip(range(1,7),[1,2]+vals));hp=[0,1]+[cp[c]+1 for c in range(1,7)]
  ep=[edges.index(tuple(sorted((cp[a],cp[b])))) for a,b in edges];actions.append((hp,ep))

from functools import lru_cache
from collections import Counter
start=time.monotonic();nodes=0
@lru_cache(None)
def count(h,used):
 global nodes
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 if h<0:return int(used==32767)
 return sum(count(h-1,used|m) for m in domain[h] if not m&used)
raw=count(7,0);union=set();hist=Counter()
assert len(actions)==8
for hp,ep in actions:
 assert sorted(hp)==list(range(8)) and sorted(ep)==list(range(15))
 for h in range(8):
  assert {sum(1<<ep[e] for e in range(15) if m>>e&1) for m in domain[h]}==set(domain[hp[h]])
for a in r['assignments']:
 orbit=set()
 for hp,ep in actions:
  b=[0]*8
  for h,m in enumerate(a):b[hp[h]]=sum(1<<ep[e] for e in range(15) if m>>e&1)
  used=0
  for h,m in enumerate(b):
   assert m in domain[h] and not used&m
   used|=m
  assert used==32767
  orbit.add(tuple(b))
 assert not union&orbit
 union|=orbit;hist[len(orbit)]+=1
assert len(union)==raw
out=dict(status='PASS',raw=raw,representatives=len(r['assignments']),orbit_histogram=dict(hist),dp_states=nodes,seconds=time.monotonic()-start,method='Reverse-host memoized disjoint-edge count; explicit symmetry images form valid disjoint full-size union.')
(pathlib.Path(__file__).parent/'cover-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
