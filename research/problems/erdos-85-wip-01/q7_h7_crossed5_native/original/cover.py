from pathlib import Path
from functools import lru_cache
import json,itertools,hashlib,time,collections
p=Path(__file__).parent;o=Path(__file__).parent
pins=json.loads((p/'input-pins.json').read_text());assert all(hashlib.sha256((p/f).read_bytes()).hexdigest()==h for f,h in pins.items())
r=json.loads((p/'profile-source.json').read_text())['results'][0];assert not r['twins_adjacent'] and r['profile_index']==5 and r['status']=='COMPLETE'
sd=json.loads((p/'seed-source.json').read_text());g=list(map(set,next(r['adjacency'] for r in sd['patterns'] if not r['twins_adjacent'])));hosts=sorted(g[0]);edges=list(itertools.combinations(range(1,7),2));pc=r['profile']['pair_counts'];domains=[]
for h,n in zip(hosts,pc):
 allowed={c for c in range(1,7) if not g[h]&g[c]};choices=[]
 for es in itertools.combinations(range(15),n):
  ends=[c for e in es for c in edges[e]]
  if len(set(ends))==len(ends) and set(ends)<=allowed:choices.append(sum(1<<e for e in es))
 domains.append(choices)
start=time.monotonic();nodes=0
@lru_cache(None)
def count(h,used):
 global nodes
 nodes+=1
 if nodes>100000 or time.monotonic()-start>60:raise TimeoutError
 if h<0:return int(used==32767)
 return sum(count(h-1,used|m) for m in domains[h] if not used&m)
raw=count(7,0)
matching={frozenset((i,j)) for i in range(8) for j in range(i) if hosts[j] in g[hosts[i]]};actions=[]
for labels in itertools.permutations(range(1,7)):
 for swap in (False,True):
  hp=([1,0] if swap else [0,1])+[c+1 for c in labels]
  if {frozenset(hp[i] for i in e) for e in matching}!=matching or any(pc[h]!=pc[hp[h]] for h in range(8)):continue
  ep=[edges.index(tuple(sorted((labels[a-1],labels[b-1])))) for a,b in edges];actions.append((hp,ep))
seen=set();hist=collections.Counter()
for a in r['assignments']:
 orbit=set()
 for hp,ep in actions:
  b=[0]*8
  for h,m in enumerate(a):b[hp[h]]=sum(1<<ep[e] for e in range(15) if m>>e&1)
  used=0
  for h,m in enumerate(b):assert m in domains[h] and not used&m;used|=m
  assert used==32767;orbit.add(tuple(b))
 assert not seen&orbit;seen|=orbit;hist[len(orbit)]+=1
assert len(seen)==raw and len(r['assignments'])==7560
out={'status':'PASS','raw':raw,'representatives':len(r['assignments']),'actions':len(actions),'orbit_histogram':dict(hist),'reverse_dp_states':nodes,'seconds':time.monotonic()-start,'source_pins':pins}
(o/'cover-results.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='source_pins'})
