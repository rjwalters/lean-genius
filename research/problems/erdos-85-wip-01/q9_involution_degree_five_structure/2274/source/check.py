import itertools,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
out=[]
for t in range(3):
 edges=[(0,1)]+[(0,2*i) for i in range(1,5)]+[(1,2*i+1) for i in range(1,5)]
 for a,b in [(2,4),(6,8)][:t]:edges.extend([(a,b),(a^1,b^1)])
 adj=[set() for _ in range(10)]
 for a,b in edges:adj[a].add(b);adj[b].add(a)
 surviving=[]
 for mask in range(1024):
  S={i for i in range(10) if mask>>i&1}
  if S&{i^1 for i in S}:continue
  if any(adj[a]&adj[b] for a,b in itertools.combinations(S,2)):continue
  surviving.append(sorted(S))
 assert max(map(len,surviving))==2
 pairs=[S for S in surviving if len(S)==2 and 0 in S]
 expected=[[0,i] for i in range(2,10,2) if len(adj[i])==1]
 assert pairs==expected
 out.append(dict(t=t,subsets_checked=1024,max_size=2,allowed_central_pairs=pairs,subset_counts={str(k):sum(len(S)==k for S in surviving) for k in range(3)}))
print(json.dumps(out,indent=2))
