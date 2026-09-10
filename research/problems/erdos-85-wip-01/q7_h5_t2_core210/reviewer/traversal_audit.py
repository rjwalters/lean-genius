import itertools,math,json,collections
from pathlib import Path
n=5;edges=list(itertools.combinations(range(n),2));expected=collections.Counter()
for bits in range(1<<len(edges)):
 g=[set() for _ in range(n)]
 for i,(a,b) in enumerate(edges):
  if bits>>i&1:g[a].add(b);g[b].add(a)
 if all(len(g[a]&g[b])<=1 for a,b in edges):expected[tuple(map(len,g))]+=1
# Same done-vertex traversal mechanics as reviewed source, with no host filter.
def traverse(degrees):
 g=[set() for _ in range(n)];rem=list(degrees)
 def legal(u,v):return v not in g[u] and all(not g[v]&g[w] for w in g[u])
 def dfs(done):
  if done==(1<<n)-1:return 1
  best=None
  for i in range(n):
   if done>>i&1:continue
   cs=[j for j in range(n) if j!=i and not done>>j&1 and rem[j]>0 and legal(i,j)]
   if len(cs)<rem[i]:return 0
   score=math.comb(len(cs),rem[i])
   if best is None or score<best[0]:best=(score,i,cs)
  _,i,cs=best;need=rem[i];total=0
  for group in itertools.combinations(cs,need):
   added=[]
   for j in group:
    if not legal(i,j):break
    g[i].add(j);g[j].add(i);rem[j]-=1;added.append(j)
   else:
    rem[i]=0;total+=dfs(done|1<<i);rem[i]=need
   for j in added:g[i].remove(j);g[j].remove(i);rem[j]+=1
  return total
 return dfs(0)
checks=0
for degrees in itertools.product(range(n),repeat=n):
 if sum(degrees)%2:continue
 assert traverse(degrees)==expected[degrees],degrees;checks+=1
result={'status':'PASS','degree_vectors_checked':checks,'direct_graph_masks':1024,'c4_free_graphs':sum(expected.values()),'scope':'Exhaustive small-domain validation of done-vertex enumeration and undo mechanics against direct edge-subset census; general completeness additionally inspected mathematically.'}
Path(__file__).with_name('traversal-results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
