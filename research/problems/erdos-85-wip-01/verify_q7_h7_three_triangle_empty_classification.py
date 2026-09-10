"""Exact induced seven-vertex H7 triangle-cover classification; no full graph search."""
import itertools,json,time,sys
from functools import lru_cache
from pathlib import Path
N=7
EDGES=list(itertools.combinations(range(N),2))
INDEX={e:i for i,e in enumerate(EDGES)}
PERMS=list(itertools.permutations(range(N)))
MAPS=[[INDEX[tuple(sorted((p[u],p[v])))] for u,v in EDGES] for p in PERMS]
def adjacency(mask):
 a=[0]*N
 for i,(u,v) in enumerate(EDGES):
  if mask>>i&1:a[u]|=1<<v;a[v]|=1<<u
 return a

def valid(mask):
 a=adjacency(mask)
 return max(x.bit_count() for x in a)<=3 and all((a[u]&a[v]).bit_count()<=1 for u,v in EDGES)

def orbit(mask):
 ix=[i for i in range(21) if mask>>i&1]
 return {sum(1<<m[i] for i in ix) for m in MAPS}

def classify(mask):
 a=adjacency(mask)
 tri=[sum(1<<x for x in t) for t in itertools.combinations(range(N),3) if all(a[u]>>v&1 for u,v in itertools.combinations(t,2))]
 cliques=[1<<v for v in range(N)]+[(1<<u)|(1<<v) for i,(u,v) in enumerate(EDGES) if mask>>i&1]+tri
 @lru_cache(None)
 def cover(s):
  if not s:return 0
  v=s&-s
  return 1+min(cover(s^c) for c in cliques if c&v and c&s==c)
 def pm(s):
  vs=[v for v in range(N) if s>>v&1]
  if not vs:return True
  u=vs[0]
  return any(a[u]>>v&1 and pm(s^(1<<u)^(1<<v)) for v in vs[1:])
 assert all(t&u==0 for t,u in itertools.combinations(tri,2))
 criterion=len(tri)>=2 or any(pm(127^t) for t in tri)
 k=cover(127)
 assert (k<=3)==criterion
 # Independent direct coloring of the complement by at most three labels.
 colorable=any(all(colors[u]!=colors[v] or a[u]>>v&1 for u,v in EDGES)
   for colors in itertools.product(range(3),repeat=N))
 assert colorable==criterion
 return dict(edges=[list(e) for i,e in enumerate(EDGES) if mask>>i&1],triangles=tri,clique_cover=k,retained=criterion)

def main():
 result={}
 for m in range(6,10):
  started=time.monotonic()
  survivors=set()
  for ix in itertools.combinations(range(21),m):
   mask=sum(1<<i for i in ix)
   if valid(mask):survivors.add(mask)
  count=len(survivors); rows=[]
  while survivors:
   mask=min(survivors);o=orbit(mask)
   assert o<=survivors
   survivors-=o
   row=classify(mask);row.update(mask=mask,orbit_size=len(o));rows.append(row)
  result[str(m)]=dict(labeled=count,orbits=rows,retained_orbits=sum(r['retained'] for r in rows))
  print(m,count,len(rows),result[str(m)]['retained_orbits'],round(time.monotonic()-started,2),flush=True)
 expected={"6":(31332,19,3),"7":(32910,15,5),"8":(17010,7,4),"9":(3360,2,1)}
 for m,d in result.items():
  assert (d['labeled'],len(d['orbits']),d['retained_orbits'])==expected[m]
  assert sum(r['orbit_size'] for r in d['orbits'])==d['labeled']
 out=Path(__file__).with_name('q7_h7_three_triangle_empty_classification.json')
 if '--write' in sys.argv:out.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(out.read_text())==result
 print('PASS: exhaustive induced domain, full S7 orbits, clique-cover DP, independent three-color check, and retained JSON')
if __name__=='__main__':main()
