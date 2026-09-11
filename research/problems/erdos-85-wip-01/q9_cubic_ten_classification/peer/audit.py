from pathlib import Path
import itertools,json,hashlib
p=Path(__file__).parent;src=Path('/Users/rwalters/lean-genius-q9-known-values-20260911/cubic-ten-classification');pins=json.loads((src/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((src/f).read_bytes()).hexdigest()==h
reps=json.loads((src/'representatives.json').read_text())
def adj(edges,n):
 A=[[0]*n for _ in range(n)]
 for u,v in edges:assert u!=v and not A[u][v];A[u][v]=A[v][u]=1
 return A
def verify(edges):
 A=adj(edges,10);assert all(sum(r)==3 for r in A)
 assert all(sum(A[u][k]*A[v][k] for k in range(10))<=1 for u,v in itertools.combinations(range(10),2))
 return A,[list(t) for t in itertools.combinations(range(10),3) if all(A[u][v] for u,v in itertools.combinations(t,2))]
RA=[]
for r in reps:
 A,tr=verify(r['edges']);assert tr==r['triangles'];RA.append(A)
assert list(map(lambda r:len(r['triangles']),reps))==[0,2,3]
pairs=list(itertools.combinations(range(4),2));hist={};valid=0
for ye in itertools.combinations(pairs,3):
 Y=adj(ye,4);dem=[3-sum(row) for row in Y]
 for chosen in itertools.combinations(pairs,3):
  if [sum(i in e for e in chosen) for i in range(4)]!=dem:continue
  if any(sum(Y[u][k]*Y[v][k] for k in range(4)) for u,v in chosen):continue
  edges=[(0,1),(0,2),(1,2),(0,3),(1,4),(2,5)]+[(6+u,6+v) for u,v in ye]+[(3+i,6+y) for i,e in enumerate(chosen) for y in e]
  A,tr=verify(edges);target=RA[1 if len(tr)==2 else 2];isomorphic=False
  for perm in itertools.permutations(range(3)):
   external=[next(j for j in range(3,10) if target[i][j]) for i in perm]
   remainder=[j for j in range(10) if j not in (*perm,*external)]
   for rest in itertools.permutations(remainder):
    m=(*perm,*external,*rest)
    if all(A[i][j]==target[m[i]][m[j]] for i in range(10) for j in range(i+1,10)):isomorphic=True;break
   if isomorphic:break
  assert isomorphic
  valid+=1;key=str(sorted(map(sum,Y)));hist[key]=hist.get(key,0)+1
assert valid==16
(p/'results.json').write_text(json.dumps({'status':'PASS','representatives':3,'triangle_counts':[0,2,3],'all_labelled_Y_graphs':20,'all_pair_selections_per_Y':20,'rooted_valid':valid,'Y_degree_histogram':hist},indent=2)+'\n')
(p/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print('PASS:3 representatives, all20x20 local completions,16 rooted completions all explicitly isomorphic')
