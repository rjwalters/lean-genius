import json,itertools
from pathlib import Path
root=Path(__file__).resolve().parent
d=json.loads((root/'results.json').read_text()); ps=list(itertools.permutations(range(3)))
E=[[0,0,0],[0,0,1],[0,1,0]]
def matrix(p): return [[int(p[i]==j) for j in range(3)] for i in range(3)]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
seen=set()
for rec in d['records']:
 key=(rec['direct'],*rec['paths']); assert key not in seen;seen.add(key)
 P=matrix(ps[key[0]]); EP=mul(E,P);PE=mul(P,E)
 U=[[3-EP[i][j]-PE[i][j]-sum(matrix(ps[z])[i][j] for z in key[1:]) for j in range(3)] for i in range(3)]
 feasible=False
 if min(map(min,U))>=0:
  C=[[0]*8 for _ in range(8)]
  for i,r in enumerate((4,3,3)):C[0][i+1]=r;C[i+4][7]=r
  for i in range(3):
   for j in range(3):C[i+1][j+4]=U[i][j]
  flow=0
  while True:
   parent={0:None};q=[0]
   for a in q:
    for b in range(8):
     if C[a][b]>0 and b not in parent:parent[b]=a;q.append(b)
   if 7 not in parent:break
   v=7; delta=100
   while parent[v] is not None: delta=min(delta,C[parent[v]][v]);v=parent[v]
   v=7
   while parent[v] is not None:
    u=parent[v];C[u][v]-=delta;C[v][u]+=delta;v=u
   flow+=delta
  feasible=flow==10
 assert feasible==(rec['allowed_tables']>0),key
assert seen==set(itertools.product(range(6),repeat=4))
print('PASS: all 1296 local feasibility results independently checked by integral maximum flow.')
