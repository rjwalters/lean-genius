from pathlib import Path
import json,hashlib,random
from verify import counts,reverse
p=Path(__file__).parent
source=Path('/tmp/erdos85-sol1-q9-order3-f2-neighbor-matching/inputs.txt')
lines=source.read_text().splitlines();rng=random.Random(85)
checked=0
for case,index in enumerate([0,1,17,183,1024,10000,30000,56915]):
 record=list(map(int,lines[index].split()));assert record[0]==index
 D=[[0]*20 for _ in range(20)]
 for i in range(20):
  D[i][i]=rng.choice([0,6]) if case else 0
  for j in range(i):
   D[i][j]=rng.randrange(8) if case else 0;D[j][i]=reverse(D[i][j])
 # Independent ordinary graph construction from physical input coordinates.
 G=[set() for _ in range(80)]
 def edge(a,b):G[a].add(b);G[b].add(a)
 for a in range(18):
  edge(a//9,2+a)
  for b in range(18):
   if record[1+a]>>b&1:edge(2+a,2+b)
 for i in range(20):
  for g in range(3):
   v=20+3*i+g
   for side in range(2):
    x=record[19+2*i+side]
    if x>=0:
     label,phase=divmod(x,3);edge(v,2+9*side+3*label+(g+phase)%3)
   for j in range(20):
    for t in range(3):
     if D[i][j]>>t&1:edge(v,20+3*j+(g+t)%3)
 assert all(v not in G[v] for v in range(80))
 AR,RR,degrees=counts(record,D)
 for a in range(6):
  for i in range(20):
   for g in range(3):
    for t in range(3):
     assert AR[a][i][t]==len(G[2+3*a+g]&G[20+3*i+(g+t)%3]);checked+=1
 for i in range(20):
  for j in range(20):
   for g in range(3):
    for t in range(3):
     assert RR[i][j][t]==len(G[20+3*i+g]&G[20+3*j+(g+t)%3]);checked+=1
  assert all(degrees[i]==len(G[20+3*i+g]) for g in range(3))
 # Pairs not covered by these blocks retain the partial-graph bound.
 assert all(len(G[a]&G[b])<=1 for a in range(20) for b in range(a+1,20))
 assert all(len(G[a]&G[b])<=1 for a in range(2) for b in range(20,80))
(p/'results.json').write_text(json.dumps({'fixtures':8,'coefficient_comparisons':checked,'all_degree_comparisons':480,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'search_launched':False},indent=2)+'\n')
print('PASS',checked,'exact block/physical-graph comparisons; no search')
