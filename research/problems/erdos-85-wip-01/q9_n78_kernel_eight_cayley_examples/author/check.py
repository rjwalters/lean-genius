from pathlib import Path
import itertools,json,time
p=Path(__file__).parent;start=time.monotonic();results=[]
for name in ['dihedral_product','elementary_semidirect']:
 if name=='dihedral_product':
  G=list(itertools.product(range(4),range(2),range(3)))
  def product(x,y):return ((x[0]+(-1)**x[1]*y[0])%4,x[1]^y[1],(x[2]+y[2])%3)
 else:
  G=list(itertools.product(range(8),range(3)))
  def rot(x,n):
   for _ in range(n):x=((x<<1)&7)|(x>>2)
   return x
  def product(x,y):return (x[0]^rot(y[0],x[1]),(x[1]+y[1])%3)
 ix={g:i for i,g in enumerate(G)};mul=[[ix[product(a,b)] for b in G] for a in G];e=0
 assert all(mul[e][i]==mul[i][e]==i for i in range(24))
 assert all(mul[mul[a][b]][c]==mul[a][mul[b][c]] for a in range(24) for b in range(24) for c in range(24))
 inv=[next(j for j in range(24) if mul[i][j]==e) for i in range(24)]
 invol=[i for i,g in enumerate(G) if i!=e and mul[i][i]==e and g[-1]==0];outs=[i for i,g in enumerate(G) if g[-1]==1];survivors=[];tested=0
 for t,a in itertools.product(invol,outs):
  assert time.monotonic()-start<30,'UNKNOWNoriginal30s'
  S=sorted([t,a,inv[a]]);tested+=1
  adj=[{mul[g][s] for s in S} for g in range(24)]
  if any(len(adj[i]&adj[j])>1 for i in range(24) for j in range(i)):continue
  assert all(len(row)==3 and i not in row and all(i in adj[j] for j in row) for i,row in enumerate(adj))
  survivors.append({'S':S,'neighbors':[sorted(x) for x in adj]})
 results.append({'name':name,'group':G,'multiplication':mul,'tested':tested,'survivors':survivors})
 print(name,tested,len(survivors),flush=True)
(p/'results.json').write_text(json.dumps({'original_seconds':30,'elapsed_seconds':time.monotonic()-start,'groups':results},indent=2)+'\n')
