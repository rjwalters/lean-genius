from pathlib import Path
import itertools,json,time,hashlib
p=Path(__file__).parent;src=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json');states=json.loads(src.read_text());start=time.monotonic();graphs=[]
for si,r in enumerate(states):
 P=r['mapping'];es=[(1,2),(4,5)]+[(i,3+j) for i,j in enumerate(P) if j>=0]
 parent=list(range(6))
 def find(i):
  while parent[i]!=i:i=parent[i]
  return i
 shifts=[]
 for i,j in es:
  x,y=find(i),find(j);shifts.append(int(x==y));parent[x]=y
 for ti,T in enumerate(r['tables']):
  assert time.monotonic()-start<60
  adj=[0]*80
  def edge(i,j):adj[i]|=1<<j;adj[j]|=1<<i
  for a in range(6):
   for g in range(3):edge(0 if a<3 else 1,2+3*a+g)
  for (a,b),s in zip(es,shifts):
   for g in range(3):edge(2+3*a+g,2+3*b+(g+s)%3)
  available={(a,b):[g for g in range(3) if not(adj[2+3*a]&adj[11+3*b+g])] for a in range(3) for b in range(3)}
  words=[];voltages=[]
  for a in range(3):
   for b in range(3):
    assert len(available[a,b])==r['capacities'][a][b]
    for s in available[a,b][:T[a][b]]:words.append((a,b));voltages.append(s)
  if r['cross_orbits']==3:
   if r['missing_labels'] is None:words.append((3,3));voltages.append(0)
   else:a,b=r['missing_labels'];words.extend([(a,3),(3,b)]);voltages.extend([0,0])
  assert len(words)==20
  for j,((a,b),s) in enumerate(zip(words,voltages)):
   for g in range(3):
    x=20+3*j+g
    if a<3:edge(x,2+3*a+g)
    if b<3:edge(x,11+3*b+(g+s)%3)
  assert all((adj[i]&adj[j]).bit_count()<=1 for i,j in itertools.combinations(range(80),2))
  assert all(adj[i].bit_count()==9 for i in range(20))
  assert all(adj[i].bit_count()<=2 for i in range(20,80))
  tau=[0,1]+[2+3*a+(g+1)%3 for a in range(6) for g in range(3)]+[20+3*a+(g+1)%3 for a in range(20) for g in range(3)]
  assert all(bool(adj[i]>>j&1)==bool(adj[tau[i]]>>tau[j]&1) for i in range(80) for j in range(i+1,80))
  graphs.append({'state':si,'table':ti,'attached_shifts':shifts,'words':words,'residual_B_offsets':voltages,'adjacency_hex':[hex(x) for x in adj]})
result={'status':'COMPLETE','original_wall_cap':60,'seconds':time.monotonic()-start,'partial_graphs':len(graphs),'scope':'20 fixed/attached vertices degree9;60 residual vertices degree0..2; no residual edges'}
(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');(p/'partial-graphs.json').write_text(json.dumps(graphs)+'\n');(p/'input-pin.json').write_text(json.dumps({'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},indent=2)+'\n');print(json.dumps(result))
