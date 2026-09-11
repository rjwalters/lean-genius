from pathlib import Path
import json,itertools,math,time
p=Path(__file__).parent
start=time.monotonic()
pairs=list(itertools.combinations(range(5),2))
cases=[]
for order in [16,24,48]:
 ds=[n for n in range(1,order+1) if order%n==0 and order//n<=8]
 for ns in itertools.combinations_with_replacement(ds,5):
  if sum(ns)==78:cases.append(dict(order=order,sizes=ns,status="UNVISITED",nodes=0,quotients=[]))
class Cap(Exception):pass
for rec in cases:
 if time.monotonic()-start>=30:break
 ns=rec['sizes'];Q=[[0]*5 for _ in range(5)]
 def capacity():
  for i in range(5):
   if sum(ns[j]*Q[j][i]*(Q[j][i]-1)//2 for j in range(5))>ns[i]*(ns[i]-1)//2:return False
  for i,k in pairs:
   if sum(ns[j]*Q[j][i]*Q[j][k] for j in range(5))>ns[i]*ns[k]:return False
  return True
 def dfs(pos):
  rec['nodes']+=1
  if time.monotonic()-start>=30:raise Cap()
  if pos==len(pairs):
   old=Q[4][4];Q[4][4]=9-sum(Q[4])
   if 0<=Q[4][4]<ns[4] and capacity():rec['quotients'].append([r[:] for r in Q])
   Q[4][4]=old
   return
  i,j=pairs[pos];g=math.gcd(ns[i],ns[j]);a=ns[j]//g;b=ns[i]//g
  hi=min((9-sum(Q[i]))//a,(9-sum(Q[j]))//b)
  for t in range(hi+1):
   Q[i][j]=a*t;Q[j][i]=b*t
   if j==4:Q[i][i]=9-sum(Q[i])
   if 0<=Q[i][i]<ns[i] and capacity():dfs(pos+1)
   if j==4:Q[i][i]=0
   Q[i][j]=Q[j][i]=0
 try:
  dfs(0);rec['status']='COMPLETE'
 except Cap:
  rec['status']='UNKNOWN';break
out=dict(status='COMPLETE' if all(r['status']=='COMPLETE' for r in cases) else 'INCOMPLETE',cap_seconds=30,seconds=time.monotonic()-start,cases=cases)
p.joinpath('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out|{'cases':[{k:v for k,v in r.items() if k!='quotients'}|{'survivors':len(r['quotients'])} for r in cases]}))
