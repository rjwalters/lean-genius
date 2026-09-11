from pathlib import Path
import json,itertools,math,time
p=Path(__file__).parent
N=7
start=time.monotonic()
pairs=list(itertools.combinations(range(N),2))
cases=[dict(order=24,sizes=ns,status='UNVISITED',nodes=0,quotients=[]) for ns in [(3,3,12,12,12,12,24),(6,6,6,12,12,12,24),(6,12,12,12,12,12,12)]]
class Cap(Exception):pass
for rec in cases:
 if time.monotonic()-start>=30:break
 ns=rec['sizes'];Q=[[0]*N for _ in range(N)]
 def capacity():
  for i in range(N):
   if sum(ns[j]*Q[j][i]*(Q[j][i]-1)//2 for j in range(N))>ns[i]*(ns[i]-1)//2:return False
  for i,k in pairs:
   if sum(ns[j]*Q[j][i]*Q[j][k] for j in range(N))>ns[i]*ns[k]:return False
  return True
 def dfs(pos):
  rec['nodes']+=1
  if time.monotonic()-start>=30:raise Cap()
  if pos==len(pairs):
   old=Q[N-1][N-1];Q[N-1][N-1]=9-sum(Q[N-1])
   if 0<=Q[N-1][N-1]<ns[N-1] and ns[N-1]*Q[N-1][N-1]%2==0 and capacity():rec['quotients'].append([r[:] for r in Q])
   Q[N-1][N-1]=old
   return
  i,j=pairs[pos];g=math.gcd(ns[i],ns[j]);a=ns[j]//g;b=ns[i]//g
  hi=min((9-sum(Q[i]))//a,(9-sum(Q[j]))//b)
  for t in range(hi+1):
   Q[i][j]=a*t;Q[j][i]=b*t
   if j==N-1:Q[i][i]=9-sum(Q[i])
   if 0<=Q[i][i]<ns[i] and ns[i]*Q[i][i]%2==0 and capacity():dfs(pos+1)
   if j==N-1:Q[i][i]=0
   Q[i][j]=Q[j][i]=0
 try:
  dfs(0);rec['status']='COMPLETE'
 except Cap:
  rec['status']='UNKNOWN';break
out=dict(status='COMPLETE' if all(r['status']=='COMPLETE' for r in cases) else 'INCOMPLETE',cap_seconds=30,seconds=time.monotonic()-start,cases=cases)
p.joinpath('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out|{'cases':[{k:v for k,v in r.items() if k!='quotients'}|{'survivors':len(r['quotients'])} for r in cases]}))
