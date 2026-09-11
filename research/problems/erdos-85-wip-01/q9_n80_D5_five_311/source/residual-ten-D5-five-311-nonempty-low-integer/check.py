from pathlib import Path
import json,itertools as it,time,functools
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();data=json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records'];pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
def flip(m):return sum(1<<(i^1) for i in range(10) if m>>i&1)
def guard():
 if time.monotonic()-start>=30:raise TimeoutError
for source in data:
 ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];R=[set() for _ in range(10)]
 for v,w in c['edges']:R[v].add(w);R[w].add(v)
 ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];Z=[[int(i!=j and not R[i]&R[j] and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)];D=[[sum(Z[k][j] for k in R[i])-sum(Z[i][k] for k in R[j]) for j in range(10)] for i in range(10)];rec={'root':source['root'],'certificates':[],'survivors':[]};out.append(rec)
 for ai,a in enumerate(source['survivors']):
  guard();rows=[x for m in a['rows'] for x in (m,flip(m))];T=[[D[i][j]-sum(((m>>i)&1)*(j in s)-(i in s)*((m>>j)&1) for m,s in zip(rows,S)) for j in range(10)] for i in range(10)];P=[[max(-v,0) for v in row] for row in T];u=a['inactive'];parity=a['diagonal_parity'];degree=[a['remaining_columns'][i]-sum(P[j][i] for j in range(10)) for i in range(10)];cap=[[min(u[i]-P[i][j],u[j]-P[j][i]) if j not in R[i] else 0 for j in range(10)] for i in range(10)];assert all(cap[i][j]>=0 for i in range(10) for j in range(10));assert all(degree[i]==degree[i^1] and parity[i]==parity[i^1] and u[i]==u[i^1] for i in range(10))
  loops=[sorted({h+2*t for h in range(cap[2*i][2*i+1]+1) for t in range((u[2*i]-parity[2*i])//2+1)}) for i in range(5)];caps={(i,j):cap[2*i][2*j]+cap[2*i][2*j+1] for i,j in it.combinations(range(5),2)};target=tuple(degree[2*i]-parity[2*i] for i in range(5))
  @functools.lru_cache(None)
  def solve(i,left):
   guard()
   if i==5:return () if not any(left) else None
   for xs in it.product(*(range(min(caps[i,j],left[j])+1) for j in range(i+1,5))):
    loop=left[i]-sum(xs)
    if loop not in loops[i]:continue
    nxt=list(left);nxt[i]=0
    for j,x in zip(range(i+1,5),xs):nxt[j]-=x
    rest=solve(i+1,tuple(nxt))
    if rest is not None:return ((loop,xs),)+rest
   return None
  witness=solve(0,target)
  if witness is None:rec['certificates'].append({'assignment':ai,'kind':'bounded_symmetric_parity_infeasible','target':target,'loops':loops,'cross_capacities':[[i,j,v] for (i,j),v in caps.items()],'states':solve.cache_info().currsize});continue
  H=[[0]*10 for _ in range(10)]
  for i,(loop,xs) in enumerate(witness):
   h=next(h for h in range(cap[2*i][2*i+1]+1) if loop>=h and (loop-h)%2==0 and parity[2*i]+loop-h<=u[2*i]);H[2*i][2*i]=H[2*i+1][2*i+1]=parity[2*i]+loop-h;H[2*i][2*i+1]=H[2*i+1][2*i]=h
   for j,x in zip(range(i+1,5),xs):
    first=min(x,cap[2*i][2*j]);second=x-first
    for v,w,z in [(2*i,2*j,first),(2*i+1,2*j+1,first),(2*i,2*j+1,second),(2*i+1,2*j,second)]:H[v][w]=H[w][v]=z
  L=[[P[i][j]+H[i][j] for j in range(10)] for i in range(10)]
  assert all(sum(H[i])==degree[i] and sum(L[i])==2*u[i] and L[i][i]%2==parity[i] and sum(L[j][i] for j in range(10))==a['remaining_columns'][i] for i in range(10));assert all(0<=L[i][j]<=u[i] and L[j][i]-L[i][j]==T[i][j] and L[i][j]==L[i^1][j^1] and (j not in R[i] or L[i][j]==0) for i in range(10) for j in range(10));rec['survivors'].append({'assignment':ai,'L':L})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'negative':sum(len(r['certificates']) for r in out),'assignments':sum(len(r['survivors']) for r in out),'positive_cases':sum(bool(r['survivors']) for r in out)}))
