from pathlib import Path
import json,itertools as I,time,functools
p=Path(__file__).parent;b=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3');read=lambda f:json.loads(f.read_text());assert read(p/'results.json')['status']=='COMPLETE';contexts=read(p/'contexts.json');up=read(b/'residual-ten-D5-five-311-nonempty-joint/results.json')['records'];data=read(b/'residual-ten-D5-five-311-nonempty-low-integer/results.json');assert data['status']=='COMPLETE';saved={r['root']:r for r in data['records']};assert len(saved)==len(data['records'])==len(up) and set(saved)=={r['root'] for r in up}
start=time.monotonic();out=[];status='INCOMPLETE'
try:
 for source in up:
  result=saved[source['root']];answers={x['assignment']:('negative',x) for x in result['certificates']}
  for x in result['survivors']:assert x['assignment'] not in answers;answers[x['assignment']]=('positive',x)
  assert set(answers)==set(range(len(source['survivors'])))
  ctx={tuple(x['rows']):x for x in contexts[str(source['root'])]}
  for ai,a in enumerate(source['survivors']):
   if time.monotonic()-start>30:raise TimeoutError
   c=ctx[tuple(a['rows'])];T=c['T'];R=c['R'];u=a['inactive'];q=a['remaining_columns'];par=a['diagonal_parity'];P=[[max(0,-x) for x in row] for row in T];degree=[q[i]-sum(P[j][i] for j in range(10)) for i in range(10)];cap=[[0 if R[i][j] else min(u[i]-P[i][j],u[j]-P[j][i]) for j in range(10)] for i in range(10)]
   assert all(cap[i][j]>=0 and cap[i][j]==cap[j][i]==cap[i^1][j^1] for i,j in I.product(range(10),repeat=2))
   assert all(degree[i]==degree[i^1] and par[i]==par[i^1] for i in range(10))
   loops=[{d+h for d in range(par[2*i],cap[2*i][2*i]+1,2) for h in range(cap[2*i][2*i+1]+1)} for i in range(5)]
   capacities=[[cap[2*i][2*j]+cap[2*i][2*j+1] if i!=j else 0 for j in range(5)] for i in range(5)]
   @functools.lru_cache(None)
   def feasible(degrees):
    if time.monotonic()-start>30:raise TimeoutError
    n=len(degrees)
    if not n:return True
    v=n-1
    for loop in loops[v]:
     demand=degrees[v]-loop
     if demand<0:continue
     choices=[range(min(capacities[v][j],degrees[j],demand)+1) for j in range(v)]
     for es in I.product(*choices):
      if sum(es)==demand and feasible(tuple(degrees[j]-es[j] for j in range(v))):return True
    return False
   possible=feasible(tuple(degree[2*i] for i in range(5)));kind,answer=answers[ai];assert possible==(kind=='positive')
   if possible:
    L=answer['L'];assert len(L)==10 and all(len(row)==10 and all(isinstance(x,int) for x in row) for row in L)
    assert all(sum(L[i])==2*u[i] and sum(L[j][i] for j in range(10))==q[i] and L[i][i]%2==par[i] for i in range(10))
    assert all(0<=L[i][j]<=u[i] and L[j][i]-L[i][j]==T[i][j] and L[i][j]==L[i^1][j^1] and (not R[i][j] or L[i][j]==0) for i,j in I.product(range(10),repeat=2))
   else:
    assert answer['kind']=='bounded_symmetric_parity_infeasible'
    assert answer['target']==[degree[2*i]-par[2*i] for i in range(5)]
    assert answer['loops']==[sorted(x-par[2*i] for x in loops[i]) for i in range(5)]
    assert answer['cross_capacities']==[[i,j,capacities[i][j]] for i,j in I.combinations(range(5),2)]
   out.append({'root':source['root'],'assignment':ai,'status':kind,'independent_states':feasible.cache_info().currsize})
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'low-results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':status,'seconds':r['seconds'],'assignments':len(out),'negative':sum(x['status']=='negative' for x in out),'positive':sum(x['status']=='positive' for x in out),'positive_cases':len({x['root'] for x in out if x['status']=='positive'})}))
