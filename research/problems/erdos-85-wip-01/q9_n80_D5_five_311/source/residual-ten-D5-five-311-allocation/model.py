from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;start=time.monotonic();base=p.parent
pack=json.loads((base/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];data=json.loads((base/'residual-ten-D5-supports/results.json').read_text())['records'];roots=[];classes=[{'representative_edges':c['edges']} for c in data];results=[]
for group in pack:
 assert group['status']=='COMPLETE'
 ci=group['class'];c=data[ci]
 for ri,original in enumerate(group['survivors']):
  ss=[c['high3'][j] for j in original['high3']]
  roots.append({'class':ci,'source_root':ri,'n311':5,'q':original['q'],'high_supports':[t for s in ss for t in (s,[v^1 for v in s])]})
def guard():
 if time.monotonic()-start>30:raise TimeoutError
for ri,root in enumerate(roots):
 guard();S=list(map(set,root['high_supports']));R=[set() for _ in range(10)]
 for a,b in classes[root['class']]['representative_edges']:R[a].add(b);R[b].add(a)
 q=root['q'];low=[9-len(R[r])-sum(r in s for s in S) for r in range(10)];assert min(low)>=0
 Z=[[int(i!=j and not(R[i]&R[j]) and not any(i in s and j in s for s in S)) for j in range(10)] for i in range(10)]
 D=[[sum(Z[k][j] for k in R[i])-sum(Z[i][k] for k in R[j]) for j in range(10)] for i in range(10)]
 variables=[];lb=[];ub=[];occ=[];seen=set()
 for v,s in enumerate(S):
  middle=set().union(*(R[r] for r in s));B=len(s)+2-sum(len(R[r]) for r in s)
  for e in range(10):
   orbit=tuple(sorted(((v,e),(v^1,e^1))))
   if orbit in seen:continue
   seen.add(orbit)
   forced=False
   upper=int(e not in middle and B>0)
   variables.append({'type':'high','orbit':orbit});lb.append(int(forced));ub.append(upper);occ.append([(set(S[w]),t,'high',w) for w,t in orbit])
 seen=set()
 for r in range(10):
  for e in range(10):
   orbit=tuple(sorted(((r,e),(r^1,e^1))))
   if orbit in seen:continue
   seen.add(orbit);upper=0 if e in R[r] else low[r]
   variables.append({'type':'low_aggregate','orbit':orbit});lb.append(0);ub.append(upper);occ.append([({a},t,'low',a) for a,t in orbit])
 constraints=[]
 def add(label,coeff,lo,hi):constraints.append({'label':label,'coefficients':[(i,a) for i,a in enumerate(coeff) if a],'lower':lo,'upper':hi})
 for e in range(10):add('column '+str(e),[sum(t==e for a,t,k,v in os) for os in occ],q[e],q[e])
 for v,s in enumerate(S):
  budget=len(s)+2-sum(len(R[r]) for r in s)
  add('high budget '+str(v),[sum(k=='high' and w==v for a,t,k,w in os) for os in occ],budget%2,budget)
 for r in range(10):add('low budget '+str(r),[sum(k=='low' and w==r for a,t,k,w in os) for os in occ],((3-len(R[r]))%2)*low[r],(3-len(R[r]))*low[r])
 for i,j in it.combinations(range(10),2):add('comm '+str((i,j)),[sum((t==i)*(j in a)-(i in a)*(t==j) for a,t,k,v in os) for os in occ],D[i][j],D[i][j])
 results.append({'root':ri,'source_root':root['source_root'],'class':root['class'],'variables':variables,'bounds':list(zip(lb,ub)),'constraints':constraints})
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':results};(p/'models.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'models':len(results)}))
